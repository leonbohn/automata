use std::hash::Hash;

use automata::{
    math,
    prelude::{Show, Symbol},
};

use super::Factor;

pub trait Classifier<S> {
    fn classify(&self, factor: &Factor<S>) -> bool;
    fn access<'a, X>(&self, factor: &Factor<S>, array: &'a [X; 2]) -> &'a X {
        if self.classify(factor) {
            &array[0]
        } else {
            &array[1]
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub enum NodeId {
    Inner(usize),
    Leaf(usize),
}
pub use NodeId::*;

impl NodeId {
    pub fn index(&self) -> usize {
        match self {
            NodeId::Inner(n) => *n,
            NodeId::Leaf(n) => *n,
        }
    }
    pub fn try_inner(&self) -> Option<usize> {
        let Self::Inner(n) = self else {
            return None;
        };
        Some(*n)
    }
    pub fn try_leaf(&self) -> Option<usize> {
        let Self::Leaf(n) = self else {
            return None;
        };
        Some(*n)
    }
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (a, b) = match self {
            NodeId::Inner(n) => ("N", n),
            NodeId::Leaf(n) => ("L", n),
        };
        write!(f, "{a}({b})")
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct InnerNode<S> {
    parent: Option<NodeId>,
    discriminator: Factor<S>,
    subtree: [NodeId; 2],
}

impl<S> InnerNode<S> {
    pub fn from_parts(
        parent: Option<NodeId>,
        discriminator: Factor<S>,
        subtree: [NodeId; 2],
    ) -> Self {
        Self {
            parent,
            discriminator,
            subtree,
        }
    }
}

impl<S: Show> std::fmt::Debug for InnerNode<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "N({:?}, {:?}, {:?})",
            self.discriminator, self.subtree[0], self.subtree[1]
        )
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Leaf<X> {
    parent: Option<NodeId>,
    content: X,
}

impl<X> Leaf<X> {
    pub fn from_parts(parent: Option<NodeId>, content: X) -> Self {
        Self { parent, content }
    }
}

impl<X: Show> std::fmt::Debug for Leaf<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "L({})", self.content.show())
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct DiscriminationTree<S, X> {
    inner: Vec<InnerNode<S>>,
    leaves: Vec<Leaf<X>>,
}

impl<S, X> DiscriminationTree<S, math::Set<X>> {
    pub fn set_based(leaf_content: math::Set<X>) -> (Self, NodeId) {
        let leaf = Leaf::from_parts(None, leaf_content);
        (Self::from_parts(vec![], vec![leaf]), Leaf(0))
    }
    fn downcast(self) -> DiscriminationTree<S, X> {
        let inner = self.inner;
        let leaves = self
            .leaves
            .into_iter()
            .map(|Leaf { parent, content }| {
                assert!(content.len() == 1);
                Leaf {
                    parent,
                    content: content.into_iter().next().unwrap(),
                }
            })
            .collect();
        DiscriminationTree::from_parts(inner, leaves)
    }
}

impl<S, X> DiscriminationTree<S, X> {
    pub fn element_based(leaf_content: X) -> (Self, NodeId) {
        let leaf = Leaf::from_parts(None, leaf_content);
        (Self::from_parts(vec![], vec![leaf]), Leaf(0))
    }

    pub fn upcast(self) -> DiscriminationTree<S, math::Set<X>>
    where
        X: Hash + Eq,
    {
        let inner = self.inner;
        let leaves = self
            .leaves
            .into_iter()
            .map(|Leaf { parent, content }| Leaf {
                parent,
                content: math::Set::from_iter([content]),
            })
            .collect();
        DiscriminationTree::from_parts(inner, leaves)
    }

    pub fn sift<'a, C: Classifier<S>>(&'a self, classifier: C, node: &NodeId) -> &'a Leaf<X> {
        if let Some(leaf) = node.try_leaf() {
            assert!(leaf < self.leaves.len(), "invalid leaf index");
            return &self.leaves[leaf];
        }

        let mut current = node;
        loop {
            let o = self.unwrap_discriminator(&current);
            let current = classifier.access(o, self.unwrap_successors(current));
        }
        &self.leaves[current.index()]
    }

    pub fn lowest_common_ancestor<'a>(&'a self, a: &'a NodeId, b: &NodeId) -> &'a NodeId {
        if a == b {
            return &a;
        }
        let ancestors_a: Vec<_> = self.ancestors_vec(a);
        if ancestors_a.contains(&b) {
            return a;
        }

        let mut current = b;
        while let Some(parent) = self.try_parent(current) {
            if ancestors_a.contains(&parent) {
                return parent;
            }
            current = parent;
        }

        unreachable!("nodes must always have a common ancestor")
    }

    pub fn ancestors_vec(&self, node: &NodeId) -> Vec<&NodeId> {
        let mut ancestors = Vec::new();
        let mut current = node;
        while let Some(parent) = self.try_parent(current) {
            ancestors.push(parent);
            current = parent;
        }
        ancestors
    }

    pub fn try_parent(&self, node: &NodeId) -> Option<&NodeId> {
        match node {
            NodeId::Inner(n) => {
                assert!(*n < self.inner.len(), "invalid inner node index");
                self.inner[*n].parent.as_ref()
            }
            NodeId::Leaf(n) => {
                assert!(*n < self.leaves.len(), "invalid leaf index");
                self.leaves[*n].parent.as_ref()
            }
        }
    }

    pub fn unwrap_successors(&self, node: &NodeId) -> &[NodeId; 2] {
        self.try_successors(node).unwrap()
    }

    pub fn try_successors(&self, node: &NodeId) -> Option<&[NodeId; 2]> {
        let inner = node.try_inner()?;
        assert!(inner < self.inner.len(), "invalid inner node index");
        Some(&self.inner[inner].subtree)
    }

    pub fn try_successors_mut(&mut self, node: &NodeId) -> Option<&mut [NodeId; 2]> {
        let inner = node.try_inner()?;
        assert!(inner < self.inner.len(), "invalid inner node index");
        Some(&mut self.inner[inner].subtree)
    }

    pub fn unwrap_discriminator(&self, node: &NodeId) -> &Factor<S> {
        self.try_discriminator(node).unwrap()
    }

    pub fn try_discriminator(&self, node: &NodeId) -> Option<&Factor<S>> {
        let inner = node.try_inner()?;
        assert!(inner < self.inner.len(), "invalid inner node index");
        Some(&self.inner[inner].discriminator)
    }

    pub fn try_discriminator_mut(&mut self, node: &NodeId) -> Option<&mut Factor<S>> {
        let inner = node.try_inner()?;
        assert!(inner < self.inner.len(), "invalid inner node index");
        Some(&mut self.inner[inner].discriminator)
    }

    pub fn try_leaf(&self, leaf: &NodeId) -> Option<&X> {
        let leaf = leaf.try_leaf()?;
        assert!(leaf < self.leaves.len(), "invalid leaf index");
        Some(&self.leaves[leaf].content)
    }
    pub fn unwrap_leaf(&self, leaf: &NodeId) -> &X {
        self.try_leaf(leaf).unwrap()
    }

    pub fn try_leaf_mut(&mut self, leaf: &NodeId) -> Option<&mut X> {
        let leaf = leaf.try_leaf()?;
        assert!(leaf < self.leaves.len(), "invalid leaf index");
        Some(&mut self.leaves[leaf].content)
    }

    pub fn from_parts(inner: Vec<InnerNode<S>>, leaves: Vec<Leaf<X>>) -> Self {
        Self { inner, leaves }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_tree() -> DiscriminationTree<char, usize> {
        DiscriminationTree::from_parts(vec![], vec![])
    }

    #[test]
    fn discrimination_tree_lowest_common_ancestor() {}
}
