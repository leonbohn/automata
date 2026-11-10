use crate::{
    Color,
    alphabet::{
        CharAlphabet, Expression, Matcher, PropAlphabet, PropExpression, PropSymbol, RawSymbolRepr,
    },
    representation::{FromTransitions, Parts},
    ts::{StateIndex, States},
};
use std::collections::BTreeSet;

/// The atoms (minterms) of a set of propositional expressions: the coarsest partition of the
/// symbol space such that every one of the expressions is a union of parts. Two symbols in the
/// same atom cannot be told apart by any of the expressions.
///
/// Algorithms that only look at edge labels can run over the (usually few) atoms instead of the
/// exponentially many symbols or over expressions: [`Self::split_edges`] relabels a system to the
/// indexed alphabet [`Self::alphabet`] with one letter per atom, where intersecting labels is an
/// equality test and the storages [`DenseTs`](crate::ts::DenseTs) and
/// [`CsrTs`](crate::ts::CsrTs) apply. Words over the atom alphabet are translated back with
/// [`Self::symbol`] (and forth with [`Self::letter_of`]).
///
/// The letter of atom `i` is `'a'` advanced by `i` code points, like in
/// [`CharAlphabet::of_size`].
///
/// # Example
/// ```
/// use automata::alphabet::{Atoms, PropAlphabet, PropExpression};
///
/// let labels = [PropExpression::<u32>::new(2, "0"), PropExpression::new(2, "1")];
/// let atoms = Atoms::new(2, labels.iter().cloned());
/// // the symbols 00, 01, 10 and 11 fall into the atoms !0&!1, !0&1, 0&!1 and 0&1
/// assert_eq!(atoms.len(), 4);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atoms<R: RawSymbolRepr = u32> {
    num_aps: u8,
    atoms: Vec<PropExpression<R>>,
}

impl<R: RawSymbolRepr> Atoms<R> {
    /// Computes the atoms of the given labels over `num_aps` atomic propositions by partition
    /// refinement: starting from the single atom `true`, every label splits each atom it cuts into
    /// two. Unsatisfiable atoms are dropped, so the atoms are nonempty and pairwise disjoint and
    /// cover all symbols. Their order is deterministic.
    pub fn new(num_aps: u8, labels: impl IntoIterator<Item = PropExpression<R>>) -> Self {
        // the Bdd handle is only interior-mutable for its manager, Ord/Eq are structural
        #[allow(clippy::mutable_key_type)]
        let labels: BTreeSet<_> = labels.into_iter().collect();
        let mut atoms = vec![PropExpression::universal(num_aps)];
        for label in labels {
            let negated = !label.clone();
            let mut refined = Vec::with_capacity(atoms.len() + 1);
            for atom in atoms {
                match (atom.intersection(&label), atom.intersection(&negated)) {
                    (Some(inside), Some(outside)) => {
                        refined.push(inside);
                        refined.push(outside);
                    }
                    _ => refined.push(atom),
                }
            }
            atoms = refined;
        }
        Self { num_aps, atoms }
    }

    /// Computes the atoms of all edge labels of the given systems, which must share the alphabet.
    pub fn of<'a, T>(alphabet: &PropAlphabet<R>, systems: impl IntoIterator<Item = &'a T>) -> Self
    where
        T: States<Alphabet = PropAlphabet<R>> + 'a,
    {
        Self::new(
            alphabet.aps(),
            systems.into_iter().flat_map(|ts| Self::labels(ts)),
        )
    }

    /// The labels of all edges of `ts`.
    pub(crate) fn labels<T>(ts: &T) -> impl Iterator<Item = PropExpression<R>> + '_
    where
        T: States<Alphabet = PropAlphabet<R>>,
    {
        ts.states().flat_map(move |q| {
            ts.edges_from(q)
                .into_iter()
                .flatten()
                .map(|e| e.expression().clone())
        })
    }

    /// The number of atoms.
    pub fn len(&self) -> usize {
        self.atoms.len()
    }

    /// Always false, there is at least one atom.
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    /// The expression that is satisfied by exactly the symbols of atom `index`.
    pub fn atom(&self, index: usize) -> Option<&PropExpression<R>> {
        self.atoms.get(index)
    }

    /// The index of the atom containing `symbol`, found by a scan over the atoms.
    pub fn index_of(&self, symbol: PropSymbol<R>) -> Option<usize> {
        self.atoms.iter().position(|a| symbol.matches(a))
    }

    /// The letter of the atom that contains `symbol`, see [`Self::alphabet`].
    pub fn letter_of(&self, symbol: PropSymbol<R>) -> Option<char> {
        self.index_of(symbol).map(Self::letter)
    }

    /// A symbol of the atom with the given index, the same one on every call. Together with
    /// [`Self::letter_of`] this translates words over the atoms back to symbols.
    pub fn symbol(&self, index: usize) -> Option<PropSymbol<R>> {
        self.atoms.get(index)?.symbols().next()
    }

    /// The symbol that represents the atom of `letter`, see [`Self::symbol`].
    pub fn symbol_of(&self, letter: char) -> Option<PropSymbol<R>> {
        self.symbol((letter as usize).checked_sub('a' as usize)?)
    }

    /// The indexed alphabet with one letter per atom.
    pub fn alphabet(&self) -> CharAlphabet {
        CharAlphabet::of_size(self.len())
    }

    fn letter(index: usize) -> char {
        char::from_u32('a' as u32 + index as u32).expect("too many atoms")
    }

    /// Spot's `split_edges`: relabels `ts` to the atom alphabet, replacing every edge by one edge
    /// per atom it covers. `ts` must only have labels that were passed when computing the atoms
    /// (then each label is a union of atoms), otherwise atoms that merely overlap a label are
    /// included. The result is in any [`FromTransitions`] target without initial state (use
    /// [`TransitionSystem::with_initial`] afterwards); states keep their order.
    pub fn split_edges<T, U>(&self, ts: &T) -> U
    where
        T: States<Alphabet = PropAlphabet<R>>,
        U: FromTransitions<
                StateIndex<T>,
                (),
                Alphabet = CharAlphabet,
                StateColor = T::StateColor,
                EdgeColor = T::EdgeColor,
            >,
        T::EdgeColor: Color,
    {
        let states = ts
            .states()
            .map(|q| (q, ts.state_color(q).expect("state exists").into_owned()));
        let edges = ts.states().flat_map(move |q| {
            ts.edges_from(q).into_iter().flatten().flat_map(move |e| {
                let color = e.color().clone();
                let target = e.target();
                self.atoms
                    .iter()
                    .enumerate()
                    .filter_map(|(i, a)| {
                        if a.overlaps(e.expression()) {
                            Some(i)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
                    .map(move |i| (q, Self::letter(i), color.clone(), target))
            })
        });
        U::from_transitions(Parts {
            alphabet: self.alphabet(),
            states,
            edges,
            initial: (),
        })
    }

    /// The number of atomic propositions.
    pub fn aps(&self) -> u8 {
        self.num_aps
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        DTS, Void,
        ts::{Deterministic, ForAlphabet, Sproutable, States},
    };

    type E = PropExpression<u32>;

    #[test]
    fn atoms_partition_the_symbols() {
        let atoms = Atoms::new(2, [E::new(2, "0"), E::new(2, "0 & 1"), E::new(2, "t")]);
        assert_eq!(atoms.len(), 3);
        for raw in 0..4 {
            let sym = PropSymbol::<u32>::from_char((b'a' + raw) as char, 2);
            let hits = (0..atoms.len())
                .filter(|&i| sym.matches(atoms.atom(i).unwrap()))
                .count();
            assert_eq!(hits, 1);
            let l = atoms.letter_of(sym).unwrap();
            let back = atoms.symbol_of(l).unwrap();
            assert_eq!(atoms.index_of(back), atoms.index_of(sym));
        }
    }

    #[test]
    fn split_edges_gives_deterministic_complete_atom_system() {
        let alphabet = PropAlphabet::<u32>::from_apnames(["p", "q"]);
        let mut ts = DTS::<PropAlphabet, Void, bool>::for_alphabet(alphabet.clone());
        let q0 = ts.add_state(Void);
        let q1 = ts.add_state(Void);
        ts.add_edge((q0, E::new(2, "0"), true, q1));
        ts.add_edge((q0, E::new(2, "!0"), false, q0));
        ts.add_edge((q1, E::new(2, "t"), false, q1));
        let atoms = Atoms::of(&alphabet, [&ts]);
        assert_eq!(atoms.len(), 2);
        let split: DTS<CharAlphabet, Void, bool> = atoms.split_edges(&ts);
        assert_eq!(split.state_count(), 2);
        let sym = |s: &str| {
            atoms
                .letter_of(PropSymbol::<u32>::from_char(s.chars().next().unwrap(), 2))
                .unwrap()
        };
        assert_eq!(split.edge(q0, sym("d")).map(|e| e.target()), Some(q1));
        assert_eq!(split.edge(q0, sym("a")).map(|e| e.target()), Some(q0));
    }
}
