//! The BDD backend of [`super::PropExpression`] for more than six atomic propositions. This is the
//! only file that knows about oxidd, none of its types appear in a public signature.
//!
//! All expressions live in one global manager with a variable for every possible atomic
//! proposition (variable `i` is proposition `i`), so expressions that were built independently can
//! be combined, and equality and hashing are O(1) (BDDs are canonical).
//!
//! Node ids depend on the history of the manager, which is shared by all threads. Nothing that is
//! observable may depend on them: [`Bdd::cubes`] therefore follows the structure of the BDD.

use std::sync::LazyLock;

use oxidd::{
    HasLevel, Manager as _, ManagerRef as _, Node,
    bcdd::{BCDDFunction, BCDDManagerRef, new_manager},
    util::AllocResult,
    {BooleanFunction as _, Function as _},
};

/// The number of variables, the number of bits of the largest `RawSymbolRepr`.
const VARS: u32 = 128;
/// The number of inner nodes the manager can hold. The slots are not touched until used, so this
/// costs virtual memory only. Garbage collection is automatic.
const NODES: usize = 1 << 24;
/// The capacity of the apply cache.
const CACHE: usize = 1 << 20;

struct Manager {
    /// Keeps the manager alive.
    _manager: BCDDManagerRef,
    top: BCDDFunction,
    bottom: BCDDFunction,
    vars: Vec<BCDDFunction>,
}

static MANAGER: LazyLock<Manager> = LazyLock::new(|| {
    let manager = new_manager(NODES, CACHE, 1);
    let (top, bottom, vars) = manager.with_manager_exclusive(|m| {
        m.add_vars(VARS);
        let vars = (0..VARS)
            .map(|i| BCDDFunction::var(m, i).expect(OOM))
            .collect();
        (BCDDFunction::t(m), BCDDFunction::f(m), vars)
    });
    Manager {
        _manager: manager,
        top,
        bottom,
        vars,
    }
});

const OOM: &str = "the BDD manager ran out of nodes";

/// A boolean function over the atomic propositions `0..128`.
///
/// # Panics
///
/// The operations panic if the manager runs out of nodes, like a failed allocation.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct Bdd(BCDDFunction);

impl std::fmt::Debug for Bdd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.cubes()).finish()
    }
}

/// A set of valuations given by some propositions that are fixed (`care`, `value`); the others
/// are free. Bit `i` belongs to the atomic proposition `i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Cube {
    pub(super) care: u128,
    pub(super) value: u128,
}

impl Bdd {
    pub(super) fn top() -> Self {
        Self(MANAGER.top.clone())
    }

    pub(super) fn bottom() -> Self {
        Self(MANAGER.bottom.clone())
    }

    /// The proposition with the given index.
    pub(super) fn var(ap: u8) -> Self {
        Self(MANAGER.vars[ap as usize].clone())
    }

    pub(super) fn and(&self, other: &Self) -> Self {
        Self(ok(self.0.and(&other.0)))
    }

    pub(super) fn or(&self, other: &Self) -> Self {
        Self(ok(self.0.or(&other.0)))
    }

    pub(super) fn not(&self) -> Self {
        Self(ok(self.0.not()))
    }

    pub(super) fn is_false(&self) -> bool {
        self.0 == MANAGER.bottom
    }

    /// Evaluates the function under the valuation that makes proposition `i < num_aps` true iff
    /// `symbol(i)`.
    pub(super) fn eval(&self, num_aps: u8, symbol: impl Fn(u8) -> bool) -> bool {
        self.0.eval((0..num_aps).map(|i| (i as u32, symbol(i))))
    }

    /// The paths to `true` as cubes. They are disjoint, and come from the low branch to the high
    /// branch in variable order, independently of the node ids.
    pub(super) fn cubes(&self) -> impl Iterator<Item = Cube> {
        let mut stack = vec![(self.0.clone(), Cube { care: 0, value: 0 })];
        std::iter::from_fn(move || {
            while let Some((f, cube)) = stack.pop() {
                let Some(ap) = variable(&f) else {
                    if f == MANAGER.top {
                        return Some(cube);
                    }
                    continue;
                };
                let (high, low) = f.cofactors().expect("inner nodes have cofactors");
                let care = cube.care | 1 << ap;
                stack.push((
                    high,
                    Cube {
                        care,
                        value: cube.value | 1 << ap,
                    },
                ));
                stack.push((
                    low,
                    Cube {
                        care,
                        value: cube.value,
                    },
                ));
            }
            None
        })
    }
}

fn ok(result: AllocResult<BCDDFunction>) -> BCDDFunction {
    result.expect(OOM)
}

/// The variable a function branches on, `None` for the constants. Variables are never reordered,
/// so the level of a node is its variable.
fn variable(f: &BCDDFunction) -> Option<u32> {
    f.with_manager_shared(|manager, edge| match manager.get_node(edge) {
        Node::Inner(node) => Some(node.level()),
        Node::Terminal(_) => None,
    })
}
