//! What a failing test prints: the assertion message followed by the operations that led to it in
//! terms of the states and edges they touched, the resulting model, and a replayable list.

use std::{
    any::Any,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
};

use super::*;

impl Op {
    /// The operation as Rust code, so that a failing sequence can be pasted into a test.
    fn rust(&self) -> String {
        match self {
            Op::AddState(c) => format!("Op::AddState({c})"),
            Op::AddEdge {
                source,
                symbol,
                color,
                target,
            } => format!(
                "Op::AddEdge {{ source: {source}, symbol: {symbol}, color: {color}, target: {target} }}"
            ),
            Op::RemoveEdge(e) => format!("Op::RemoveEdge({e})"),
            Op::RemoveState(q) => format!("Op::RemoveState({q})"),
            Op::SetStateColor(q, c) => format!("Op::SetStateColor({q}, {c})"),
            Op::SetEdgeColor(e, c) => format!("Op::SetEdgeColor({e}, {c})"),
            Op::RemoveEdgesTo(q) => format!("Op::RemoveEdgesTo({q})"),
            Op::RemoveEdgesFrom(q) => format!("Op::RemoveEdgesFrom({q})"),
            Op::RemoveEdgesBetween(p, q) => format!("Op::RemoveEdgesBetween({p}, {q})"),
            Op::TrimFrom(q) => format!("Op::TrimFrom({q})"),
            Op::Compact => "Op::Compact".to_string(),
        }
    }
}

impl std::fmt::Debug for Op {
    /// One line per operation, also when pretty printed as part of a list.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.rust())
    }
}

fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else {
        "panicked with a payload that is not a string".to_string()
    }
}

impl<Ts> Harness<Ts>
where
    Ts: Sproutable<Alphabet = CharAlphabet, StateColor = u8, EdgeColor = u8>
        + Shrinkable
        + PredecessorIterable
        + States,
{
    /// The operation with every selector replaced by the position of what it selected among the
    /// live states or edges (one past the last for things that do not exist). It does the same
    /// as `op` when applied now, but is easier to read and replay.
    fn normalize(&self, op: &Op) -> Op {
        let live_states = self.model.states();
        let live_edges: Vec<_> = self.model.edges().iter().map(|e| e.0).collect();
        let state = |sel: usize, allow_missing: bool| {
            self.pick_state(sel, allow_missing).map_or(sel, |q| {
                live_states
                    .iter()
                    .position(|&p| p == q)
                    .unwrap_or(live_states.len())
            })
        };
        let edge = |sel: usize| {
            let id = self.pick_edge(sel);
            live_edges
                .iter()
                .position(|&e| e == id)
                .unwrap_or(live_edges.len())
        };
        match *op {
            Op::AddState(c) => Op::AddState(c),
            Op::AddEdge {
                source,
                symbol,
                color,
                target,
            } => Op::AddEdge {
                source: state(source, false),
                symbol: symbol % ALPHABET_SIZE,
                color,
                target: state(target, false),
            },
            Op::RemoveEdge(e) => Op::RemoveEdge(edge(e)),
            Op::RemoveState(q) => Op::RemoveState(state(q, true)),
            Op::SetStateColor(q, c) => Op::SetStateColor(state(q, true), c),
            Op::SetEdgeColor(e, c) => Op::SetEdgeColor(edge(e), c),
            Op::RemoveEdgesTo(q) => Op::RemoveEdgesTo(state(q, true)),
            Op::RemoveEdgesFrom(q) => Op::RemoveEdgesFrom(state(q, true)),
            Op::RemoveEdgesBetween(p, q) => Op::RemoveEdgesBetween(state(p, true), state(q, true)),
            Op::TrimFrom(q) => Op::TrimFrom(state(q, false)),
            Op::Compact => Op::Compact,
        }
    }

    /// Describes `op` in terms of the states and edges it refers to right now.
    pub(super) fn describe(&self, op: &Op) -> String {
        let state = |sel: usize, allow_missing: bool| match self.pick_state(sel, allow_missing) {
            Some(q) if self.model.contains_state(q) => format!("q{q}"),
            Some(q) => format!("q{q} (does not exist)"),
            None => "no state".to_string(),
        };
        let edge = |sel: usize| {
            let id = self.pick_edge(sel);
            if self.model.edges().iter().any(|e| e.0 == id) {
                format!("e{id}")
            } else {
                format!("e{id} (does not exist)")
            }
        };
        match *op {
            Op::AddState(color) => {
                format!("q{} = add_state(color {color})", self.created_states)
            }
            Op::AddEdge {
                source,
                symbol,
                color,
                target,
            } => format!(
                "e{} = add_edge({} -{}/{color}-> {})",
                self.model.next_edge_id,
                state(source, false),
                symbol_char(symbol),
                state(target, false)
            ),
            Op::RemoveEdge(sel) => format!("remove_edge({})", edge(sel)),
            Op::RemoveState(sel) => format!("remove_state({})", state(sel, true)),
            Op::SetStateColor(sel, color) => {
                format!("set color of {} to {color}", state(sel, true))
            }
            Op::SetEdgeColor(sel, color) => format!("set color of {} to {color}", edge(sel)),
            Op::RemoveEdgesTo(sel) => format!("remove_edges_to({})", state(sel, true)),
            Op::RemoveEdgesFrom(sel) => format!("remove_edges_from({})", state(sel, true)),
            Op::RemoveEdgesBetween(source, target) => format!(
                "remove_edges_between({}, {})",
                state(source, true),
                state(target, true)
            ),
            Op::TrimFrom(sel) => format!("trim_from({})", state(sel, false)),
            Op::Compact => "compact (the storage renumbers its ids)".to_string(),
        }
    }

    /// Applies `op` to the storage and the model, checks that the results agree and then compares
    /// the full state of both. A failure reports the operations applied so far.
    pub fn step(&mut self, op: &Op) {
        let description = self.describe(op);
        self.trace.push(description);
        self.applied.push(self.normalize(op));
        let result = catch_unwind(AssertUnwindSafe(|| self.apply(op)));
        if let Err(payload) = result {
            self.fail(payload, true);
        }
    }

    /// Runs `check` and, if it panics, extends the message with the operations that led to the
    /// state that was checked.
    pub(super) fn reported<R>(&self, check: impl FnOnce() -> R) -> R {
        match catch_unwind(AssertUnwindSafe(check)) {
            Ok(r) => r,
            Err(payload) => self.fail(payload, false),
        }
    }

    fn fail(&self, payload: Box<dyn Any + Send>, in_last_operation: bool) -> ! {
        let message = panic_message(&*payload);
        let mut report = format!("{message}\n\n");
        report += &format!("after {} operation(s):\n", self.trace.len());
        for (i, line) in self.trace.iter().enumerate() {
            let marker = if in_last_operation && i + 1 == self.trace.len() {
                "   <-- failed here"
            } else {
                ""
            };
            report += &format!("  {:>3}. {line}{marker}\n", i + 1);
        }
        report += "\nthe model is\n";
        report += &self.model.describe();
        report += "\nreplay with\n  [";
        report += &self
            .applied
            .iter()
            .map(Op::rust)
            .collect::<Vec<_>>()
            .join(", ");
        report += "]\n";
        resume_unwind(Box::new(report))
    }
}
