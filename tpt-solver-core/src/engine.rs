//! The solving engine's public surface and its typestate lifecycle.
//!
//! ## Two distinct outcomes
//!
//! * [`SolveResult`] is what the **engine** produces: it claims `Sat`, `Unsat`, or
//!   `Unknown` (fuel exhausted / could not decide). This is untrusted.
//! * The **checker** ([`tpt-solver-check`](https://crates.io/crates/tpt-solver-check))
//!   then validates the claim into one of three outcomes `Accept` / `Reject` /
//!   `Inconclusive`. That verdict is what callers may trust.
//!
//! ## Typestate
//!
//! The solver moves through distinct, checked states. A `Solver<Solving>` can only
//! produce a [`SolveResult`]; once it has, it transitions to `Solver<Model>` (for a
//! `Sat` answer, carrying the model) or `Solver<Proof>` (for an `Unsat` answer,
//! carrying the certificate). Operations invalid in the current state are absent
//! from the type, so misuse is a compile error.

use crate::fuel::Fuel;
use crate::ir::{ClauseId, Lit, VarId};

/// The engine's claim about a problem. Untrusted until rechecked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveResult {
    /// The engine found a satisfying assignment.
    Sat,
    /// The engine found the problem unsatisfiable (and, when wired up, a proof).
    Unsat,
    /// The engine could not decide within its resource budget (`Unknown` is the
    /// honest last resort — never a panic).
    Unknown,
}

/// Typestate marker: the solver is still searching.
#[derive(Debug)]
pub struct Solving;

/// Typestate marker: the solver has produced a satisfying model.
#[derive(Debug)]
pub struct Model;

/// Typestate marker: the solver has produced an unsatisfiability certificate.
#[derive(Debug)]
pub struct Proof;

/// A minimal, typestated solver skeleton.
///
/// This is the foundation scaffold: it owns the ID tables and fuel, and demonstrates
/// the lifecycle type-states. The actual CDCL/DPLL(T) search lands in Phase 2.
#[derive(Debug)]
pub struct Solver<State> {
    state: core::marker::PhantomData<State>,
    var_count: u32,
    clause_count: u32,
    fuel: Fuel,
}

impl Solver<Solving> {
    /// Begin a new solving session with `var_count` variables and an initial fuel
    /// budget.
    #[inline]
    pub fn new(var_count: u32, fuel: Fuel) -> Solver<Solving> {
        Solver {
            state: PhantomData,
            var_count,
            clause_count: 0,
            fuel,
        }
    }

    /// Number of variables declared so far.
    #[inline]
    pub fn var_count(&self) -> u32 {
        self.var_count
    }

    /// Allocate a fresh variable, returning its [`VarId`].
    ///
    /// Panics are forbidden by the crate's lint gate; running out of the `u32` index
    /// space is a programming error surfaced as `None` rather than a panic.
    #[inline]
    pub fn new_var<S>(&mut self) -> Option<VarId<S>> {
        let next = self.var_count.checked_add(1)?;
        self.var_count = next;
        VarId::new(next)
    }

    /// Record that a clause was added, returning its [`ClauseId`].
    #[inline]
    pub fn new_clause<S>(&mut self) -> Option<ClauseId<S>> {
        let next = self.clause_count.checked_add(1)?;
        self.clause_count = next;
        ClauseId::new(next)
    }

    /// Remaining fuel.
    #[inline]
    pub fn fuel(&self) -> Fuel {
        self.fuel
    }

    // The decision/search routine is intentionally not implemented here: it is the
    // Phase 2 CDCL engine. For now the skeleton only establishes identity, typing,
    // and lifecycle.
}

/// A satisfying assignment is a sequence of literals forced true by the model.
#[derive(Clone, Debug, Default)]
pub struct Assignment {
    lits: alloc::vec::Vec<Lit<()>>,
}

impl Assignment {
    /// Build an assignment from a list of literals (the literals forced true).
    #[inline]
    pub fn from_lits(lits: alloc::vec::Vec<Lit<()>>) -> Assignment {
        Assignment { lits }
    }

    /// The literals that are true in this model.
    #[inline]
    pub fn lits(&self) -> &[Lit<()>] {
        &self.lits
    }
}

use core::marker::PhantomData;

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn skeleton_lifecycle_typing() {
        let mut s = Solver::new(0, Fuel::new(100));
        let v = s.new_var::<()>().expect("room for one var");
        let c = s.new_clause::<()>().expect("room for one clause");
        assert_eq!(v.get(), 1);
        assert_eq!(c.get(), 1);
        assert_eq!(s.fuel().remaining(), 100);
    }
}
