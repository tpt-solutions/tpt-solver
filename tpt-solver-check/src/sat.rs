//! Cheap SAT answer recheck: substitute the model and verify satisfaction.
//!
//! This is the single highest-yield, lowest-cost sanity check in the suite. Most
//! "wrong SAT answer" bugs are caught here simply by plugging the engine's claimed
//! assignment back into the original CNF and confirming every clause has a true
//! literal.

extern crate alloc;
use alloc::vec::Vec;
use tpt_solver_core::ir::Lit;

/// A Boolean formula in conjunctive normal form: a list of clauses, each a list of
/// literals. An empty clause is unsatisfiable; an empty CNF is trivially satisfied.
#[derive(Clone, Debug, Default)]
pub struct Cnf {
    clauses: Vec<Vec<Lit<()>>>,
}

impl Cnf {
    /// Build a CNF from its clauses.
    #[inline]
    pub fn new(clauses: Vec<Vec<Lit<()>>>) -> Cnf {
        Cnf { clauses }
    }

    /// The number of clauses.
    #[inline]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Whether the CNF has no clauses (trivially satisfiable).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// The clauses.
    #[inline]
    pub fn clauses(&self) -> &[Vec<Lit<()>>] {
        &self.clauses
    }
}

/// A claimed satisfying assignment: the literals the engine asserts are simultaneously
/// true. Partial assignments are valid SAT witnesses (an unassigned variable need not
/// be mentioned).
#[derive(Clone, Debug, Default)]
pub struct Model {
    true_lits: Vec<Lit<()>>,
}

impl Model {
    /// Build a model from the literals claimed true.
    #[inline]
    pub fn from_lits(true_lits: Vec<Lit<()>>) -> Model {
        Model { true_lits }
    }

    /// The literals claimed true.
    #[inline]
    pub fn true_lits(&self) -> &[Lit<()>] {
        &self.true_lits
    }
}

/// Verify that `model` satisfies `cnf`.
///
/// Returns [`Outcome::Accept`] if every clause contains at least one literal made
/// true by the model, [`Outcome::Reject`] otherwise (the engine returned a model that
/// does not actually satisfy the formula). A malformed input with a literal whose
/// variable exceeds the declared range is reported as [`Outcome::Inconclusive`].
#[inline]
pub fn check_model(cnf: &Cnf, model: &Model, var_count: u32) -> crate::outcome::Outcome {
    use crate::outcome::Outcome;

    let mut assigned = Vec::with_capacity(var_count as usize);
    assigned.resize(var_count as usize, None);

    for lit in model.true_lits() {
        let v = lit.var();
        let idx = v.index();
        if v.get() > var_count {
            return Outcome::Inconclusive;
        }
        assigned[idx] = Some(lit.is_positive());
    }

    for clause in cnf.clauses() {
        if clause.is_empty() {
            // An empty clause can never be satisfied.
            return Outcome::Reject;
        }
        let mut satisfied = false;
        for lit in clause {
            let idx = lit.var().index();
            if lit.var().get() > var_count {
                return Outcome::Inconclusive;
            }
            match assigned[idx] {
                Some(true) if lit.is_positive() => {
                    satisfied = true;
                    break;
                }
                Some(false) if !lit.is_positive() => {
                    satisfied = true;
                    break;
                }
                _ => {}
            }
        }
        if !satisfied {
            return Outcome::Reject;
        }
    }

    Outcome::Accept
}

/// Build a [`VarId`] in the unbranded session for testing/kernel-internal use.
#[cfg(test)]
#[allow(clippy::unwrap_used)]
pub(crate) fn var(id: u32) -> tpt_solver_core::ir::VarId<()> {
    tpt_solver_core::ir::VarId::new(id).expect("non-zero var id")
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use tpt_solver_core::ir::Lit;

    #[test]
    fn accepts_valid_model() {
        // (x1) & (x2)
        let cnf = Cnf::new(vec![
            vec![Lit::new(var(1), true)],
            vec![Lit::new(var(2), true)],
        ]);
        let model = Model::from_lits(vec![Lit::new(var(1), true), Lit::new(var(2), true)]);
        assert!(check_model(&cnf, &model, 2).is_accept());
    }

    #[test]
    fn rejects_invalid_model() {
        // (x1) & (x2); model only sets x1.
        let cnf = Cnf::new(vec![
            vec![Lit::new(var(1), true)],
            vec![Lit::new(var(2), true)],
        ]);
        let model = Model::from_lits(vec![Lit::new(var(1), true)]);
        assert!(check_model(&cnf, &model, 2).is_reject());
    }

    #[test]
    fn rejects_contradictory_clause() {
        // (x1) & (!x1) cannot be satisfied by any single model.
        let cnf = Cnf::new(vec![
            vec![Lit::new(var(1), true)],
            vec![Lit::new(var(1), false)],
        ]);
        let model = Model::from_lits(vec![Lit::new(var(1), true)]);
        assert!(check_model(&cnf, &model, 1).is_reject());
    }
}
