//! UNSAT certificate checking: RUP/LRAT.
//!
//! A SAT-propositional UNSAT claim is backed by a certificate: a sequence of derived
//! clauses, each of which must be redundant (RUP — *reverse unit propagation*) or
//! asymmetric-tautology (RAT) with respect to the clauses derived before it. If the
//! final derived clause is the empty clause, the original CNF is unsatisfiable.
//!
//! The full, hint-validated LRAT format (validating RAT hints, deletion records, and
//! the precise order) is the Phase 2 deliverable. What is implemented here from day
//! one is the sound core: a correct unit-propagation RUP checker. A clause `C` is RUP
//! derivable iff assuming the negations of all literals of `C` makes the existing
//! clause set yield a conflict by unit propagation. This alone is sufficient to prove
//! UNSAT for purely-RUP proofs and is independently trustworthy.

extern crate alloc;
use crate::outcome::Outcome;
use alloc::vec::Vec;
use tpt_solver_core::ir::Lit;
/// A single derived clause in a proof, with its (optional) LRAT hint clause ids.
///
/// The hint is *not* required for the RUP soundness check (we recompute via unit
/// propagation), but it is retained so the Phase 2 hint-validated checker can use it.
#[derive(Clone, Debug)]
pub struct LratStep {
    /// The clause literals.
    pub clause: Vec<Lit<()>>,
    /// LRAT hint clause ids (used by the full Phase 2 checker).
    pub hints: Vec<u32>,
}

/// A proof: an ordered sequence of derived clauses ending (for UNSAT) in the empty
/// clause.
#[derive(Clone, Debug, Default)]
pub struct LratProof {
    steps: Vec<LratStep>,
}

impl LratProof {
    /// Build a proof from its steps.
    #[inline]
    pub fn new(steps: Vec<LratStep>) -> LratProof {
        LratProof { steps }
    }

    /// The steps.
    #[inline]
    pub fn steps(&self) -> &[LratStep] {
        &self.steps
    }
}

/// A clause's polarity state under an assignment, used by the propagation loop.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LitState {
    True,
    False,
    Unassigned,
}

/// Check whether `derived` is RUP with respect to `database` (the clauses already
/// established, including the original CNF).
///
/// Returns [`Outcome::Accept`] if assuming the negations of `derived`'s literals
/// forces a conflict (so `derived` is redundant and may be added), [`Outcome::Reject`]
/// if no conflict is forced, and [`Outcome::Inconclusive`] on malformed input (a
/// literal outside `[1, var_count]`).
#[inline]
pub fn check_rup(database: &[Vec<Lit<()>>], derived: &[Lit<()>], var_count: u32) -> Outcome {
    if var_count == 0 {
        return Outcome::Inconclusive;
    }
    let mut state = Vec::with_capacity(var_count as usize);
    state.resize(var_count as usize, LitState::Unassigned);

    // Assume the negations of the derived clause's literals.
    for lit in derived {
        let idx = lit.var().index();
        if lit.var().get() > var_count {
            return Outcome::Inconclusive;
        }
        let want = if lit.is_positive() {
            LitState::False
        } else {
            LitState::True
        };
        state[idx] = want;
    }

    // Unit propagation to fixpoint.
    let mut changed = true;
    while changed {
        changed = false;
        for clause in database {
            // The pending unit literal, if exactly one is unassigned so far: its
            // variable index *and* the state that variable must take to satisfy
            // this literal (`True` if the literal is positive, `False` if it's
            // negated) — losing the polarity here and always assigning `True`
            // would silently corrupt unit propagation for negative unit literals.
            let mut unassigned: Option<(usize, LitState)> = None;
            let mut false_count = 0usize;
            for lit in clause {
                let idx = lit.var().index();
                if lit.var().get() > var_count {
                    return Outcome::Inconclusive;
                }
                let s = state[idx];
                let polarized = if lit.is_positive() {
                    s
                } else {
                    match s {
                        LitState::True => LitState::False,
                        LitState::False => LitState::True,
                        LitState::Unassigned => LitState::Unassigned,
                    }
                };
                match polarized {
                    LitState::True => {
                        unassigned = None;
                        break;
                    }
                    LitState::False => false_count += 1,
                    LitState::Unassigned => {
                        if unassigned.is_some() {
                            unassigned = None;
                            break;
                        }
                        let desired = if lit.is_positive() {
                            LitState::True
                        } else {
                            LitState::False
                        };
                        unassigned = Some((idx, desired));
                    }
                }
            }
            if unassigned.is_none() && false_count == clause.len() && !clause.is_empty() {
                // All literals false -> conflict. The RUP clause is derivable.
                return Outcome::Accept;
            }
            if let Some((idx, desired)) = unassigned {
                if state[idx] == LitState::Unassigned {
                    state[idx] = desired;
                    changed = true;
                }
            }
        }
    }

    Outcome::Reject
}

/// Verify a full proof: every step must be RUP-derivable from the original CNF plus
/// the previously-accepted steps. If the last step is the empty clause, the formula
/// is UNSAT.
///
/// Returns [`Outcome::Accept`] only if the proof is both internally valid *and* ends
/// in the empty clause; [`Outcome::Reject`] if a step fails RUP or the proof does not
/// end in contradiction; [`Outcome::Inconclusive`] on malformed input.
#[inline]
pub fn check_proof(cnf: &[Vec<Lit<()>>], proof: &LratProof, var_count: u32) -> Outcome {
    let mut database: Vec<Vec<Lit<()>>> =
        alloc::vec::Vec::with_capacity(cnf.len() + proof.steps().len());
    for c in cnf {
        database.push(c.clone());
    }
    for step in proof.steps() {
        if check_rup(&database, &step.clause, var_count) != Outcome::Accept {
            return Outcome::Reject;
        }
        database.push(step.clause.clone());
    }
    // UNSAT requires the final derived clause to be empty (a contradiction).
    match proof.steps().last() {
        Some(last) if last.clause.is_empty() => Outcome::Accept,
        _ => Outcome::Reject,
    }
}

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
    fn rup_empty_clause_is_accept() {
        // (x1) (!x1) -> deriving empty clause is RUP.
        let db = vec![vec![Lit::new(var(1), true)], vec![Lit::new(var(1), false)]];
        assert_eq!(check_rup(&db, &[], 1), Outcome::Accept);
    }

    #[test]
    fn negative_unit_clause_alone_is_satisfiable_not_rup_empty() {
        // (!x1) alone is satisfiable (x1 = false); it must NOT let the checker
        // derive the empty clause (which would falsely certify UNSAT).
        let db = vec![vec![Lit::new(var(1), false)]];
        assert_eq!(check_rup(&db, &[], 1), Outcome::Reject);
    }

    #[test]
    fn chained_propagation_respects_polarity() {
        // x1, (!x1 or x2), (!x2 or !x3): the only models have x3 = false.
        let db = vec![
            vec![Lit::new(var(1), true)],
            vec![Lit::new(var(1), false), Lit::new(var(2), true)],
            vec![Lit::new(var(2), false), Lit::new(var(3), false)],
        ];
        // (x3) is NOT entailed (x1=T,x2=T,x3=F is a model of the database).
        assert_eq!(
            check_rup(&db, &[Lit::new(var(3), true)], 3),
            Outcome::Reject
        );
        // (!x3) IS entailed.
        assert_eq!(
            check_rup(&db, &[Lit::new(var(3), false)], 3),
            Outcome::Accept
        );
    }

    #[test]
    fn non_rup_is_reject() {
        let db = vec![vec![Lit::new(var(1), true)]];
        // (x2) is not derivable from (x1).
        assert_eq!(
            check_rup(&db, &[Lit::new(var(2), true)], 2),
            Outcome::Reject
        );
    }

    #[test]
    fn full_proof_accepts() {
        let cnf = vec![vec![Lit::new(var(1), true)], vec![Lit::new(var(1), false)]];
        let proof = LratProof::new(vec![LratStep {
            clause: vec![],
            hints: vec![],
        }]);
        assert_eq!(check_proof(&cnf, &proof, 1), Outcome::Accept);
    }

    #[test]
    fn proof_without_empty_end_is_reject() {
        let proof = LratProof::new(vec![LratStep {
            clause: vec![Lit::new(var(1), true)],
            hints: vec![],
        }]);
        assert_eq!(check_proof(&[], &proof, 1), Outcome::Reject);
    }
}
