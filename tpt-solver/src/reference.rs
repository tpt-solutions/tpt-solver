//! A small, correct reference DPLL solver.
//!
//! This is **not** the optimized engine (that lives, untrusted, in
//! `tpt-solver-core`). It exists as:
//!
//! 1. A *reference oracle* for differential testing (Phase 1 onward).
//! 2. The Phase 4 "fallback tier 3" solver — simpler and more exhaustively tested
//!    than the aggressive engine, used when the checker rejects an optimized answer.
//!
//! Every answer it produces is still validated by [`tpt_solver_check`]; nothing here
//! is trusted blindly.

use tpt_solver_check::lrat::{check_proof, LratProof, LratStep};
use tpt_solver_check::lra::check_farkas;
use tpt_solver_check::outcome::Outcome;
use tpt_solver_check::sat::{check_model, Cnf, Model};
use tpt_solver_core::engine::SolveResult;
use tpt_solver_core::ir::{Lit, VarId};
use tpt_solver_core::lra::{fourier_motzkin, FmResult, LinConstraint};
use tpt_solver_core::rational::Rational;

/// A formula in simple (non-branded) CNF: each literal is `var` (positive) or `-var`
/// (negative), `var` in `1..=var_count`.
#[derive(Clone, Debug)]
pub struct Problem {
    pub var_count: u32,
    pub clauses: Vec<Vec<i32>>,
}

impl Problem {
    /// The same problem expressed as a [`Cnf`] for the checker.
    pub fn as_cnf(&self) -> Cnf {
        let clauses = self
            .clauses
            .iter()
            .map(|c| {
                c.iter()
                    .map(|&l| {
                        let v = VarId::new(l.unsigned_abs()).expect("non-zero var");
                        Lit::new(v, l > 0)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Cnf::new(clauses)
    }
}

/// The result of the reference solver.
#[derive(Clone, Debug)]
pub struct RefResult {
    pub outcome: tpt_solver_core::engine::SolveResult,
    /// The model (var `i` -> `true`/`false`), present only on `Sat`.
    pub model: Option<Vec<bool>>,
}

/// Solve `problem` with a bounded DPLL search. Returns [`RefResult`] with
/// [`SolveResult::Unknown`](tpt_solver_core::engine::SolveResult::Unknown) if the
/// step budget (fuel) is exhausted before a decision.
pub fn solve(problem: &Problem, fuel: u64) -> RefResult {
    let n = problem.var_count as usize;
    let mut assign = vec![None; n];
    // Pre-convert clauses to (var0, polarity) pairs.
    let clauses: Vec<Vec<(usize, bool)>> = problem
        .clauses
        .iter()
        .map(|c| {
            c.iter()
                .map(|&l| ((l.unsigned_abs() as usize) - 1, l > 0))
                .collect()
        })
        .collect();

    let mut steps = 0u64;
    if dpll(&clauses, &mut assign, &mut steps, fuel) {
        RefResult {
            outcome: tpt_solver_core::engine::SolveResult::Sat,
            model: Some(assign.into_iter().map(|x| x.unwrap_or(false)).collect()),
        }
    } else if steps >= fuel {
        RefResult {
            outcome: tpt_solver_core::engine::SolveResult::Unknown,
            model: None,
        }
    } else {
        RefResult {
            outcome: tpt_solver_core::engine::SolveResult::Unsat,
            model: None,
        }
    }
}

fn satisfies(clauses: &[Vec<(usize, bool)>], assign: &[Option<bool>]) -> bool {
    for clause in clauses {
        let mut ok = false;
        for &(v, pol) in clause {
            match assign[v] {
                Some(val) if val == pol => {
                    ok = true;
                    break;
                }
                _ => {}
            }
        }
        if !ok {
            return false;
        }
    }
    true
}

fn dpll(
    clauses: &[Vec<(usize, bool)>],
    assign: &mut [Option<bool>],
    steps: &mut u64,
    fuel: u64,
) -> bool {
    if *steps >= fuel {
        return false;
    }
    *steps += 1;

    if satisfies(clauses, assign) {
        return true;
    }

    // Unit propagation: a clause with exactly one unassigned literal forces it.
    let mut changed = true;
    while changed {
        changed = false;
        for clause in clauses {
            let mut unassigned: Option<(usize, bool)> = None;
            let mut unassigned_count = 0usize;
            let mut satisfied = false;
            for &(v, pol) in clause {
                match assign[v] {
                    Some(val) if val == pol => {
                        satisfied = true;
                    }
                    Some(_) => {}
                    None => {
                        unassigned_count += 1;
                        if unassigned.is_none() {
                            unassigned = Some((v, pol));
                        }
                    }
                }
            }
            if satisfied {
                continue;
            }
            if unassigned_count == 0 {
                return false; // all assigned, none satisfied => conflict
            }
            if unassigned_count == 1 {
                if let Some((v, pol)) = unassigned {
                    if assign[v].is_none() {
                        assign[v] = Some(pol);
                        changed = true;
                    }
                }
            }
        }
    }

    // Pick an unassigned variable and branch.
    let branch = assign.iter().position(|a| a.is_none());
    match branch {
        None => satisfies(clauses, assign),
        Some(v) => {
            for guess in [true, false] {
                assign[v] = Some(guess);
                if dpll(clauses, assign, steps, fuel) {
                    return true;
                }
                assign[v] = None;
            }
            false
        }
    }
}

/// Solve and then validate the answer through the trusted checker, returning the
/// checker's three-way verdict plus the engine's raw claim.
pub fn solve_and_check(
    problem: &Problem,
    fuel: u64,
) -> (tpt_solver_core::engine::SolveResult, Outcome) {
    let result = solve(problem, fuel);
    let verdict = match &result.model {
        Some(model) => {
            let mut lits: Vec<Lit<()>> = Vec::with_capacity(model.len());
            for (i, &b) in model.iter().enumerate() {
                if let Some(v) = VarId::new((i as u32) + 1) {
                    lits.push(Lit::new(v, b));
                }
            }
            let cnf = problem.as_cnf();
            tpt_solver_check::sat::check_model(&cnf, &Model::from_lits(lits), problem.var_count)
        }
        None => Outcome::Inconclusive,
    };
    (result.outcome, verdict)
}

/// Solve with the optimized CDCL engine ([`tpt_solver_core::sat`]) and validate the
/// answer through the trusted checker. Returns the engine's claim and the checker's
/// three-way verdict.
///
/// * **SAT** — the model is re-substituted into the original CNF (`check_model`).
/// * **UNSAT** — the emitted LRAT-style proof is re-validated clause-by-clause via
///   [`check_proof`] (each step must be RUP-derivable from the original clauses plus
///   earlier steps, ending in the empty clause).
pub fn solve_and_check_cdcl(problem: &Problem, fuel: u64) -> (SolveResult, Outcome) {
    let ans = tpt_solver_core::sat::solve_cnf(problem.var_count, &problem.clauses, fuel);
    match ans.result {
        SolveResult::Sat => {
            let verdict = match ans.model {
                Some(model) => {
                    let lits: Vec<Lit<()>> = model
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &b)| VarId::new((i as u32) + 1).map(|v| Lit::new(v, b)))
                        .collect();
                    let cnf = problem.as_cnf();
                    check_model(&cnf, &Model::from_lits(lits), problem.var_count)
                }
                None => Outcome::Inconclusive,
            };
            (SolveResult::Sat, verdict)
        }
        SolveResult::Unsat => {
            let steps: Vec<LratStep> = ans
                .proof
                .iter()
                .map(|cl| LratStep {
                    clause: cl
                        .iter()
                        .filter_map(|&l| VarId::new(l.unsigned_abs()).map(|v| Lit::new(v, l > 0)))
                        .collect(),
                    hints: Vec::new(),
                })
                .collect();
            let proof = LratProof::new(steps);
            let cnf = problem.as_cnf();
            let verdict = check_proof(cnf.clauses(), &proof, problem.var_count);
            (SolveResult::Unsat, verdict)
        }
        SolveResult::Unknown => (SolveResult::Unknown, Outcome::Inconclusive),
    }
}

/// Solve a QF_LRA problem: Fourier–Motzkin decides feasibility and emits a Farkas
/// certificate on UNSAT, while a Simplex pass extracts a model on SAT. Both answers
/// are validated through the trusted kernel.
///
/// * **UNSAT** — the prover emits a Farkas certificate, re-checked coefficient-by-
///   coefficient by [`check_farkas`].
/// * **SAT** — Simplex extracts a satisfying assignment, which the kernel re-substitutes
///   into the original constraints via [`check_lra_model`]. If Simplex fails to produce
///   a model the verdict degrades to `Inconclusive` rather than a wrong `Accept`.
pub fn solve_and_check_lra(constraints: &[LinConstraint], _fuel: u64) -> (SolveResult, Outcome) {
    match fourier_motzkin(constraints) {
        Some(FmResult::Unsat(cert)) => {
            let verdict = check_farkas(constraints, &cert);
            (SolveResult::Unsat, verdict)
        }
        Some(FmResult::Sat) => match tpt_solver_core::lra::lra_model(constraints) {
            Some(Some(model)) => {
                let verdict = tpt_solver_check::lra::check_lra_model(constraints, &model);
                (SolveResult::Sat, verdict)
            }
            Some(None) => (SolveResult::Unsat, Outcome::Inconclusive),
            None => (SolveResult::Unknown, Outcome::Inconclusive),
        },
        None => (SolveResult::Unknown, Outcome::Inconclusive),
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn sat_example() {
        let p = Problem {
            var_count: 2,
            clauses: vec![vec![1], vec![2]],
        };
        let (claim, verdict) = solve_and_check(&p, 1000);
        assert_eq!(claim, tpt_solver_core::engine::SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn unsat_example() {
        let p = Problem {
            var_count: 1,
            clauses: vec![vec![1], vec![-1]],
        };
        let r = solve(&p, 1000);
        assert_eq!(r.outcome, tpt_solver_core::engine::SolveResult::Unsat);
    }

    #[test]
    fn cdcl_sat_accepts() {
        let p = Problem {
            var_count: 2,
            clauses: vec![vec![1], vec![2]],
        };
        let (claim, verdict) = solve_and_check_cdcl(&p, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn cdcl_unsat_accepts() {
        // (x1 | x2) & (!x1 | x3) & (!x2 | x3) & (!x3)  -- unsatisfiable
        let p = Problem {
            var_count: 3,
            clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]],
        };
        let (claim, verdict) = solve_and_check_cdcl(&p, 1_000_000);
        assert_eq!(claim, SolveResult::Unsat);
        assert!(
            verdict.is_accept(),
            "checker should Accept the CDCL UNSAT proof"
        );
    }

    #[test]
    fn lra_unsat_certified() {
        // x >= 1  (=> -x <= -1)  and  x <= 0  => infeasible
        let cons = vec![
            LinConstraint {
                coeffs: vec![Rational::from_i64(-1)],
                rhs: Rational::from_i64(-1),
            },
            LinConstraint {
                coeffs: vec![Rational::from_i64(1)],
                rhs: Rational::from_i64(0),
            },
        ];
        let (claim, verdict) = solve_and_check_lra(&cons, 1_000_000);
        assert_eq!(claim, SolveResult::Unsat);
        assert!(verdict.is_accept(), "kernel should Accept the Farkas certificate");
    }

    #[test]
    fn lra_sat_certified() {
        // 0 <= x <= 5, 0 <= y <= 5, x + y <= 8  => feasible
        let cons = vec![
            LinConstraint {
                coeffs: vec![Rational::from_i64(1), Rational::from_i64(0)],
                rhs: Rational::from_i64(5),
            },
            LinConstraint {
                coeffs: vec![Rational::from_i64(-1), Rational::from_i64(0)],
                rhs: Rational::from_i64(0),
            },
            LinConstraint {
                coeffs: vec![Rational::from_i64(0), Rational::from_i64(1)],
                rhs: Rational::from_i64(5),
            },
            LinConstraint {
                coeffs: vec![Rational::from_i64(0), Rational::from_i64(-1)],
                rhs: Rational::from_i64(0),
            },
            LinConstraint {
                coeffs: vec![Rational::from_i64(1), Rational::from_i64(1)],
                rhs: Rational::from_i64(8),
            },
        ];
        let (claim, verdict) = solve_and_check_lra(&cons, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept(), "kernel should Accept the Simplex model");
    }
}
