//! Parallel portfolio SAT solving (Phase 5).
//!
//! Several diverse CDCL workers race the same CNF on separate OS threads
//! (`tpt_solver_core::sat::solve_cnf_worker`, each seeded to branch
//! differently — see that function's docs). They share one cooperative
//! [`Cancel`] flag: the moment any worker's answer is checker-`Accept`ed, the
//! flag is set and every other worker notices it (polled once per search
//! step) and stops promptly, instead of running to its own fuel exhaustion.
//!
//! This is the one piece of shared-state concurrency the suite introduces;
//! `tpt-solver-core/tests/loom_cancel.rs` model-checks the flag itself under
//! every thread interleaving `loom` can enumerate. Everything past that flag
//! — spawning threads, collecting results — is ordinary `std::sync::mpsc`
//! message passing, no further shared mutable state.
//!
//! Every answer, however it was produced, still goes through exactly the
//! same trusted-checker logic as the sequential path
//! ([`crate::reference::check_cdcl_answer`]) — racing workers changes nothing
//! about what may be trusted.

use std::sync::{mpsc, Arc};
use std::thread;

use crate::reference::{check_cdcl_answer, Problem};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::cancel::Cancel;
use tpt_solver_core::engine::SolveResult;
use tpt_solver_core::sat::solve_cnf_worker;

/// Race `workers` (clamped to at least 1) diverse CDCL workers against
/// `problem`, each given `fuel_per_worker` fuel. Returns the first
/// checker-`Accept`ed `(claim, verdict)`; if none of the workers are
/// accepted, returns the first worker's raw (non-`Accept`) result — the
/// fail-closed decision of what to do next belongs one layer up, in
/// [`crate::policy::solve_certified_portfolio`].
pub fn solve_and_check_cdcl_portfolio(
    problem: &Problem,
    fuel_per_worker: u64,
    workers: usize,
) -> (SolveResult, Outcome) {
    let workers = workers.max(1);
    let clauses = Arc::new(problem.clauses.clone());
    let var_count = problem.var_count;
    let cancel = Cancel::shared();
    let (tx, rx) = mpsc::channel();

    let handles: Vec<_> = (0..workers)
        .map(|w| {
            let clauses = Arc::clone(&clauses);
            let cancel = cancel.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let ans = solve_cnf_worker(var_count, &clauses, fuel_per_worker, w as u64, cancel);
                let _ = tx.send(ans);
            })
        })
        .collect();
    // Drop our own sender so the channel closes once every worker's clone is
    // dropped (i.e. once every worker has finished), letting `for ans in rx`
    // below terminate instead of blocking forever.
    drop(tx);

    let mut fallback: Option<(SolveResult, Outcome)> = None;
    for ans in rx {
        let verdict = check_cdcl_answer(problem, ans);
        if verdict.1.is_accept() {
            cancel.request();
            for h in handles {
                let _ = h.join();
            }
            return verdict;
        }
        if fallback.is_none() {
            fallback = Some(verdict);
        }
    }
    for h in handles {
        let _ = h.join();
    }
    fallback.unwrap_or((SolveResult::Unknown, Outcome::Inconclusive))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policy::solve_certified_portfolio;

    #[test]
    fn sat_accepts() {
        let p = Problem {
            var_count: 2,
            clauses: vec![vec![1], vec![2]],
        };
        let (claim, verdict) = solve_and_check_cdcl_portfolio(&p, 1_000_000, 3);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn unsat_accepts() {
        let p = Problem {
            var_count: 3,
            clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]],
        };
        let (claim, verdict) = solve_and_check_cdcl_portfolio(&p, 1_000_000, 3);
        assert_eq!(claim, SolveResult::Unsat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn single_worker_matches_sequential() {
        let p = Problem {
            var_count: 4,
            clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 4], vec![-3, -4]],
        };
        let (claim, verdict) = solve_and_check_cdcl_portfolio(&p, 1_000_000, 1);
        assert!(verdict.is_accept());
        assert_ne!(claim, SolveResult::Unknown);
    }

    #[test]
    fn portfolio_agrees_with_brute_force() {
        // Same oracle idiom as `sat::tests::solve_cnf_agrees_with_brute_force`,
        // but through the certified portfolio path: only ever trust an
        // `Accept`ed claim, and it must match exhaustive enumeration.
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0
            }
            fn below(&mut self, n: u64) -> u64 {
                self.next() % n
            }
        }
        let mut rng = Lcg(0xC0FFEE);
        let brute = |n: u32, cls: &[Vec<i32>]| -> bool {
            let total = 1u32 << n;
            let mut a = 0u32;
            while a < total {
                let ok = cls.iter().all(|c| {
                    c.iter().any(|&l| {
                        let v = (l.unsigned_abs()) - 1;
                        let bit = (a >> v) & 1 == 1;
                        if l > 0 {
                            bit
                        } else {
                            !bit
                        }
                    })
                });
                if ok {
                    return true;
                }
                a += 1;
            }
            false
        };
        for _ in 0..300u32 {
            let n = 1 + rng.below(6) as u32; // 1..6 vars
            let nclauses = 1 + rng.below(5) as u32;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..nclauses {
                let len = 1 + rng.below(3) as u32;
                let mut c: Vec<i32> = Vec::new();
                for _ in 0..len {
                    let v = 1 + rng.below(n as u64) as i32;
                    let sign: i32 = if rng.below(2) == 0 { 1 } else { -1 };
                    c.push(sign * v);
                }
                cls.push(c);
            }
            let sat = brute(n, &cls);
            let p = Problem {
                var_count: n,
                clauses: cls.clone(),
            };
            let (claim, verdict, _dump) = solve_certified_portfolio(&p, 200_000, 3);
            if !verdict.is_accept() {
                continue; // only `Accept`ed claims are trusted; skip anything else.
            }
            match claim {
                SolveResult::Sat => assert!(sat, "portfolio SAT but formula is UNSAT: {:?}", cls),
                SolveResult::Unsat => {
                    assert!(!sat, "portfolio UNSAT but formula is SAT: {:?}", cls)
                }
                SolveResult::Unknown => {}
            }
        }
    }
}
