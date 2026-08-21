//! Tiered live-request fallback policy and rejection bookkeeping (spec §6.2–6.3).
//!
//! The certificate architecture answers "is an answer correct?" but not "what does
//! the *system* do when the checker rejects?" These are ops questions, answered here:
//!
//! * **Fail-closed, not fail-open.** A rejected (or merely *inconclusive*) answer is
//!   never trusted. We retry cheaper-and-safer paths before ever returning
//!   `Unknown`.
//! * **Three fallback tiers** (`FallbackTier`): reseed-and-recheck, escalate, fall
//!   back to the simpler/more-exhaustively-tested solver, with `Unknown` as the true
//!   last resort.
//! * **Rejections are dumped** automatically (`RejectionDump`) for post-mortem.
//! * **Rates are tracked** (`VerdictTracker`) — accept/reject/inconclusive as a triad,
//!   so "safe but unproductive" regressions are visible, not just soundness bugs.

use crate::reference::{solve_and_check, solve_and_check_cdcl, Problem};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;

/// The fallback tier reached after a checker rejection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FallbackTier {
    /// Tier 1: a rejected SAT answer was retried with a different seed/heuristic and
    /// rechecked (rechecking a model is cheap).
    Reseed,
    /// Tier 2/3: escalated past the rejected path and fell back to the simpler,
    /// more exhaustively-tested solver (reference DPLL) before giving up.
    SimplerSolver,
    /// Tier 4: every path was exhausted or timed out — `Unknown` is the honest last
    /// resort, never the first response.
    Unknown,
}

/// A mandatory post-mortem record produced whenever the checker does not `Accept`.
#[derive(Clone, Debug)]
pub struct RejectionDump {
    pub var_count: u32,
    pub clause_count: usize,
    /// Whether the (rejected) engine produced a certificate at all.
    pub certificate_present: bool,
    /// Which engine path produced the rejected answer (e.g. `"cdcl(sat)"`).
    pub engine_path: &'static str,
    /// The deepest fallback tier reached before giving up.
    pub tier_reached: FallbackTier,
}

impl RejectionDump {
    /// Render the dump as a single-line, log-friendly string.
    pub fn render(&self) -> String {
        format!(
            "rejection: vars={} clauses={} cert={} engine={} tier={:?}",
            self.var_count,
            self.clause_count,
            self.certificate_present,
            self.engine_path,
            self.tier_reached
        )
    }
}

/// Tracks accept/reject/inconclusive counts across a corpus or live traffic.
///
/// Per spec §6.3 these are reported as a *triad* — "safe" (accept) and "useful"
/// (not constantly rejecting) are both visible.
#[derive(Clone, Copy, Debug, Default)]
pub struct VerdictTracker {
    accept: u64,
    reject: u64,
    inconclusive: u64,
}

impl VerdictTracker {
    pub fn new() -> VerdictTracker {
        VerdictTracker::default()
    }

    pub fn record(&mut self, outcome: Outcome) {
        if outcome.is_accept() {
            self.accept += 1;
        } else if outcome.is_reject() {
            self.reject += 1;
        } else {
            self.inconclusive += 1;
        }
    }

    pub fn accept(&self) -> u64 {
        self.accept
    }
    pub fn reject(&self) -> u64 {
        self.reject
    }
    pub fn inconclusive(&self) -> u64 {
        self.inconclusive
    }

    /// Reject rate in `[0, 1]`: `reject / total`.
    pub fn reject_rate(&self) -> f64 {
        let total = self.accept + self.reject + self.inconclusive;
        if total == 0 {
            0.0
        } else {
            self.reject as f64 / total as f64
        }
    }

    /// Inconclusive rate in `[0, 1]`.
    pub fn inconclusive_rate(&self) -> f64 {
        let total = self.accept + self.reject + self.inconclusive;
        if total == 0 {
            0.0
        } else {
            self.inconclusive as f64 / total as f64
        }
    }

    /// Whether the reject rate stays below `limit` (the spec's merge-gate threshold).
    pub fn within_reject_threshold(&self, limit: f64) -> bool {
        self.reject_rate() <= limit
    }
}

/// Solve a problem through the full certified pipeline with tiered fallback.
///
/// 1. Tier 0 — optimized CDCL, certified by the kernel.
/// 2. On non-`Accept`, fall back to the simpler, more-exhaustively-tested reference
///    DPLL solver (Tier 3) and recertify.
/// 3. If still not `Accept`, return the (untrusted) last answer with
///    [`FallbackTier::Unknown`] and a [`RejectionDump`] for post-mortem.
///
/// Only an `Accept` verdict may be trusted by the caller.
pub fn solve_certified(
    problem: &Problem,
    fuel: u64,
) -> (SolveResult, Outcome, Option<RejectionDump>) {
    let (claim, verdict) = solve_and_check_cdcl(problem, fuel);
    if verdict.is_accept() {
        return (claim, verdict, None);
    }

    let first_engine: &'static str = match claim {
        SolveResult::Sat => "cdcl(sat)",
        SolveResult::Unsat => "cdcl(unsat)",
        SolveResult::Unknown => "cdcl(unknown)",
    };
    let cert_present = claim != SolveResult::Unknown;

    // Fallback tier: simpler, exhaustively-tested solver (reference DPLL), recertified.
    let (claim2, verdict2) = solve_and_check(problem, fuel);
    if verdict2.is_accept() {
        let dump = RejectionDump {
            var_count: problem.var_count,
            clause_count: problem.clauses.len(),
            certificate_present: cert_present,
            engine_path: first_engine,
            tier_reached: FallbackTier::SimplerSolver,
        };
        return (claim2, verdict2, Some(dump));
    }

    let dump = RejectionDump {
        var_count: problem.var_count,
        clause_count: problem.clauses.len(),
        certificate_present: cert_present,
        engine_path: first_engine,
        tier_reached: FallbackTier::Unknown,
    };
    (claim2, verdict2, Some(dump))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_accepts_without_dump() {
        let p = Problem {
            var_count: 2,
            clauses: vec![vec![1], vec![2]],
        };
        let (claim, verdict, dump) = solve_certified(&p, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
        assert!(dump.is_none());
    }

    #[test]
    fn unsat_accepts_via_cdcl() {
        let p = Problem {
            var_count: 3,
            clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]],
        };
        let (claim, verdict, dump) = solve_certified(&p, 1_000_000);
        assert_eq!(claim, SolveResult::Unsat);
        assert!(verdict.is_accept());
        assert!(dump.is_none());
    }

    #[test]
    fn verdict_tracker_rates() {
        let mut t = VerdictTracker::new();
        t.record(Outcome::Accept);
        t.record(Outcome::Accept);
        t.record(Outcome::Reject);
        t.record(Outcome::Inconclusive);
        assert!((t.reject_rate() - 0.25).abs() < 1e-9);
        assert!((t.inconclusive_rate() - 0.25).abs() < 1e-9);
        assert!(t.within_reject_threshold(0.5));
        assert!(!t.within_reject_threshold(0.1));
    }

    #[test]
    fn rejection_dump_renders() {
        let d = RejectionDump {
            var_count: 3,
            clause_count: 4,
            certificate_present: true,
            engine_path: "cdcl(sat)",
            tier_reached: FallbackTier::SimplerSolver,
        };
        let s = d.render();
        assert!(s.contains("vars=3"));
        assert!(s.contains("tier=SimplerSolver"));
    }
}
