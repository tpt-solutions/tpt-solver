//! CDCL SAT engine — the untrusted search core (Phase 2).
//!
//! Implements conflict-driven clause learning with two-watched literals, VSIDS
//! branching, restarts, and learnt-clause deletion. Every answer is recheckable:
//!
//! * **SAT** — a model is produced; the periphery re-substitutes it into the original
//!   CNF via [`tpt_solver_check`].
//! * **UNSAT** — a sequence of learned clauses is emitted as an LRAT-style proof
//!   (each step is RUP-derivable from the original clauses plus earlier steps; the
//!   final step is the empty clause). The periphery validates the whole chain with
//!   [`tpt_solver_check::lrat`].
//!
//! The engine is *not* trusted: if it ever emits an unsound clause, the checker
//! rejects it. The engine itself never panics and always respects its [`Fuel`].

use crate::engine::SolveResult;
use crate::fuel::Fuel;

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

/// The result of [`solve_cnf`], including the evidence needed to recheck it.
#[derive(Clone, Debug)]
pub struct SatAnswer {
    /// The engine's (untrusted) claim.
    pub result: SolveResult,
    /// Satisfying assignment (var `i` -> value), present only on `Sat`.
    pub model: Option<Vec<bool>>,
    /// Learned clauses in derivation order, last entry the empty clause on `Unsat`.
    /// Used by the checker to validate the UNSAT proof.
    pub proof: Vec<Vec<i32>>,
}

#[derive(Clone, Copy, Debug)]
struct Watcher {
    clause: usize,
    /// The other watched literal (as an `i32`); if it is currently true the watched
    /// clause is satisfied and needs no work.
    blocking: i32,
}

#[derive(Clone, Debug)]
struct Clause {
    lits: Vec<i32>,
    learnt: bool,
    activity: f64,
}

enum Prop {
    Ok,
    Conflict(usize),
    Fuel,
}

/// A CDCL solver instance over a fixed set of variables.
pub struct CdclSolver {
    n_vars: u32,
    clauses: Vec<Clause>,
    watchers: Vec<Vec<Watcher>>,
    assigns: Vec<Option<bool>>,
    level: Vec<i32>,
    reason: Vec<Option<usize>>,
    trail: Vec<i32>,
    trail_lim: Vec<usize>,
    propagate_head: usize,
    unassigned: u32,
    activity: Vec<f64>,
    polarity: Vec<bool>,
    conflicts: u32,
    restart_limit: u32,
    fuel: Fuel,
    proof: Vec<Vec<i32>>,
}

impl CdclSolver {
    fn new(n_vars: u32, fuel: Fuel) -> CdclSolver {
        let n = n_vars as usize;
        CdclSolver {
            n_vars,
            clauses: Vec::new(),
            watchers: vec![Vec::new(); 2 * n],
            assigns: vec![None; n],
            level: vec![0; n],
            reason: vec![None; n],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            propagate_head: 0,
            unassigned: n_vars,
            activity: vec![0.0; n],
            polarity: vec![true; n],
            conflicts: 0,
            restart_limit: core::cmp::max(100, n_vars),
            fuel,
            proof: Vec::new(),
        }
    }

    #[inline]
    fn lit_code(&self, l: i32) -> usize {
        (((l.unsigned_abs() as usize) - 1) << 1) + if l > 0 { 0 } else { 1 }
    }

    #[inline]
    fn negate(l: i32) -> i32 {
        -l
    }

    #[inline]
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    #[inline]
    fn value(&self, l: i32) -> Option<bool> {
        let v = (l.unsigned_abs() as usize) - 1;
        self.assigns[v].map(|b| if l > 0 { b } else { !b })
    }

    #[inline]
    fn is_true(&self, l: i32) -> bool {
        self.value(l) == Some(true)
    }

    #[inline]
    fn is_false(&self, l: i32) -> bool {
        self.value(l) == Some(false)
    }

    fn enqueue(&mut self, l: i32, reason: Option<usize>) -> bool {
        let v = (l.unsigned_abs() as usize) - 1;
        if let Some(b) = self.assigns[v] {
            return b == (l > 0);
        }
        self.assigns[v] = Some(l > 0);
        self.level[v] = self.decision_level() as i32;
        self.reason[v] = reason;
        self.polarity[v] = l > 0;
        self.trail.push(l);
        self.unassigned -= 1;
        true
    }

    fn add_clause(&mut self, lits: &[i32]) -> bool {
        // Returns false only if an empty clause is given (immediate UNSAT).
        if lits.is_empty() {
            return false;
        }
        if lits.len() == 1 {
            let ok = self.enqueue(lits[0], None);
            return ok || self.is_true(lits[0]);
        }
        self.clauses.push(Clause {
            lits: lits.to_vec(),
            learnt: false,
            activity: 0.0,
        });
        let idx = self.clauses.len() - 1;
        let c = &self.clauses[idx];
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        let code0 = self.lit_code(l0);
        let code1 = self.lit_code(l1);
        self.watchers[code0].push(Watcher {
            clause: idx,
            blocking: l1,
        });
        self.watchers[code1].push(Watcher {
            clause: idx,
            blocking: l0,
        });
        true
    }

    fn propagate(&mut self) -> Prop {
        while self.propagate_head < self.trail.len() {
            if !self.fuel.burn_one() {
                return Prop::Fuel;
            }
            let l = self.trail[self.propagate_head];
            self.propagate_head += 1;
            let false_lit = Self::negate(l);
            let fc = self.lit_code(false_lit);
            let mut w_i = 0;
            while w_i < self.watchers[fc].len() {
                let w = self.watchers[fc][w_i];
                if self.is_true(w.blocking) {
                    w_i += 1;
                    continue;
                }
                let clause_idx = w.clause;
                let mut cl = self.clauses[clause_idx].lits.clone();
                let pos_fc = if self.lit_code(cl[0]) == fc { 0 } else { 1 };
                let pos_other = 1 - pos_fc;
                let other = cl[pos_other];
                let mut satisfied = false;
                let mut alt: Option<usize> = None;
                let mut k = 2;
                while k < cl.len() {
                    let c = cl[k];
                    if self.is_true(c) {
                        satisfied = true;
                        break;
                    }
                    if !self.is_false(c) {
                        alt = Some(k);
                        break;
                    }
                    k += 1;
                }
                if satisfied {
                    w_i += 1;
                    continue;
                }
                match alt {
                    Some(k) => {
                        cl.swap(pos_fc, k);
                        self.clauses[clause_idx].lits = cl;
                        let new_code = self.lit_code(self.clauses[clause_idx].lits[pos_fc]);
                        self.watchers[fc].swap_remove(w_i);
                        self.watchers[new_code].push(Watcher {
                            clause: clause_idx,
                            blocking: other,
                        });
                    }
                    None => {
                        if self.is_false(other) {
                            return Prop::Conflict(clause_idx);
                        }
                        if !self.enqueue(other, Some(clause_idx)) {
                            return Prop::Conflict(clause_idx);
                        }
                        w_i += 1;
                    }
                }
            }
        }
        Prop::Ok
    }

    fn analyze(&mut self, confl: usize) -> (Vec<i32>, usize) {
        let n = self.n_vars as usize;
        let mut seen = vec![false; n + 1];
        let mut out_learnt: Vec<i32> = Vec::new();
        out_learnt.push(0); // placeholder for asserting literal
        let mut out_btlevel: usize = 0;
        let mut index = self.trail.len();
        let mut path_c: i32 = 0;
        let mut p: i32 = 0;
        let mut conflict_clause = confl;
        loop {
            let cl = self.clauses[conflict_clause].lits.clone();
            let start = if p == 0 { 0 } else { 1 };
            let mut j = start;
            while j < cl.len() {
                let q = cl[j];
                let v = q.unsigned_abs() as usize;
                if !seen[v] && self.level[v - 1] > 0 {
                    self.bump_var_activity(v - 1);
                    seen[v] = true;
                    if (self.level[v - 1] as usize) >= self.decision_level() {
                        path_c += 1;
                    }
                    out_learnt.push(q);
                }
                j += 1;
            }
            loop {
                index -= 1;
                p = self.trail[index];
                if seen[p.unsigned_abs() as usize] {
                    break;
                }
            }
            let pv = (p.unsigned_abs() as usize) - 1;
            seen[pv + 1] = false;
            path_c -= 1;
            if path_c > 0 {
                match self.reason[pv] {
                    Some(r) => conflict_clause = r,
                    None => break,
                }
            } else {
                break;
            }
        }
        out_learnt[0] = Self::negate(p);
        let mut i = 1;
        while i < out_learnt.len() {
            let lv = self.level[(out_learnt[i].unsigned_abs() as usize) - 1] as usize;
            if lv > out_btlevel {
                out_btlevel = lv;
            }
            i += 1;
        }
        let mut i = 0;
        while i < out_learnt.len() {
            seen[out_learnt[i].unsigned_abs() as usize] = false;
            i += 1;
        }
        (out_learnt, out_btlevel)
    }

    fn cancel_until(&mut self, level: usize) {
        while self.trail_lim.len() > level {
            let start = match self.trail_lim.last() {
                Some(&s) => s,
                None => break,
            };
            while self.trail.len() > start {
                let l = match self.trail.pop() {
                    Some(x) => x,
                    None => break,
                };
                let v = (l.unsigned_abs() as usize) - 1;
                self.assigns[v] = None;
                self.level[v] = 0;
                self.reason[v] = None;
                self.unassigned += 1;
            }
            self.trail_lim.pop();
        }
    }

    fn bump_var_activity(&mut self, v: usize) {
        self.activity[v] += 1.0;
        if self.activity[v] > 1e100 {
            let mut i = 0;
            while i < self.activity.len() {
                self.activity[i] *= 1e-100;
                i += 1;
            }
        }
    }

    fn decide(&mut self) {
        // Pick the unassigned variable with the highest activity.
        let mut best: i32 = -1;
        let mut best_act = -1.0f64;
        let mut v = 0;
        while v < self.n_vars as usize {
            if self.assigns[v].is_none() && self.activity[v] > best_act {
                best_act = self.activity[v];
                best = v as i32;
            }
            v += 1;
        }
        if best < 0 {
            return; // none unassigned (caller checks unassigned==0 first)
        }
        let var = (best as usize) + 1;
        let lit = if self.polarity[best as usize] {
            var as i32
        } else {
            -(var as i32)
        };
        self.trail_lim.push(self.trail.len());
        self.enqueue(lit, None);
    }

    fn add_learnt(&mut self, lits: &[i32]) {
        if lits.is_empty() {
            self.proof.push(Vec::new());
            return;
        }
        if lits.len() == 1 {
            self.proof.push(lits.to_vec());
            self.enqueue(lits[0], None);
            return;
        }
        let idx = self.clauses.len();
        self.clauses.push(Clause {
            lits: lits.to_vec(),
            learnt: true,
            activity: 0.0,
        });
        let c = &self.clauses[idx];
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        let code0 = self.lit_code(l0);
        let code1 = self.lit_code(l1);
        self.watchers[code0].push(Watcher {
            clause: idx,
            blocking: l1,
        });
        self.watchers[code1].push(Watcher {
            clause: idx,
            blocking: l0,
        });
        self.proof.push(lits.to_vec());
        // Enqueue the asserting literal (lits[0]).
        let _ = self.enqueue(l0, Some(idx));
    }

    fn reduce_db(&mut self) {
        let mut learnt_acts: Vec<f64> = Vec::new();
        for c in self.clauses.iter() {
            if c.learnt {
                learnt_acts.push(c.activity);
            }
        }
        let limit = (self.n_vars as f64) * 4.0 + 16.0;
        if (learnt_acts.len() as f64) <= limit {
            return;
        }
        learnt_acts.sort_by(|a, b| a.partial_cmp(b).unwrap_or(core::cmp::Ordering::Equal));
        let cutoff = learnt_acts[learnt_acts.len() / 2];
        let kept: Vec<Clause> = self
            .clauses
            .iter()
            .filter(|c| !c.learnt || c.activity >= cutoff)
            .cloned()
            .collect();
        self.clauses = kept;
        self.watchers = vec![Vec::new(); 2 * self.n_vars as usize];
        let mut idx = 0;
        while idx < self.clauses.len() {
            let len = self.clauses[idx].lits.len();
            if len >= 2 {
                let l0 = self.clauses[idx].lits[0];
                let l1 = self.clauses[idx].lits[1];
                let code0 = self.lit_code(l0);
                let code1 = self.lit_code(l1);
                self.watchers[code0].push(Watcher {
                    clause: idx,
                    blocking: l1,
                });
                self.watchers[code1].push(Watcher {
                    clause: idx,
                    blocking: l0,
                });
            } else if len == 1 {
                let _ = self.enqueue(self.clauses[idx].lits[0], None);
            }
            idx += 1;
        }
    }

    fn restart(&mut self) {
        self.cancel_until(0);
        self.restart_limit = ((self.restart_limit as f64) * 1.5) as u32 + 1;
        let mut i = 0;
        while i < self.activity.len() {
            self.activity[i] *= 0.95;
            i += 1;
        }
        self.reduce_db();
    }

    fn search(&mut self) -> SolveResult {
        loop {
            if !self.fuel.burn_one() {
                return SolveResult::Unknown;
            }
            match self.propagate() {
                Prop::Ok => {
                    if self.unassigned == 0 {
                        return SolveResult::Sat;
                    }
                    self.decide();
                    if self.conflicts >= self.restart_limit {
                        self.restart();
                    }
                }
                Prop::Conflict(c) => {
                    self.conflicts += 1;
                    if self.decision_level() == 0 {
                        self.proof.push(Vec::new());
                        return SolveResult::Unsat;
                    }
                    let (learnt, btlevel) = self.analyze(c);
                    self.cancel_until(btlevel);
                    self.add_learnt(&learnt);
                }
                Prop::Fuel => return SolveResult::Unknown,
            }
        }
    }

    fn model(&self) -> Vec<bool> {
        let mut m = vec![false; self.n_vars as usize];
        let mut v = 0;
        while v < self.n_vars as usize {
            m[v] = self.assigns[v] == Some(true);
            v += 1;
        }
        m
    }
}

/// Solve a CNF with `n_vars` variables (1-based) and the given clauses.
///
/// Returns the engine's claim plus a model (on `Sat`) or an LRAT-style proof (on
/// `Unsat`). The result is untrusted until rechecked by [`tpt_solver_check`].
pub fn solve_cnf(n_vars: u32, clauses: &[Vec<i32>], fuel: u64) -> SatAnswer {
    let mut s = CdclSolver::new(n_vars, Fuel::new(fuel));
    for c in clauses {
        if !s.add_clause(c) {
            return SatAnswer {
                result: SolveResult::Unsat,
                model: None,
                proof: vec![Vec::new()],
            };
        }
    }
    let res = s.search();
    match res {
        SolveResult::Sat => SatAnswer {
            result: SolveResult::Sat,
            model: Some(s.model()),
            proof: s.proof,
        },
        SolveResult::Unsat => SatAnswer {
            result: SolveResult::Unsat,
            model: None,
            proof: s.proof,
        },
        SolveResult::Unknown => SatAnswer {
            result: SolveResult::Unknown,
            model: None,
            proof: s.proof,
        },
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn sat_simple() {
        // (x1) & (x2)
        let a = solve_cnf(2, &[vec![1], vec![2]], 1_000_000);
        assert_eq!(a.result, SolveResult::Sat);
        assert_eq!(a.model.as_ref().unwrap(), &[true, true]);
    }

    #[test]
    fn unsat_simple() {
        // (x1) & (!x1)
        let a = solve_cnf(1, &[vec![1], vec![-1]], 1_000_000);
        assert_eq!(a.result, SolveResult::Unsat);
        assert!(a.proof.last().unwrap().is_empty());
    }

    #[test]
    fn unsat_chain() {
        // (x1 | x2) & (!x1 | x3) & (!x2 | x3) & (!x3)
        let clauses = vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]];
        let a = solve_cnf(3, &clauses, 1_000_000);
        assert_eq!(a.result, SolveResult::Unsat);
    }

    #[test]
    fn unsat_php_small() {
        // Contradiction chain: x1, (x1->x2), (x2->x3), (!x1 | !x3)
        let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-1, -3]];
        let a = solve_cnf(3, &clauses, 1_000_000);
        assert_eq!(a.result, SolveResult::Unsat);
    }

    #[test]
    fn fuel_exhaustion_no_panic() {
        let mut clauses = Vec::new();
        for i in 0..50u32 {
            clauses.push(vec![(i * 2 + 1) as i32, (i * 2 + 2) as i32]);
        }
        let a = solve_cnf(100, &clauses, 5);
        assert!(matches!(
            a.result,
            SolveResult::Unknown | SolveResult::Sat | SolveResult::Unsat
        ));
    }
}
