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

use crate::cancel::Cancel;
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
    cancel: Cancel,
    proof: Vec<Vec<i32>>,
}

/// Derive variable `v`'s initial branching polarity from a portfolio `seed`.
///
/// A cheap mixing function (not cryptographic — just enough to decorrelate
/// workers sharing the same `seed=0` baseline). `seed == 0` reproduces the
/// engine's original always-`true` initial polarity, so [`solve_cnf`]'s
/// behavior (and every existing test) is unchanged.
#[inline]
fn seeded_polarity(seed: u64, v: u32) -> bool {
    if seed == 0 {
        return true;
    }
    let mixed = (seed ^ v as u64).wrapping_mul(0x9E3779B97F4A7C15);
    (mixed >> 63) == 1
}

impl CdclSolver {
    fn new(n_vars: u32, fuel: Fuel, seed: u64, cancel: Cancel) -> CdclSolver {
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
            polarity: (0..n_vars).map(|v| seeded_polarity(seed, v)).collect(),
            conflicts: 0,
            restart_limit: core::cmp::max(100, n_vars),
            fuel,
            cancel,
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

    /// Dedupe literals and detect tautologies. Returns `None` for a tautology
    /// (contains both `l` and `-l`), `Some(deduped)` otherwise (order-preserving,
    /// first occurrence wins).
    fn normalize_clause(lits: &[i32]) -> Option<Vec<i32>> {
        let mut out: Vec<i32> = Vec::with_capacity(lits.len());
        for &l in lits {
            if out.contains(&-l) {
                return None;
            }
            if !out.contains(&l) {
                out.push(l);
            }
        }
        Some(out)
    }

    fn add_clause(&mut self, lits: &[i32]) -> bool {
        // Normalize first: dedupe repeated literals and drop tautologies (a clause
        // containing both `l` and `-l` is trivially satisfied and adds no
        // constraint). Without this, a duplicated literal ends up watched twice
        // from the *same* watcher bucket (`lit_code(lits[0]) == lit_code(lits[1])`),
        // and the second, now-stale watcher entry corrupts propagation once the
        // first entry triggers a swap — a real soundness bug caught by differential
        // testing (CDCL claiming Sat with a model the checker rejects).
        let lits = match Self::normalize_clause(lits) {
            Some(l) => l,
            None => return true, // tautology: trivially satisfied, nothing to add
        };
        let lits = lits.as_slice();
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

    /// First-UIP conflict analysis (MiniSat-style).
    ///
    /// Only literals from levels *below* the current one are collected into
    /// the learnt clause; current-level literals merely count toward `pathC`
    /// and are represented by the final pivot (`learnt[0] = ¬p`). Collecting
    /// current-level literals too would yield clauses that are implied but
    /// *not asserting* — they backtrack nowhere, fail to enqueue, and break
    /// the RUP chain the kernel re-validates.
    ///
    /// Returns an empty clause as a bail-out signal if the reason chain is
    /// malformed (the caller backtracks to level 0 without learning).
    fn analyze(&mut self, confl: usize) -> (Vec<i32>, usize) {
        let n = self.n_vars as usize;
        let mut seen = vec![false; n + 1];
        let mut learnt: Vec<i32> = Vec::new();
        let mut btlevel: usize = 0;
        let mut index = self.trail.len();
        let mut path_c: i32 = 0;
        let mut p: i32;
        let mut conflict_clause = confl;
        loop {
            let cl = self.clauses[conflict_clause].lits.clone();
            // Scan every literal, including position 0: unlike MiniSat,
            // `propagate` does not guarantee the propagated literal sits at
            // index 0 of its reason clause (a watch swap can leave it at
            // index 1 instead), so skipping index 0 on non-initial clauses
            // silently dropped a real antecedent literal from the
            // resolution. The pivot itself is excluded correctly below by
            // the `value(q) == Some(false)` guard: it is on the trail as
            // true, so it never re-qualifies.
            let mut j = 0;
            while j < cl.len() {
                let q = cl[j];
                let vq = q.unsigned_abs() as usize;
                if !seen[vq] {
                    // Only literal-false literals are part of the conflict; a
                    // satisfied literal plays no role in the resolution and must
                    // not be marked seen (doing so corrupts the path-count and
                    // the trail scan, which previously sent the search into an
                    // unrecoverable empty-learnt bail that burned all fuel).
                    if self.value(q) == Some(false) {
                        seen[vq] = true;
                        self.bump_var_activity(vq - 1);
                        if (self.level[vq - 1] as usize) >= self.decision_level() {
                            path_c += 1;
                        } else {
                            learnt.push(q);
                            let lv = self.level[vq - 1] as usize;
                            if lv > btlevel {
                                btlevel = lv;
                            }
                        }
                    }
                }
                j += 1;
            }
            // Most recent seen literal on the trail.
            loop {
                if index == 0 {
                    // Malformed reason chain; bail out (caller restarts at 0).
                    return (Vec::new(), 0);
                }
                index -= 1;
                p = self.trail[index];
                if seen[p.unsigned_abs() as usize] {
                    break;
                }
            }
            seen[p.unsigned_abs() as usize] = false;
            path_c -= 1;
            if path_c <= 0 {
                break;
            }
            match self.reason[(p.unsigned_abs() as usize) - 1] {
                Some(r) => conflict_clause = r,
                None => break, // decision var mid-path: bail out
            }
        }
        learnt.insert(0, Self::negate(p));
        (learnt, btlevel)
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
        // Backtracking popped already-trailed literals; anything between the
        // new trail length and the old propagation head was cancelled and
        // must never be propagated. Without clamping, the head can sit past
        // the trail end so `propagate` becomes a no-op, decisions fill every
        // remaining variable, and the search returns "Sat" with a model that
        // violates clauses — caught by the bit-vector certification tests.
        if self.propagate_head > self.trail.len() {
            self.propagate_head = self.trail.len();
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

    /// Add a learnt clause and enqueue its asserting literal.
    ///
    /// Returns `false` when the learnt clause is already falsified under the
    /// current assignment — a level-0 contradiction (the asserting literal is
    /// assigned the wrong way), which the caller must surface as UNSAT.
    /// Swallowing that failure lets the search continue from a violated
    /// learnt clause and eventually claim `Sat` with a model violating the
    /// *original* clauses — a soundness bug caught by the bit-vector
    /// certification tests.
    fn add_learnt(&mut self, lits: &[i32]) -> bool {
        if lits.is_empty() {
            self.proof.push(Vec::new());
            return false;
        }
        if lits.len() == 1 {
            self.proof.push(lits.to_vec());
            return self.enqueue(lits[0], None);
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
        // Enqueue the asserting literal (lits[0]); failure = falsified learnt.
        self.enqueue(l0, Some(idx))
    }

    /// Delete half of the learnt clauses (lowest activity) and rebuild the
    /// watcher lists.
    ///
    /// Returns `false` when a survivor clause is falsified by the (level-0)
    /// current assignment — an immediate UNSAT. The rebuild must watch
    /// non-false literals where possible: blindly watching `lits[0..2]` can
    /// pick two already-false literals, after which the clause is never
    /// visited again even when it should propagate or conflict — a soundness
    /// bug (bogus `Sat` models) caught by the bit-vector certification tests.
    fn reduce_db(&mut self) -> bool {
        let mut learnt_acts: Vec<f64> = Vec::new();
        for c in self.clauses.iter() {
            if c.learnt {
                learnt_acts.push(c.activity);
            }
        }
        let limit = (self.n_vars as f64) * 4.0 + 16.0;
        if (learnt_acts.len() as f64) > limit {
            learnt_acts.sort_by(|a, b| a.partial_cmp(b).unwrap_or(core::cmp::Ordering::Equal));
            let cutoff = learnt_acts[learnt_acts.len() / 2];
            let kept: Vec<Clause> = self
                .clauses
                .iter()
                .filter(|c| !c.learnt || c.activity >= cutoff)
                .cloned()
                .collect();
            self.clauses = kept;
        }
        self.watchers = vec![Vec::new(); 2 * self.n_vars as usize];
        let mut idx = 0;
        while idx < self.clauses.len() {
            let len = self.clauses[idx].lits.len();
            if len >= 2 {
                let mut lits = self.clauses[idx].lits.clone();
                // Find up to two literals that are not false under the
                // permanent (level-0) assignment.
                let mut picks: Vec<i32> = Vec::with_capacity(2);
                for &l in lits.iter() {
                    if !self.is_false(l) && !picks.contains(&l) {
                        picks.push(l);
                        if picks.len() == 2 {
                            break;
                        }
                    }
                }
                match picks.len() {
                    0 => return false, // falsified at level 0: immediate UNSAT
                    1 => {
                        // Unit or satisfied-and-permanent: enqueue at level 0
                        // and watch the single literal twice.
                        let u = picks[0];
                        let _ = self.enqueue(u, None);
                        if let Some(p) = lits.iter().position(|&x| x == u) {
                            lits.swap(0, p);
                        }
                        self.clauses[idx].lits = lits;
                        let code = self.lit_code(u);
                        self.watchers[code].push(Watcher {
                            clause: idx,
                            blocking: u,
                        });
                        self.watchers[code].push(Watcher {
                            clause: idx,
                            blocking: u,
                        });
                    }
                    _ => {
                        let l0 = picks[0];
                        let l1 = picks[1];
                        if let Some(p0) = lits.iter().position(|&x| x == l0) {
                            lits.swap(0, p0);
                        }
                        let mut p1 = lits.iter().position(|&x| x == l1).unwrap_or(1);
                        if p1 == 0 {
                            p1 = 1;
                        }
                        lits.swap(1, p1);
                        self.clauses[idx].lits = lits;
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
                    }
                }
            } else if len == 1 {
                let _ = self.enqueue(self.clauses[idx].lits[0], None);
            }
            idx += 1;
        }
        true
    }

    /// Backtrack to level 0, age activities, and prune learnt clauses.
    /// Returns `false` when the prune reveals a level-0 falsified clause.
    fn restart(&mut self) -> bool {
        self.cancel_until(0);
        self.restart_limit = ((self.restart_limit as f64) * 1.5) as u32 + 1;
        let mut i = 0;
        while i < self.activity.len() {
            self.activity[i] *= 0.95;
            i += 1;
        }
        self.reduce_db()
    }

    fn search(&mut self) -> SolveResult {
        loop {
            // The cancel check is cooperative and cheap (a single `Relaxed`
            // load): a portfolio caller that already has a checker-accepted
            // answer from another worker uses it to stop this one promptly,
            // rather than waiting for its own fuel to run out.
            if !self.fuel.burn_one() || self.cancel.is_set() {
                return SolveResult::Unknown;
            }
            match self.propagate() {
                Prop::Ok => {
                    if self.unassigned == 0 {
                        return SolveResult::Sat;
                    }
                    if self.conflicts >= self.restart_limit && !self.restart() {
                        self.proof.push(Vec::new());
                        return SolveResult::Unsat;
                    }
                    self.decide();
                }
                Prop::Conflict(c) => {
                    self.conflicts += 1;
                    if self.decision_level() == 0 {
                        self.proof.push(Vec::new());
                        return SolveResult::Unsat;
                    }
                    let (learnt, btlevel) = self.analyze(c);
                    if learnt.is_empty() {
                        // An empty learnt means a top-level contradiction: a
                        // genuine UNSAT (the original BAIL-here recovery looped).
                        self.proof.push(Vec::new());
                        return SolveResult::Unsat;
                    } else {
                        self.cancel_until(btlevel);
                        if !self.add_learnt(&learnt) {
                            // The learnt clause is already falsified: a
                            // level-0 contradiction derived from the original
                            // clauses.
                            self.proof.push(Vec::new());
                            return SolveResult::Unsat;
                        }
                    }
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
    solve_cnf_worker(n_vars, clauses, fuel, 0, Cancel::none())
}

/// A single portfolio worker's solve: like [`solve_cnf`], but `seed`
/// decorrelates this worker's initial branching polarity from the others
/// racing the same problem, and `cancel` lets any of them stop this one early
/// once a winner has been found (checked cooperatively once per search step —
/// see [`Cancel`]). `seed == 0` with `Cancel::none()` reproduces `solve_cnf`
/// exactly, which is how `solve_cnf` is implemented in terms of this.
pub fn solve_cnf_worker(
    n_vars: u32,
    clauses: &[Vec<i32>],
    fuel: u64,
    seed: u64,
    cancel: Cancel,
) -> SatAnswer {
    let mut s = CdclSolver::new(n_vars, Fuel::new(fuel), seed, cancel);
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
#[allow(clippy::unwrap_used, clippy::panic)]
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

    #[test]
    fn solve_cnf_agrees_with_brute_force() {
        // Trusted oracle: exhaustive SAT check vs the CDCL engine on tiny CNFs.
        // Catches soundness AND completeness bugs in analyse/propagate/learn.
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
        let mut rng = Lcg(0x1234_5678);
        let brute = |n: u32, cls: &[Vec<i32>]| -> bool {
            let total = 1u32 << n;
            let mut a = 0u32;
            while a < total {
                let mut ok = true;
                for c in cls {
                    let mut sat = false;
                    for &l in c {
                        let v = l.unsigned_abs() - 1;
                        let bit = (a >> v) & 1 == 1;
                        let lit = if l > 0 { bit } else { !bit };
                        if lit {
                            sat = true;
                            break;
                        }
                    }
                    if !sat {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    return true;
                }
                a += 1;
            }
            false
        };
        for _ in 0..4000u32 {
            let n = 1 + rng.below(7) as u32; // 1..7 vars
            let nclauses = 1 + rng.below(6) as u32;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..nclauses {
                let len = 1 + rng.below(3) as u32; // 1..3 literals
                let mut c: Vec<i32> = Vec::new();
                for _ in 0..len {
                    let v = 1 + rng.below(n as u64) as i32;
                    let sign = if rng.below(2) == 0 { 1 } else { -1 };
                    c.push(sign * v);
                }
                cls.push(c);
            }
            let sat = brute(n, &cls);
            let ans = solve_cnf(n, &cls, 1_000_000);
            match (sat, ans.result) {
                (true, SolveResult::Sat) => {
                    // model must satisfy every clause
                    let m = ans.model.unwrap();
                    for c in &cls {
                        let mut ok = false;
                        for &l in c {
                            let v = (l.unsigned_abs() as usize) - 1;
                            if (l > 0 && m[v]) || (l < 0 && !m[v]) {
                                ok = true;
                                break;
                            }
                        }
                        assert!(ok, "engine SAT model violates clause {:?} in {:?}", c, cls);
                    }
                }
                (true, SolveResult::Unsat) => {
                    panic!("engine claimed UNSAT but formula is SAT: {:?}", cls);
                }
                (false, SolveResult::Sat) => {
                    panic!("engine claimed SAT but formula is UNSAT: {:?}", cls);
                }
                (false, SolveResult::Unsat) => {}
                (_, SolveResult::Unknown) => {
                    panic!("engine gave Unknown on tiny formula (bug): {:?}", cls);
                }
            }
        }
    }
}
