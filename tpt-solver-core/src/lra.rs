//! QF_LRA linear constraints and a Fourier–Motzkin UNSAT prover.
//!
//! The prover eliminates variables one at a time; every derived constraint is a
//! *nonnegative* combination of the originals, so when elimination reaches a
//! contradiction (`0 <= negative`) the accumulated multiplier vector is a valid
//! **Farkas certificate** — exactly what [`tpt_solver_check::lra::check_farkas`]
//! re-validates. This is the LRA counterpart of the SAT RUP proof: the kernel never
//! trusts the engine, it re-derives.

use crate::rational::Rational;
use alloc::vec::Vec;

/// A linear constraint in canonical `<=` form: `Σ coeffs[i]·x_i <= rhs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinConstraint {
    /// Coefficient of each variable, in a fixed variable order shared by every
    /// constraint in the system.
    pub coeffs: Vec<Rational>,
    /// The right-hand side of the `<=` bound.
    pub rhs: Rational,
}

/// A Farkas certificate: nonnegative multipliers, one per original constraint, whose
/// weighted sum of the constraints yields a direct contradiction (`0 <= negative`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FarkasCertificate {
    /// One nonnegative multiplier per original constraint, in input order.
    pub multipliers: Vec<Rational>,
}

/// Result of the UNSAT search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FmResult {
    /// The system is feasible (no contradiction found).
    Sat,
    /// The system is infeasible; the certificate proves it.
    Unsat(FarkasCertificate),
}

#[derive(Clone, Debug)]
struct Internal {
    coeffs: Vec<Rational>,
    rhs: Rational,
    /// Accreted multipliers over the *original* constraints.
    mult: Vec<Rational>,
}

/// Run Fourier–Motzkin elimination.
///
/// Returns [`FmResult::Unsat`] with a Farkas certificate when a contradiction is
/// found, otherwise [`FmResult::Sat`]. Returns `None` if exact arithmetic overflows
/// (caller should treat as "could not decide", never as a sound answer).
#[allow(clippy::needless_range_loop)]
pub fn fourier_motzkin(input: &[LinConstraint]) -> Option<FmResult> {
    if input.is_empty() {
        return Some(FmResult::Sat);
    }
    let n = input[0].coeffs.len();
    let mut cons: Vec<Internal> = input
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let mut mult = vec![Rational::zero(); input.len()];
            mult[i] = Rational::from_i64(1);
            Internal {
                coeffs: c.coeffs.clone(),
                rhs: c.rhs,
                mult,
            }
        })
        .collect();

    for k in 0..n {
        let mut next: Vec<Internal> = Vec::new();
        // Constraints not involving x_k are carried forward unchanged.
        for c in &cons {
            if c.coeffs[k].is_zero() {
                next.push(c.clone());
            }
        }
        // Combine each upper bound (coeff > 0) with each lower bound (coeff < 0).
        for ui in &cons {
            if ui.coeffs[k].is_negative() {
                continue;
            }
            for lj in &cons {
                if !lj.coeffs[k].is_negative() {
                    continue;
                }
                // m1 = -coeff(lj) > 0, m2 = coeff(ui) > 0.
                let m1 = lj.coeffs[k].neg();
                let m2 = ui.coeffs[k];
                let mut nc = vec![Rational::zero(); n];
                let nrhs = ui.rhs.mul(m1)?.add(lj.rhs.mul(m2)?)?;
                let mut nmult = vec![Rational::zero(); input.len()];
                for j in 0..n {
                    if j == k {
                        continue;
                    }
                    nc[j] = ui.coeffs[j].mul(m1)?.add(lj.coeffs[j].mul(m2)?)?;
                }
                for j in 0..input.len() {
                    nmult[j] = ui.mult[j].mul(m1)?.add(lj.mult[j].mul(m2)?)?;
                }
                next.push(Internal {
                    coeffs: nc,
                    rhs: nrhs,
                    mult: nmult,
                });
            }
        }
        cons = next;
    }

    for c in &cons {
        if c.coeffs.iter().all(|x| x.is_zero()) && c.rhs.is_negative() {
            return Some(FmResult::Unsat(FarkasCertificate {
                multipliers: c.mult.clone(),
            }));
        }
    }
    Some(FmResult::Sat)
}

/// A Simplex tableau for QF_LRA feasibility (all variables treated as non-negative
/// via the `x = x⁺ − x⁻` difference trick) with a two-phase start.
///
/// The prover's job here is narrow: *given* that Fourier–Motzkin already decided the
/// system is feasible, find one concrete satisfying assignment. That assignment is
/// never trusted — [`tpt_solver_check::lra::check_lra_model`] re-substitutes it into
/// the original constraints and rejects any that don't actually hold. So an imperfect
/// Simplex only ever degrades a SAT answer to `Inconclusive`, never to a wrong
/// `Accept`.
struct Tableau {
    /// `rows[i][c]` is the coefficient of column `c`; `rows[i][ncols]` is the RHS.
    rows: Vec<Vec<Rational>>,
    /// `basis[i]` is the column index basic in row `i`.
    basis: Vec<usize>,
    /// Column index of each original variable's `+`/`−` halves, the slacks, and the
    /// artificials, packed into one contiguous range.
    n_vars: usize,
    n_constraints: usize,
    n_struct: usize,
    art_start: usize,
    ncols: usize,
}

impl Tableau {
    fn build(constraints: &[LinConstraint]) -> Option<Tableau> {
        if constraints.is_empty() {
            return None;
        }
        let n = constraints[0].coeffs.len();
        let m = constraints.len();
        let n_struct = 2 * n;
        let art_start = n_struct + m;
        let ncols = n_struct + m + m; // x⁺, x⁻, slack, artificial(per row)

        let mut rows: Vec<Vec<Rational>> = Vec::with_capacity(m);
        let mut basis: Vec<usize> = Vec::with_capacity(m);
        for (i, c) in constraints.iter().enumerate() {
            let mut row = vec![Rational::zero(); ncols + 1];
            if c.coeffs.len() != n {
                return None;
            }
            for (j, coeff) in c.coeffs.iter().enumerate() {
                row[j] = *coeff;
                row[n + j] = coeff.neg();
            }
            row[n_struct + i] = Rational::from_i64(1);
            let mut rhs = c.rhs;
            if rhs.is_negative() {
                for cell in row[..ncols].iter_mut() {
                    *cell = cell.neg();
                }
                rhs = rhs.neg();
                row[art_start + i] = Rational::from_i64(1);
                basis.push(art_start + i);
            } else {
                basis.push(n_struct + i);
            }
            row[ncols] = rhs;
            rows.push(row);
        }

        Some(Tableau {
            rows,
            basis,
            n_vars: n,
            n_constraints: m,
            n_struct,
            art_start,
            ncols,
        })
    }

    /// Phase-1 objective row: the sum of the artificial columns. Returned as a row in
    /// the same shape as `rows` (`len == ncols + 1`).
    #[allow(clippy::needless_range_loop)]
    fn phase1_objective(&self) -> Option<Vec<Rational>> {
        let mut obj = vec![Rational::zero(); self.ncols + 1];
        for (i, &b) in self.basis.iter().enumerate() {
            if b >= self.art_start {
                for c in 0..=self.ncols {
                    obj[c] = obj[c].add(self.rows[i][c])?;
                }
            }
        }
        Some(obj)
    }

    /// Run two-phase Simplex. Returns `Some(Some(model))` on feasibility (model is the
    /// value of each original variable), `Some(None)` if infeasible, and `None` on
    /// exact-arithmetic overflow / resource exhaustion (treated as "could not decide").
    #[allow(clippy::needless_range_loop)]
    fn solve(&mut self, max_iter: u64) -> Option<Option<Vec<Rational>>> {
        let mut obj = self.phase1_objective()?;
        let mut iter = 0u64;
        // Phase 1: drive the sum of artificials to zero.
        loop {
            if iter >= max_iter {
                return None;
            }
            iter += 1;
            // Entering column: a nonbasic column whose reduced cost is negative (i.e.
            // `obj[c] > 0` in our `z = obj_rhs - Σ obj[c]·x_c` tableau), so increasing it
            // lowers the phase-1 objective (the sum of artificials). It must also have
            // a positive pivot to keep the basis feasible.
            //
            // Artificial columns are excluded here: `obj[c]` is only a valid reduced
            // cost for columns with true phase-1 cost 0 (`c_j - z_j = -z_j = obj[c]`).
            // Artificials have cost 1, so their real reduced cost is `1 - obj[c]`, not
            // `obj[c]` — treating them the same way would let a nonbasic artificial
            // with `0 < obj[c] <= 1` look "improving" and re-enter the basis, which
            // only reintroduces infeasibility it already left. Once an original
            // constraint's artificial has been driven out, it should never come back.
            let mut entering: Option<usize> = None;
            let mut best = Rational::zero();
            for c in 0..self.art_start {
                if self.basis.contains(&c) {
                    continue;
                }
                if !obj[c].is_positive() {
                    continue;
                }
                let has_positive_pivot =
                    (0..self.n_constraints).any(|p| self.rows[p][c].is_positive());
                if !has_positive_pivot {
                    continue;
                }
                if entering.is_none() || obj[c].cmp(best) == core::cmp::Ordering::Greater {
                    best = obj[c];
                    entering = Some(c);
                }
            }
            let q = match entering {
                Some(c) => c,
                None => {
                    // No pivotable improving column. If any improving column exists at
                    // all the objective is unbounded below => infeasible; otherwise we
                    // have reached optimality.
                    let unbounded = (0..self.art_start)
                        .any(|c| !self.basis.contains(&c) && obj[c].is_positive());
                    if unbounded {
                        return Some(None);
                    }
                    break;
                }
            };
            // Ratio test: minimize rhs[p] / rows[p][q] over rows with positive pivot.
            let mut leaving: Option<usize> = None;
            let mut best_ratio: Option<Rational> = None;
            for p in 0..self.n_constraints {
                let piv = self.rows[p][q];
                if piv.is_negative() {
                    continue;
                }
                if piv.is_zero() {
                    continue;
                }
                let ratio = self.rows[p][self.ncols].checked_div(piv)?;
                match best_ratio {
                    None => {
                        best_ratio = Some(ratio);
                        leaving = Some(p);
                    }
                    Some(br) => {
                        if ratio.cmp(br) == core::cmp::Ordering::Less {
                            best_ratio = Some(ratio);
                            leaving = Some(p);
                        }
                    }
                }
            }
            let p = match leaving {
                Some(p) => p,
                None => return Some(None), // unbounded below => infeasible
            };
            self.pivot(p, q, &mut obj)?;
        }

        // Feasibility: sum of artificials must be exactly zero.
        if !obj[self.ncols].is_zero() {
            return Some(None);
        }

        // Read off a feasible assignment: basic vars take their row RHS, non-basic
        // structural vars are zero (their lower bound).
        let mut values = vec![Rational::zero(); self.n_struct];
        for (i, &b) in self.basis.iter().enumerate() {
            if b < self.n_struct {
                values[b] = self.rows[i][self.ncols];
            }
        }
        let mut model = Vec::with_capacity(self.n_vars);
        for j in 0..self.n_vars {
            let pos = values[j];
            let neg = values[self.n_vars + j];
            model.push(pos.add(neg.neg())?);
        }
        Some(Some(model))
    }

    /// Pivot row `p` so that column `q` becomes basic, updating `obj` as a normal row.
    #[allow(clippy::needless_range_loop)]
    fn pivot(&mut self, p: usize, q: usize, obj: &mut [Rational]) -> Option<()> {
        let pivot_val = self.rows[p][q];
        if pivot_val.is_zero() {
            return None;
        }
        // Normalize the pivot row.
        for c in 0..=self.ncols {
            self.rows[p][c] = self.rows[p][c].checked_div(pivot_val)?;
        }
        let pivot_row = self.rows[p].clone();
        // Zero out column `q` in every other row (including the objective).
        for r in 0..self.n_constraints {
            if r == p {
                continue;
            }
            let factor = self.rows[r][q];
            if factor.is_zero() {
                continue;
            }
            for c in 0..=self.ncols {
                let term = pivot_row[c].mul(factor)?;
                self.rows[r][c] = self.rows[r][c].add(term.neg())?;
            }
        }
        let obj_factor = obj[q];
        if !obj_factor.is_zero() {
            for c in 0..=self.ncols {
                let term = pivot_row[c].mul(obj_factor)?;
                obj[c] = obj[c].add(term.neg())?;
            }
        }
        self.basis[p] = q;
        Some(())
    }
}

/// Find one satisfying assignment for a feasible QF_LRA system (given in `<=` form).
///
/// Returns:
/// * `Some(Some(model))` — a model (one value per original variable) that the caller
///   should revalidate with [`tpt_solver_check::lra::check_lra_model`].
/// * `Some(None)` — the system is infeasible (no model exists).
/// * `None` — exact arithmetic overflowed or iteration budget was exhausted; treated
///   as "could not decide", never as a sound answer.
pub fn lra_model(constraints: &[LinConstraint]) -> Option<Option<Vec<Rational>>> {
    if constraints.is_empty() {
        // Vacuously feasible: the empty assignment satisfies the empty system.
        return Some(Some(Vec::new()));
    }
    let mut tab = Tableau::build(constraints)?;
    // Iteration ceiling scales with problem size; this is a *decision* budget, not a
    // soundness bound — exhausting it only yields `None`.
    let max_iter = (tab.ncols as u64 + 1) * (tab.n_constraints as u64 + 1) * 100;
    tab.solve(max_iter)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;

    fn c(coeffs: &[i64], rhs: i64) -> LinConstraint {
        LinConstraint {
            coeffs: coeffs.iter().map(|&x| Rational::from_i64(x)).collect(),
            rhs: Rational::from_i64(rhs),
        }
    }

    #[test]
    fn unsat_x_ge_1_and_x_le_0() {
        // x >= 1  =>  -x <= -1 ;  x <= 0  =>  x <= 0
        let cons = vec![c(&[-1], -1), c(&[1], 0)];
        match fourier_motzkin(&cons) {
            Some(FmResult::Unsat(cert)) => {
                // certificate should be [1, 1]: 1*(x>=1) + 1*(x<=0) => 0 <= -1
                assert_eq!(
                    cert.multipliers,
                    vec![Rational::from_i64(1), Rational::from_i64(1)]
                );
            }
            other => panic!("expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn sat_simple_feasible() {
        // x <= 5, x >= 0
        let cons = vec![c(&[1], 5), c(&[-1], 0)];
        assert_eq!(fourier_motzkin(&cons), Some(FmResult::Sat));
    }

    #[test]
    fn unsat_two_var_chain() {
        // x <= y, y <= z, z <= x - 1  => infeasible
        let cons = vec![c(&[1, -1], 0), c(&[0, 1, -1], 0), c(&[-1, 0, 1], -1)];
        assert!(matches!(fourier_motzkin(&cons), Some(FmResult::Unsat(_))));
    }

    #[test]
    fn simplex_finds_model_single_var() {
        // x <= 5, x >= 0  => feasible; model should satisfy both.
        let cons = vec![c(&[1], 5), c(&[-1], 0)];
        let model = lra_model(&cons).unwrap().unwrap();
        assert_eq!(model.len(), 1);
        assert!(model[0].cmp(Rational::from_i64(0)) != core::cmp::Ordering::Less);
        assert!(model[0].cmp(Rational::from_i64(5)) != core::cmp::Ordering::Greater);
    }

    #[test]
    fn simplex_finds_model_two_var() {
        // 0 <= x <= 10, 0 <= y <= 10, x + y <= 15
        let cons = vec![
            c(&[1, 0], 10),
            c(&[-1, 0], 0),
            c(&[0, 1], 10),
            c(&[0, -1], 0),
            c(&[1, 1], 15),
        ];
        let model = lra_model(&cons).unwrap().unwrap();
        assert_eq!(model.len(), 2);
        let x = model[0];
        let y = model[1];
        assert!(x.cmp(Rational::from_i64(0)) != core::cmp::Ordering::Less);
        assert!(x.cmp(Rational::from_i64(10)) != core::cmp::Ordering::Greater);
        assert!(y.cmp(Rational::from_i64(0)) != core::cmp::Ordering::Less);
        assert!(y.cmp(Rational::from_i64(10)) != core::cmp::Ordering::Greater);
        assert!(x.add(y).unwrap().cmp(Rational::from_i64(15)) != core::cmp::Ordering::Greater);
    }

    #[test]
    fn simplex_reports_infeasible_when_unsat() {
        // x >= 1 (-x <= -1) and x <= 0  => infeasible
        let cons = vec![c(&[-1], -1), c(&[1], 0)];
        match lra_model(&cons) {
            Some(None) => {} // expected infeasible
            other => panic!("expected Some(None), got {:?}", other),
        }
    }
}
