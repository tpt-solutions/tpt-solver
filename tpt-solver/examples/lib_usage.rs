//! Example: using tpt-solver as a library rather than through the CLI.
//!
//! Every answer is revalidated by the trusted checker kernel exactly as the CLI
//! does — the `verdict` returned alongside each `claim` is what actually may be
//! trusted (`Accept`, `Reject`, or `Inconclusive`; see `tpt_solver_check::outcome`).
//!
//! Run with `cargo run --example lib_usage`.

use tpt_solver::core::lra::LinConstraint;
use tpt_solver::core::rational::Rational;
use tpt_solver::reference::{solve_and_check_cdcl, solve_and_check_lra_with_cert, Problem};

fn main() {
    sat_example();
    lra_example();
}

/// Build a tiny CNF in memory (no DIMACS file needed) and solve it with the
/// certified CDCL engine: `(x1 or x2) and (not x1 or x3) and (not x2 or x3) and
/// (not x3)` is UNSAT (`x3` is forced false, then both `x1` and `x2` are forced
/// true, contradicting the first clause once `x3` is false).
fn sat_example() {
    let problem = Problem {
        var_count: 3,
        clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]],
    };
    let (claim, verdict) = solve_and_check_cdcl(&problem, 1_000_000);
    println!("SAT example: claim = {:?}, checker = {:?}", claim, verdict);
    assert!(
        verdict.is_accept(),
        "the trusted checker did not accept the engine's answer"
    );
}

/// Build a tiny infeasible linear system in memory (`x >= 1` and `x <= 0`) and
/// solve it via Fourier-Motzkin, inspecting the Farkas certificate that proves
/// UNSAT. Every `LinConstraint` is `coeffs · vars <= rhs`, so `x >= 1` is
/// entered as `-x <= -1`.
fn lra_example() {
    let one = Rational::from_i64(1);
    let neg_one = Rational::from_i64(-1);
    let zero = Rational::zero();
    let constraints = vec![
        LinConstraint {
            coeffs: vec![neg_one],
            rhs: neg_one,
        },
        LinConstraint {
            coeffs: vec![one],
            rhs: zero,
        },
    ];
    let (claim, verdict, cert) = solve_and_check_lra_with_cert(&constraints, 1_000_000);
    println!("LRA example: claim = {:?}, checker = {:?}", claim, verdict);
    if let Some(cert) = cert {
        println!(
            "Farkas multipliers (one per constraint above): {:?}",
            cert.multipliers
        );
    }
    assert!(
        verdict.is_accept(),
        "the trusted checker did not accept the engine's answer"
    );
}
