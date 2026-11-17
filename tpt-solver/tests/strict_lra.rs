//! Strict inequalities in QF_LRA are exact end to end: parser, Fourier–Motzkin
//! prover, simplex model search, and the trusted checker.
//!
//! Regression cases for the bug where `<` and `>` were approximated by `<=` and
//! `>=`. That made `x >= 1 && x < 1` SAT with the model `x = 1`, and the checker
//! accepted the model.

use tpt_solver::api::{solve_str, Format, Model, Options};
use tpt_solver::check::outcome::Outcome;
use tpt_solver::core::engine::SolveResult;

fn run(body: &str) -> tpt_solver::api::Report {
    let script = format!("(set-logic QF_LRA)\n(declare-const x Real)\n{body}\n(check-sat)\n");
    solve_str(&script, Format::SmtLib2, &Options::default()).expect("solve")
}

fn model_value(report: &tpt_solver::api::Report, name: &str) -> String {
    match &report.model {
        Some(Model::Named(v)) => v
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, val)| val.clone())
            .unwrap_or_else(|| panic!("no value for {name}")),
        other => panic!("expected a named model, got {other:?}"),
    }
}

#[test]
fn strict_lower_bound_meeting_equal_upper_bound_is_unsat() {
    let r = run("(assert (>= x 1.0))\n(assert (< x 1.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn strict_upper_bound_meeting_equal_lower_bound_is_unsat() {
    let r = run("(assert (< x 1.0))\n(assert (>= x 1.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn strict_greater_meeting_equal_bound_is_unsat() {
    let r = run("(assert (> x 1.0))\n(assert (<= x 1.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn negated_non_strict_is_strict_and_unsat_at_the_boundary() {
    // not (x <= 1) means x > 1, which contradicts x <= 1.
    let r = run("(assert (not (<= x 1.0)))\n(assert (<= x 1.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn negated_strict_is_non_strict() {
    // not (x < 1) means x >= 1, which is satisfied by x = 1.
    let r = run("(assert (not (< x 1.0)))\n(assert (<= x 1.0))");
    assert_eq!(r.claim, SolveResult::Sat);
    assert_eq!(r.verdict, Outcome::Accept);
    assert_eq!(model_value(&r, "x"), "1");
}

#[test]
fn strict_bounds_with_room_are_sat_and_model_is_strictly_inside() {
    let r = run("(assert (< x 2.0))\n(assert (>= x 1.5))");
    assert_eq!(r.claim, SolveResult::Sat);
    assert_eq!(r.verdict, Outcome::Accept);
    let v = model_value(&r, "x");
    // The model must satisfy the strict bound: a value of 2 would not.
    let parsed = match v.split_once('/') {
        Some((n, d)) => n.parse::<f64>().unwrap() / d.parse::<f64>().unwrap(),
        None => v.parse::<f64>().unwrap(),
    };
    assert!(parsed >= 1.5 && parsed < 2.0, "model x = {v}");
}

#[test]
fn strict_open_interval_with_tight_point_is_sat_only_inside() {
    // 0 < x < 1e-6 (open) has a model, and the simplex must find one strictly inside.
    let r = run("(assert (> x 0.0))\n(assert (< x 0.000001))");
    assert_eq!(r.claim, SolveResult::Sat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn empty_open_interval_is_unsat() {
    let r = run("(assert (> x 1.0))\n(assert (< x 1.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
}

#[test]
fn non_strict_problems_are_unaffected() {
    let r = run("(assert (>= x 1.0))\n(assert (<= x 0.0))");
    assert_eq!(r.claim, SolveResult::Unsat);
    assert_eq!(r.verdict, Outcome::Accept);
    let r = run("(assert (>= x 1.0))\n(assert (<= x 1.0))");
    assert_eq!(r.claim, SolveResult::Sat);
    assert_eq!(r.verdict, Outcome::Accept);
}
