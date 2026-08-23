//! `tpt-solver` binary: end-to-end demonstration of the certificate architecture.
//!
//! Usage:
//! ```text
//! tpt-solver                 # run built-in demo (reference + CDCL, both certified)
//! tpt-solver FILE.cnf        # parse a DIMACS CNF, solve with CDCL, certify answer
//! tpt-solver FILE.smt2       # parse an SMT-LIB2 script, solve (LRA or SAT), certify
//! tpt-solver FILE.mps        # parse a free-format LP-MPS file, solve the LRA
//!                             # feasibility system (no objective optimization), certify
//! tpt-solver FILE.cnf --fuel N
//! ```
//!
//! Every answer is revalidated by the trusted checker (`tpt-solver-check`); the
//! printed verdict is what may actually be trusted. A richer CLI (`clap`) arrives
//! in a later phase.

use tpt_solver::parsers::dimacs::parse_dimacs;
use tpt_solver::parsers::mps::parse_mps;
use tpt_solver::parsers::smtlib2::{parse_script, LraProblem, SmtError};
use tpt_solver::reference::{
    solve_and_check, solve_and_check_arrays, solve_and_check_bv, solve_and_check_cdcl,
    solve_and_check_lra, Problem,
};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut path: Option<&str> = None;
    let mut fuel: u64 = 10_000_000;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--fuel" => {
                if let Some(next) = args.get(i + 1) {
                    if let Ok(f) = next.parse() {
                        fuel = f;
                    }
                }
                i += 2;
            }
            "--bench" => {
                run_bench();
                return;
            }
            other => {
                if path.is_none() && !other.starts_with('-') {
                    path = Some(other);
                }
                i += 1;
            }
        }
    }

    match path {
        Some(p) => run_file(p, fuel),
        None => run_demo(),
    }
}

fn run_file(path: &str, fuel: u64) {
    if path.ends_with(".smt2") || path.ends_with(".smt") {
        return run_smtlib2(path, fuel);
    }
    if path.ends_with(".mps") {
        return run_mps(path, fuel);
    }
    run_dimacs(path, fuel);
}

fn run_mps(path: &str, fuel: u64) {
    let input = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    let prob: LraProblem = match parse_mps(&input) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: failed to parse '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    println!(
        "parsed MPS: {} vars, {} constraints",
        prob.var_count(),
        prob.constraints.len()
    );
    let (claim, verdict) = solve_and_check_lra(&prob.constraints, fuel);
    print_verdict("LRA engine", claim, verdict);
    if claim == SolveResult::Sat {
        let model = extract_lra_model(&prob.constraints);
        println!(
            "model: {:?}",
            prob.vars.iter().zip(&model).collect::<Vec<_>>()
        );
    }
}

fn run_dimacs(path: &str, fuel: u64) {
    let input = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    let problem = match parse_dimacs(&input) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: failed to parse '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    println!(
        "parsed: {} variables, {} clauses",
        problem.var_count,
        problem.clauses.len()
    );

    let (claim, verdict) = solve_and_check_cdcl(&problem, fuel);
    print_verdict("CDCL engine", claim, verdict);

    if claim == SolveResult::Sat {
        if let Some(model) = solve_model(&problem, fuel) {
            println!(
                "model (x1..x10 shown): {:?}",
                &model[..core::cmp::min(10, model.len())]
            );
        }
    }
}

fn run_smtlib2(path: &str, fuel: u64) {
    let input = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    let script = match parse_script(&input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: failed to parse '{}': {}", path, e);
            std::process::exit(2);
        }
    };
    println!(
        "parsed SMT-LIB2: logic={:?}, {} decls, {} asserts",
        script.logic,
        script.decl_count(),
        script.assert_count()
    );

    // Prefer the LRA path (linear arithmetic); fall back to propositional SAT.
    match script.to_lra() {
        Ok(prob) => {
            println!("lowering: QF_LRA ({} vars)", prob.var_count());
            let (claim, verdict) = solve_and_check_lra(&prob.constraints, fuel);
            print_verdict("LRA engine", claim, verdict);
            if claim == SolveResult::Sat {
                let model = extract_lra_model(&prob.constraints);
                println!(
                    "model: {:?}",
                    prob.vars.iter().zip(&model).collect::<Vec<_>>()
                );
            }
            return;
        }
        Err(SmtError::Unsupported(_)) => {
            // Not linear arithmetic; try the bit-vector path.
        }
        Err(e) => {
            eprintln!("error: LRA lowering failed: {}", e);
            std::process::exit(2);
        }
    }

    match script.to_bv() {
        Ok(prob) => {
            println!("lowering: QF_BV ({} vars)", prob.names.len());
            let (claim, verdict) = solve_and_check_bv(prob.var_count, &prob.assertions, fuel);
            print_verdict("BV engine", claim, verdict);
            if claim == SolveResult::Sat {
                // Deterministic engine: re-solving yields the same model.
                if let Some(tpt_solver_core::bv::BvOutcome::Sat(model)) =
                    tpt_solver_core::bv::solve_bv(prob.var_count, &prob.assertions, fuel)
                {
                    println!(
                        "model: {:?}",
                        prob.names.iter().zip(&model.values).collect::<Vec<_>>()
                    );
                }
            }
            return;
        }
        Err(SmtError::Unsupported(_)) => {
            // Not bit-vector; try the array path.
        }
        Err(e) => {
            eprintln!("error: BV lowering failed: {}", e);
            std::process::exit(2);
        }
    }

    match script.to_array() {
        Ok(prob) => {
            println!(
                "lowering: QF_AX ({} arrays, {} elements)",
                prob.avars.len(),
                prob.evars.len()
            );
            let (claim, verdict) = solve_and_check_arrays(
                prob.avars.len() as u32,
                prob.evars.len() as u32,
                &prob.assertions,
                fuel,
            );
            print_verdict("AX engine", claim, verdict);
            return;
        }
        Err(SmtError::Unsupported(_)) => {
            // Not arrays; try the propositional path.
        }
        Err(e) => {
            eprintln!("error: array lowering failed: {}", e);
            std::process::exit(2);
        }
    }

    let problem = match script.to_cnf() {
        Ok(p) => p,
        Err(e) => {
            eprintln!(
                "error: could not lower script ({}); only QF_LRA and QF_SAT subsets are supported",
                e
            );
            std::process::exit(2);
        }
    };
    println!(
        "lowering: QF_SAT ({} vars, {} clauses)",
        problem.var_count,
        problem.clauses.len()
    );
    let (claim, verdict) = solve_and_check_cdcl(&problem, fuel);
    print_verdict("CDCL engine", claim, verdict);
}

/// Best-effort extraction of an LRA model for display (re-uses the core's Simplex).
fn extract_lra_model(
    constraints: &[tpt_solver_core::lra::LinConstraint],
) -> Vec<tpt_solver_core::rational::Rational> {
    match tpt_solver_core::lra::lra_model(constraints) {
        Some(Some(m)) => m,
        _ => Vec::new(),
    }
}

fn solve_model(problem: &Problem, fuel: u64) -> Option<Vec<bool>> {
    let ans = tpt_solver_core::sat::solve_cnf(problem.var_count, &problem.clauses, fuel);
    ans.model
}

/// Local performance harness: a deterministic random 3-SAT ladder around the
/// phase transition, run through the full certified CDCL pipeline.
///
/// This is the offline scaffolding for the SAT-COMP/SMT-COMP benchmark item —
/// real competition runs additionally need the official corpora and hardware,
/// but this ladder catches gross performance regressions in CI-sized time.
fn run_bench() {
    use std::time::Instant;
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        fn below(&mut self, n: u32) -> u32 {
            (self.next() % n as u64) as u32
        }
    }

    println!("bench: random 3-SAT ladder, certified CDCL pipeline (5 seeds each)");
    println!(
        "{:>6} {:>8} {:>12} {:>7}",
        "vars", "clauses", "mean_ms", "sat%"
    );
    for &n in &[100usize, 200, 300, 400, 500] {
        let m = ((n as f64) * 4.26).round() as usize; // near the phase transition
        let mut total_us = 0u128;
        let mut sat_count = 0u32;
        let runs = 5u32;
        for seed in 0..runs {
            let mut rng = Lcg(0xBADC0DE ^ (n as u64) ^ ((seed as u64) * 7_919));
            let mut clauses: Vec<Vec<i32>> = Vec::with_capacity(m);
            for _ in 0..m {
                let mut c = Vec::with_capacity(3);
                for _ in 0..3 {
                    let v = 1 + rng.below(n as u32);
                    let sign: i32 = if rng.below(2) == 0 { 1 } else { -1 };
                    c.push(sign * v as i32);
                }
                clauses.push(c);
            }
            let problem = Problem {
                var_count: n as u32,
                clauses,
            };
            let start = Instant::now();
            let (claim, _verdict, _dump) =
                tpt_solver::policy::solve_certified(&problem, 50_000_000);
            total_us += start.elapsed().as_micros();
            if claim == SolveResult::Sat {
                sat_count += 1;
            }
        }
        println!(
            "{:>6} {:>8} {:>12.1} {:>6.0}%",
            n,
            m,
            total_us as f64 / runs as f64 / 1000.0,
            100.0 * sat_count as f64 / runs as f64
        );
    }
}

fn run_demo() {
    let sat_problem = Problem {
        var_count: 2,
        clauses: vec![vec![1], vec![2]],
    };
    let unsat_problem = Problem {
        var_count: 3,
        clauses: vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]],
    };

    demo("reference DPLL", solve_and_check(&sat_problem, fuel_demo()));
    demo(
        "reference DPLL",
        solve_and_check(&unsat_problem, fuel_demo()),
    );
    demo(
        "CDCL engine",
        solve_and_check_cdcl(&sat_problem, fuel_demo()),
    );
    demo(
        "CDCL engine",
        solve_and_check_cdcl(&unsat_problem, fuel_demo()),
    );
}

#[inline]
fn fuel_demo() -> u64 {
    1_000_000
}

fn demo(label: &str, (claim, verdict): (SolveResult, Outcome)) {
    println!(
        "[{:>15}] claim = {:?}, checker = {:?}",
        label, claim, verdict
    );
    print_verdict_tail(claim, verdict);
}

fn print_verdict(label: &str, claim: SolveResult, verdict: Outcome) {
    println!(
        "[{:>15}] claim = {:?}, checker = {:?}",
        label, claim, verdict
    );
    print_verdict_tail(claim, verdict);
}

fn print_verdict_tail(claim: SolveResult, verdict: Outcome) {
    match claim {
        SolveResult::Sat => {
            if verdict.is_accept() {
                println!("                 OK: model verified by the trusted kernel.");
            } else {
                println!("                 WARN: checker did not Accept the SAT model.");
            }
        }
        SolveResult::Unsat => {
            if verdict.is_accept() {
                println!("                 OK: UNSAT proof verified by the trusted kernel.");
            } else {
                println!("                 WARN: checker did not Accept the UNSAT proof.");
            }
        }
        SolveResult::Unknown => {
            println!("                 engine returned Unknown (honest last resort).");
        }
    }
}
