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
use tpt_solver::reference::{solve_and_check, solve_and_check_cdcl, solve_and_check_lra, Problem};
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
            // Not linear arithmetic; try the propositional path.
        }
        Err(e) => {
            eprintln!("error: LRA lowering failed: {}", e);
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
