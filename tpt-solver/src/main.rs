//! `tpt-solver` binary: end-to-end demonstration of the certificate architecture.
//!
//! Usage:
//! ```text
//! tpt-solver                          # run built-in demo (reference + CDCL, both certified)
//! tpt-solver FILE.cnf                  # parse a DIMACS CNF, solve with CDCL, certify answer
//! tpt-solver FILE.smt2                 # parse an SMT-LIB2 script, solve (LRA or SAT), certify
//! tpt-solver FILE.mps                  # parse a free-format LP-MPS file, solve the LRA
//!                                       # feasibility system (no objective optimization), certify
//! tpt-solver FILE.cnf --fuel N
//! tpt-solver FILE.cnf --parallel N     # race N diverse CDCL workers (DIMACS only)
//! tpt-solver FILE.cnf --emit-proof P   # on UNSAT, dump the checked certificate to file P
//! tpt-solver FILE.smt2 --explain       # on UNSAT (LRA only), print the implicated constraints
//! tpt-solver --bench                   # local 3-SAT performance ladder
//! ```
//!
//! Every answer is revalidated by the trusted checker (`tpt-solver-check`); the
//! printed verdict is what may actually be trusted.

use clap::Parser;
use tpt_solver::parsers::dimacs::parse_dimacs;
use tpt_solver::parsers::mps::parse_mps;
use tpt_solver::parsers::smtlib2::{parse_script, LraProblem, SmtError};
use tpt_solver::policy::solve_certified_portfolio;
use tpt_solver::reference::{
    solve_and_check, solve_and_check_arrays, solve_and_check_bv, solve_and_check_cdcl,
    solve_and_check_cdcl_with_proof, solve_and_check_lra_with_cert, Problem,
};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;
use tpt_solver_core::lra::{FarkasCertificate, LinConstraint};

/// tpt-solver: a certificate-architecture SAT/SMT solver suite.
///
/// Every answer this CLI prints is revalidated by the independent trusted checker
/// (`tpt-solver-check`) before being reported; run with no arguments for a built-in
/// demo of that pipeline.
#[derive(Parser)]
#[command(name = "tpt-solver", version, about, long_about = None)]
struct Cli {
    /// Input file: .cnf (DIMACS), .smt2/.smt (SMT-LIB2), or .mps (LP-MPS).
    /// Omit to run the built-in demo.
    path: Option<String>,

    /// Step budget for the engine before giving up with `Unknown`.
    #[arg(long, default_value_t = 10_000_000)]
    fuel: u64,

    /// Race N diverse CDCL workers instead of a single solve (DIMACS only).
    #[arg(long, value_name = "N")]
    parallel: Option<usize>,

    /// Run the local 3-SAT performance ladder instead of solving a file.
    #[arg(long)]
    bench: bool,

    /// On an UNSAT claim, write the checked certificate to FILE: an LRAT-style
    /// clause dump for DIMACS/CNF, or the Farkas multipliers for SMT-LIB2/MPS LRA.
    #[arg(long, value_name = "FILE")]
    emit_proof: Option<String>,

    /// On an UNSAT claim, print the minimal core of original constraints
    /// implicated in the contradiction. LRA only in this release (SMT-LIB2/MPS);
    /// a DIMACS/CNF UNSAT core needs clause-provenance tracking not yet wired in.
    #[arg(long)]
    explain: bool,
}

/// Options threaded through every `run_*` function for a single file solve.
struct RunOpts {
    fuel: u64,
    parallel: Option<usize>,
    emit_proof: Option<String>,
    explain: bool,
}

fn main() {
    let cli = Cli::parse();
    if cli.bench {
        run_bench();
        return;
    }
    let opts = RunOpts {
        fuel: cli.fuel,
        parallel: cli.parallel,
        emit_proof: cli.emit_proof,
        explain: cli.explain,
    };
    match cli.path {
        Some(p) => run_file(&p, &opts),
        None => run_demo(),
    }
}

fn run_file(path: &str, opts: &RunOpts) {
    if path.ends_with(".smt2") || path.ends_with(".smt") {
        return run_smtlib2(path, opts);
    }
    if path.ends_with(".mps") {
        return run_mps(path, opts);
    }
    run_dimacs(path, opts);
}

/// Report the certificate/explain output for an LRA UNSAT claim, shared by the
/// SMT-LIB2 and MPS front ends (both lower to the same `LinConstraint` system).
fn report_lra_unsat(cert: &FarkasCertificate, constraints: &[LinConstraint], opts: &RunOpts) {
    if let Some(path) = &opts.emit_proof {
        write_farkas_cert(path, cert);
    }
    if opts.explain {
        print_lra_explain(cert, constraints);
    }
}

fn run_mps(path: &str, opts: &RunOpts) {
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
    let (claim, verdict, cert) = solve_and_check_lra_with_cert(&prob.constraints, opts.fuel);
    print_verdict("LRA engine", claim, verdict);
    if claim == SolveResult::Sat {
        let model = extract_lra_model(&prob.constraints);
        println!(
            "model: {:?}",
            prob.vars.iter().zip(&model).collect::<Vec<_>>()
        );
    } else if let Some(cert) = &cert {
        report_lra_unsat(cert, &prob.constraints, opts);
    }
}

fn run_dimacs(path: &str, opts: &RunOpts) {
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

    let claim = match opts.parallel {
        Some(workers) => {
            println!("solving with {} racing portfolio workers", workers.max(1));
            let (claim, verdict, dump) = solve_certified_portfolio(&problem, opts.fuel, workers);
            if let Some(d) = dump {
                println!("{}", d.render());
            }
            print_verdict("CDCL engine (portfolio)", claim, verdict);
            if opts.emit_proof.is_some() {
                eprintln!("note: --emit-proof is not supported with --parallel; re-run without --parallel to export a certificate");
            }
            claim
        }
        None => {
            let (claim, verdict, proof) = solve_and_check_cdcl_with_proof(&problem, opts.fuel);
            print_verdict("CDCL engine", claim, verdict);
            if let (Some(path), Some(proof)) = (&opts.emit_proof, &proof) {
                write_lrat_proof(path, proof);
            }
            if opts.explain && claim == SolveResult::Unsat {
                println!("note: --explain is LRA-only in this release; no CNF/SAT UNSAT core is available");
            }
            claim
        }
    };

    if claim == SolveResult::Sat {
        if let Some(model) = solve_model(&problem, opts.fuel) {
            println!(
                "model (x1..x10 shown): {:?}",
                &model[..core::cmp::min(10, model.len())]
            );
        }
    }
}

fn run_smtlib2(path: &str, opts: &RunOpts) {
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
            let (claim, verdict, cert) =
                solve_and_check_lra_with_cert(&prob.constraints, opts.fuel);
            print_verdict("LRA engine", claim, verdict);
            if claim == SolveResult::Sat {
                let model = extract_lra_model(&prob.constraints);
                println!(
                    "model: {:?}",
                    prob.vars.iter().zip(&model).collect::<Vec<_>>()
                );
            } else if let Some(cert) = &cert {
                report_lra_unsat(cert, &prob.constraints, opts);
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
            let (claim, verdict) = solve_and_check_bv(prob.var_count, &prob.assertions, opts.fuel);
            print_verdict("BV engine", claim, verdict);
            if claim == SolveResult::Sat {
                // Deterministic engine: re-solving yields the same model.
                if let Some(tpt_solver_core::bv::BvOutcome::Sat(model)) =
                    tpt_solver_core::bv::solve_bv(prob.var_count, &prob.assertions, opts.fuel)
                {
                    println!(
                        "model: {:?}",
                        prob.names.iter().zip(&model.values).collect::<Vec<_>>()
                    );
                }
            } else if opts.emit_proof.is_some() || opts.explain {
                println!("note: --emit-proof/--explain are not yet supported for QF_BV");
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
                opts.fuel,
            );
            print_verdict("AX engine", claim, verdict);
            if claim == SolveResult::Unsat && (opts.emit_proof.is_some() || opts.explain) {
                println!("note: --emit-proof/--explain are not yet supported for QF_AX");
            }
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
    let (claim, verdict, proof) = solve_and_check_cdcl_with_proof(&problem, opts.fuel);
    print_verdict("CDCL engine", claim, verdict);
    if let (Some(path), Some(proof)) = (&opts.emit_proof, &proof) {
        write_lrat_proof(path, proof);
    }
    if opts.explain && claim == SolveResult::Unsat {
        println!("note: --explain is LRA-only in this release; no CNF/SAT UNSAT core is available");
    }
}

/// Dump a checked [`tpt_solver_check::lrat::LratProof`] as a DRAT-style clause
/// list (one derived clause per line, `0`-terminated, empty line for the final
/// empty clause) so external tools (e.g. `drat-trim`) can independently
/// re-verify the UNSAT claim. Full LRAT hints are not populated by the engine
/// yet, so this is the plain-RUP subset of the format.
fn write_lrat_proof(path: &str, proof: &tpt_solver_check::lrat::LratProof) {
    let mut out = String::new();
    for step in proof.steps() {
        for lit in &step.clause {
            let n = lit.var().get() as i64;
            out.push_str(&(if lit.is_positive() { n } else { -n }).to_string());
            out.push(' ');
        }
        out.push_str("0\n");
    }
    match std::fs::write(path, out) {
        Ok(()) => println!(
            "proof written to '{}' ({} step(s))",
            path,
            proof.steps().len()
        ),
        Err(e) => eprintln!("warning: failed to write proof to '{}': {}", path, e),
    }
}

/// Dump a checked [`FarkasCertificate`] as one `index multiplier` line per
/// original constraint (only nonzero multipliers are listed), so the
/// contradiction `sum(multiplier_i * constraint_i) => 0 <= negative` can be
/// independently re-derived.
fn write_farkas_cert(path: &str, cert: &FarkasCertificate) {
    let mut out = String::from("# Farkas certificate: nonzero (index multiplier) pairs\n");
    for (i, m) in cert.multipliers.iter().enumerate() {
        if !m.is_zero() {
            out.push_str(&format!("{} {:?}\n", i, m));
        }
    }
    match std::fs::write(path, out) {
        Ok(()) => println!("proof written to '{}'", path),
        Err(e) => eprintln!("warning: failed to write proof to '{}': {}", path, e),
    }
}

/// Print the LRA UNSAT core: the original constraints with a nonzero Farkas
/// multiplier, i.e. exactly those that participate in the contradiction.
fn print_lra_explain(cert: &FarkasCertificate, constraints: &[LinConstraint]) {
    let core: Vec<usize> = cert
        .multipliers
        .iter()
        .enumerate()
        .filter(|(_, m)| !m.is_zero())
        .map(|(i, _)| i)
        .collect();
    println!(
        "explain: UNSAT core is {} of {} constraint(s): {:?}",
        core.len(),
        constraints.len(),
        core
    );
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
