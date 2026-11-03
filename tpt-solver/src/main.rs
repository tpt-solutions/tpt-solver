//! `tpt-solver` binary: a certificate-architecture SAT/SMT solver CLI.
//!
//! ```text
//! tpt-solver FILE                     solve FILE (.cnf, .smt2, .mps, optionally .gz); "-" reads stdin
//! tpt-solver FILE --format smt2       choose the format when it cannot be detected
//! tpt-solver FILE --output competition  SAT-competition output and exit codes (10/20/0)
//! tpt-solver FILE --emit-proof P      on UNSAT, write the checked certificate to P
//! tpt-solver FILE --explain           on UNSAT, print the needed clauses or constraints
//! tpt-solver check PROBLEM PROOF      check a proof file against its problem, without solving
//! tpt-solver bench                    random 3-SAT ladder, CSV on stdout
//! tpt-solver completions <SHELL>      print a shell completion script
//! tpt-solver man                      print the man page
//! ```
//!
//! Every answer is revalidated by the trusted checker (`tpt-solver-check`). The
//! printed result is what the checker accepted, and the verdict is shown with it.
//! Exit codes are described in the README.

use std::fmt;
use std::io::{self, Write};
use std::process::ExitCode;
use std::time::Duration;

use clap::{ArgAction, CommandFactory, Parser, Subcommand, ValueEnum};
use tpt_solver::api::{self, Format, Model, Options, Proof, Report};
use tpt_solver::policy::solve_cnf_certified;
use tpt_solver::reference::{solve_and_check, solve_and_check_cdcl, Problem};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;

/// tpt-solver: a certificate-architecture SAT/SMT solver suite.
///
/// Every answer this CLI prints is revalidated by the independent trusted checker
/// (`tpt-solver-check`) before it is reported. Run with no input for a built-in demo
/// of that pipeline.
#[derive(Parser)]
#[command(
    name = "tpt-solver",
    version,
    about,
    args_conflicts_with_subcommands = true
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Input file: DIMACS CNF, SMT-LIB2 (.smt2/.smt) or LP-MPS (.mps), optionally
    /// gzip-compressed. Use `-` to read standard input. Omit to run the demo.
    ///
    /// MPS input is feasibility-only: the objective (N) row is dropped, so the
    /// solver answers whether the constraints are satisfiable and does not optimize.
    input: Option<String>,

    /// Input format, when it cannot be read from the extension or the content.
    #[arg(long, value_name = "FORMAT", value_parser = parse_format_arg)]
    format: Option<Format>,

    /// How results are printed.
    #[arg(long, value_enum, default_value_t = Output::Human)]
    output: Output,

    /// Step budget for each engine run before giving up with `unknown`.
    #[arg(long, default_value_t = 10_000_000, value_name = "N")]
    fuel: u64,

    /// Race N diverse CDCL workers (CNF inputs only).
    #[arg(long, value_name = "N")]
    parallel: Option<usize>,

    /// Give up after SECS seconds of wall-clock time and report `unknown`.
    #[arg(long, value_name = "SECS")]
    timeout: Option<f64>,

    /// On UNSAT, write the checked certificate to FILE. CNF writes a DRAT-style clause
    /// list, and LRA writes Farkas multipliers.
    #[arg(long, value_name = "FILE")]
    emit_proof: Option<String>,

    /// On UNSAT, report the clauses or constraints that are needed for the
    /// contradiction. CNF cores are computed by deletion and cost one solve per clause.
    #[arg(long)]
    explain: bool,

    /// Print the model on SAT (always printed in competition mode).
    #[arg(long)]
    model: bool,

    /// Print sizes and timing to stderr.
    #[arg(long)]
    stats: bool,

    /// More detail on stderr (repeat for more).
    #[arg(short, long, action = ArgAction::Count, conflicts_with = "quiet")]
    verbose: u8,

    /// Print only the result line.
    #[arg(short, long)]
    quiet: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Check a proof against its problem without solving the problem.
    Check {
        /// The problem file (DIMACS, SMT-LIB2 or MPS).
        problem: String,
        /// The proof file, as written by `--emit-proof`.
        proof: String,
        /// Problem format, when it cannot be detected.
        #[arg(long, value_name = "FORMAT", value_parser = parse_format_arg)]
        format: Option<Format>,
    },
    /// Run a random 3-SAT performance ladder through the certified pipeline (CSV).
    Bench {
        /// Random instances per size.
        #[arg(long, default_value_t = 5)]
        seeds: u32,
    },
    /// Print a shell completion script to stdout.
    Completions {
        /// The shell to generate for.
        shell: clap_complete::Shell,
    },
    /// Print the man page (roff) to stdout.
    Man,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
enum Output {
    /// Readable text on stdout.
    Human,
    /// One JSON object on stdout.
    Json,
    /// SAT-competition format: `s` and `v` lines, exit codes 10, 20 and 0.
    Competition,
}

fn parse_format_arg(s: &str) -> Result<Format, String> {
    Format::from_name(s)
        .ok_or_else(|| format!("unknown format '{s}' (expected dimacs, smt2 or mps)"))
}

/// Errors that stop the CLI before it can report an answer.
#[derive(Debug)]
enum CliError {
    /// A library error: reading, parsing, lowering, or detection.
    Api(api::Error),
    /// Bad flag values.
    Usage(String),
    /// Writing an output file failed.
    Write { path: String, source: io::Error },
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CliError::Api(e) => write!(f, "{}", e),
            CliError::Usage(msg) => write!(f, "{}", msg),
            CliError::Write { path, source } => write!(f, "cannot write '{}': {}", path, source),
        }
    }
}

impl From<api::Error> for CliError {
    fn from(e: api::Error) -> CliError {
        CliError::Api(e)
    }
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::from(2)
        }
    }
}

fn run(cli: Cli) -> Result<ExitCode, CliError> {
    match &cli.command {
        Some(Command::Check {
            problem,
            proof,
            format,
        }) => run_check(problem, proof, *format),
        Some(Command::Bench { seeds }) => {
            run_bench(*seeds);
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Completions { shell }) => {
            clap_complete::generate(*shell, &mut Cli::command(), "tpt-solver", &mut io::stdout());
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Man) => {
            let man = clap_mangen::Man::new(Cli::command());
            man.render(&mut io::stdout())
                .map_err(|source| CliError::Write {
                    path: "stdout".to_string(),
                    source,
                })?;
            Ok(ExitCode::SUCCESS)
        }
        None => match &cli.input {
            Some(path) => run_solve(&cli, path),
            None => {
                run_demo();
                Ok(ExitCode::SUCCESS)
            }
        },
    }
}

fn run_solve(cli: &Cli, path: &str) -> Result<ExitCode, CliError> {
    let opts = Options {
        fuel: cli.fuel,
        workers: cli.parallel.unwrap_or(1).max(1),
        timeout: match cli.timeout {
            Some(secs) => Some(
                Duration::try_from_secs_f64(secs)
                    .map_err(|_| CliError::Usage(format!("invalid --timeout {secs}")))?,
            ),
            None => None,
        },
        want_proof: cli.emit_proof.is_some(),
        explain: cli.explain,
    };

    let input = api::read_input(path)?;
    let hint = (path != "-").then_some(path);
    let format = api::resolve_format(cli.format, hint, &input)?;
    if cli.verbose > 0 {
        eprintln!("format: {}", format);
    }

    let report = api::solve_str(&input, format, &opts)?;
    let accepted = report.verdict.is_accept();

    if let Some(proof_path) = &cli.emit_proof {
        emit_proof(proof_path, &report, cli.output)?;
    }

    if cli.stats || cli.verbose > 0 {
        eprintln!(
            "stats: theory={} variables={} constraints={} workers={} elapsed={:.1}ms",
            report.theory,
            report.stats.variables,
            report.stats.constraints,
            report.stats.workers,
            report.stats.elapsed.as_secs_f64() * 1000.0
        );
    }

    match cli.output {
        Output::Human => print_human(&report, cli),
        Output::Competition => print_competition(&report),
        Output::Json => print_json(&report, cli),
    }

    Ok(exit_code(&report, cli.output, accepted))
}

/// Exit status for a solve. Competition mode uses the SAT-competition codes. In the
/// other modes, an answer the checker did not accept is `1`, so scripts can tell
/// when the trusted kernel refused.
fn exit_code(report: &Report, output: Output, accepted: bool) -> ExitCode {
    let code = match (output, report.claim, accepted) {
        (_, SolveResult::Unknown, _) => 0,
        (_, _, false) => 1,
        (Output::Competition, SolveResult::Sat, true) => 10,
        (Output::Competition, SolveResult::Unsat, true) => 20,
        (_, _, true) => 0,
    };
    ExitCode::from(code)
}

fn claim_label(claim: SolveResult) -> &'static str {
    match claim {
        SolveResult::Sat => "SAT",
        SolveResult::Unsat => "UNSAT",
        SolveResult::Unknown => "UNKNOWN",
    }
}

fn checker_label(verdict: Outcome) -> &'static str {
    if verdict.is_accept() {
        "accept"
    } else if verdict.is_reject() {
        "reject"
    } else {
        "inconclusive"
    }
}

fn checker_note(claim: SolveResult, verdict: Outcome) -> &'static str {
    match (claim, verdict.is_accept()) {
        (SolveResult::Sat, true) => "model verified by the trusted kernel",
        (SolveResult::Unsat, true) => "proof verified by the trusted kernel",
        (SolveResult::Unknown, _) => "engine returned unknown (fuel or timeout)",
        (SolveResult::Sat, false) => "checker did not accept the model; do not trust this answer",
        (SolveResult::Unsat, false) => "checker did not accept the proof; do not trust this answer",
    }
}

fn print_human(report: &Report, cli: &Cli) {
    println!(
        "{}: {}",
        claim_label(report.claim),
        checker_note(report.claim, report.verdict)
    );
    if cli.quiet {
        return;
    }
    println!("theory: {}", report.theory);
    if cli.model {
        if let Some(model) = &report.model {
            println!("model: {}", model_text(model));
        }
    }
    if let Some(core) = &report.core {
        println!(
            "core: {} of {} {}: {:?}",
            core.len(),
            report.stats.constraints,
            if report.theory == api::Theory::Cnf {
                "clauses"
            } else {
                "constraints"
            },
            core
        );
    }
    if report.claim == SolveResult::Unsat && report.proof.is_none() && cli.emit_proof.is_some() {
        println!("note: no proof was produced for this answer");
    }
}

fn model_text(model: &Model) -> String {
    match model {
        Model::Bool(values) => values
            .iter()
            .enumerate()
            .map(|(i, &b)| {
                let v = (i + 1) as i64;
                if b {
                    v.to_string()
                } else {
                    (-v).to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(" "),
        Model::Named(pairs) => pairs
            .iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect::<Vec<_>>()
            .join(", "),
    }
}

fn print_competition(report: &Report) {
    if report.claim != SolveResult::Unknown && !report.verdict.is_accept() {
        println!("s UNKNOWN");
        println!("c checker did not accept the answer");
        return;
    }
    match report.claim {
        SolveResult::Unknown => println!("s UNKNOWN"),
        SolveResult::Unsat => println!("s UNSATISFIABLE"),
        SolveResult::Sat => {
            println!("s SATISFIABLE");
            if let Some(Model::Bool(values)) = &report.model {
                print_v_lines(values);
            }
        }
    }
}

/// Print a CNF model as SAT-competition `v` lines, wrapped near 78 columns and
/// terminated by `0`.
fn print_v_lines(values: &[bool]) {
    let mut line = String::from("v");
    for (i, &b) in values.iter().enumerate() {
        let v = (i + 1) as i64;
        let lit = if b { v } else { -v }.to_string();
        if line.len() + 1 + lit.len() > 78 {
            println!("{}", line);
            line = String::from("v");
        }
        line.push(' ');
        line.push_str(&lit);
    }
    if line.len() + 2 > 78 {
        println!("{}", line);
        line = String::from("v");
    }
    line.push_str(" 0");
    println!("{}", line);
}

/// Write `report`'s proof to `path`. Warns on stderr when there is none to write.
fn emit_proof(path: &str, report: &Report, output: Output) -> Result<(), CliError> {
    let Some(proof) = &report.proof else {
        if output != Output::Json {
            eprintln!("note: --emit-proof: no UNSAT proof for this answer; nothing written");
        }
        return Ok(());
    };
    let mut text = String::new();
    match proof {
        Proof::Drat(clauses) => {
            for clause in clauses {
                for lit in clause {
                    text.push_str(&lit.to_string());
                    text.push(' ');
                }
                text.push_str("0\n");
            }
        }
        Proof::Farkas(pairs) => {
            text.push_str("# Farkas certificate: nonzero (index multiplier) pairs\n");
            for (index, multiplier) in pairs {
                text.push_str(&format!("{} {}\n", index, multiplier));
            }
        }
    }
    std::fs::write(path, text).map_err(|source| CliError::Write {
        path: path.to_string(),
        source,
    })?;
    if output != Output::Json {
        eprintln!("proof written to '{}'", path);
    }
    Ok(())
}

fn run_check(problem: &str, proof: &str, format: Option<Format>) -> Result<ExitCode, CliError> {
    let input = api::read_input(problem)?;
    let hint = (problem != "-").then_some(problem);
    let format = api::resolve_format(format, hint, &input)?;
    let proof_text = api::read_input(proof)?;
    let verdict = api::check_proof_text(&input, format, &proof_text)?;
    match verdict {
        Outcome::Accept => {
            println!("s VERIFIED");
            Ok(ExitCode::SUCCESS)
        }
        Outcome::Reject => {
            println!("s NOT VERIFIED");
            Ok(ExitCode::from(1))
        }
        Outcome::Inconclusive => {
            println!("s INCONCLUSIVE");
            Ok(ExitCode::from(1))
        }
    }
}

/// Local performance harness: a deterministic random 3-SAT ladder around the phase
/// transition, run through the full certified CDCL pipeline. Output is CSV, one row
/// per instance, so runs can be compared across commits.
///
/// This is scaffolding for the SAT-COMP/SMT-COMP benchmark item. Competition runs
/// need the official corpora and hardware. The ladder catches gross regressions in
/// CI-sized time.
fn run_bench(seeds: u32) {
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

    println!("vars,clauses,seed,millis,claim,checker");
    for &n in &[100usize, 200, 300, 400, 500] {
        let m = ((n as f64) * 4.26).round() as usize; // near the phase transition
        for seed in 0..seeds {
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
            let (cert, _dump) = solve_cnf_certified(&problem, 50_000_000, 1);
            let millis = start.elapsed().as_secs_f64() * 1000.0;
            println!(
                "{},{},{},{:.3},{},{}",
                n,
                m,
                seed,
                millis,
                claim_label(cert.claim).to_lowercase(),
                checker_label(cert.verdict)
            );
        }
    }
    let _ = io::stdout().flush();
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

    demo("reference DPLL", solve_and_check(&sat_problem, 1_000_000));
    demo("reference DPLL", solve_and_check(&unsat_problem, 1_000_000));
    demo("CDCL engine", solve_and_check_cdcl(&sat_problem, 1_000_000));
    demo(
        "CDCL engine",
        solve_and_check_cdcl(&unsat_problem, 1_000_000),
    );
}

fn demo(label: &str, (claim, verdict): (SolveResult, Outcome)) {
    println!(
        "[{:>15}] claim = {:?}, checker = {:?}",
        label, claim, verdict
    );
    println!("                 {}", checker_note(claim, verdict));
}

fn print_json(report: &Report, cli: &Cli) {
    println!("{}", report.to_json(cli.emit_proof.as_deref()));
}
