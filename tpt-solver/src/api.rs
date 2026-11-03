//! One-call entry points: read an input, solve it, and certify the answer.
//!
//! [`solve_str`] and [`solve_file`] are what the `tpt-solver` binary is built on, so
//! the library and the CLI always agree on what counts as trusted. Every
//! [`Report`] carries the checker's [`Outcome`]; only an `Accept` verdict may be
//! trusted. A model, proof or core is reported as the solver produced it, and the
//! verdict says whether the checker accepted it.
//!
//! ```
//! use tpt_solver::prelude::*;
//!
//! let report = solve_str(
//!     "p cnf 2 2\n1 0\n2 0\n",
//!     Format::Dimacs,
//!     &Options::default(),
//! )
//! .expect("well-formed input");
//! assert_eq!(report.claim, SolveResult::Sat);
//! assert!(report.verdict.is_accept());
//! ```

use std::fmt;
use std::io::{self, Read};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use crate::parsers::dimacs::parse_dimacs_located;
use crate::parsers::mps::parse_mps_located;
use crate::parsers::smtlib2::{parse_script_located, SmtError};
use crate::parsers::Located;
use crate::policy::solve_cnf_certified;
use crate::reference::{
    solve_and_check_arrays, solve_and_check_bv_certified, solve_and_check_lra_with_cert, Problem,
};
use tpt_solver_check::lra::check_farkas;
use tpt_solver_check::lrat::{check_proof, LratProof, LratStep};
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;
use tpt_solver_core::ir::{Lit, VarId};
use tpt_solver_core::lra::{lra_model, FarkasCertificate, LinConstraint};
use tpt_solver_core::rational::Rational;

/// The input languages this crate can read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Format {
    /// DIMACS CNF (`p cnf ...`).
    Dimacs,
    /// SMT-LIB2 script (`.smt2` / `.smt`).
    SmtLib2,
    /// Free-format LP-MPS (feasibility only; the objective is dropped).
    Mps,
}

impl Format {
    /// The name used by the CLI's `--format` flag.
    pub fn name(self) -> &'static str {
        match self {
            Format::Dimacs => "dimacs",
            Format::SmtLib2 => "smt2",
            Format::Mps => "mps",
        }
    }

    /// Parse a `--format` name (`dimacs`/`cnf`, `smt2`/`smt`, `mps`).
    pub fn from_name(name: &str) -> Option<Format> {
        match name {
            "dimacs" | "cnf" => Some(Format::Dimacs),
            "smt2" | "smt" | "smt-lib2" => Some(Format::SmtLib2),
            "mps" => Some(Format::Mps),
            _ => None,
        }
    }

    /// Guess the format from a file name, ignoring a trailing `.gz`.
    pub fn from_path(path: &str) -> Option<Format> {
        let base = path.strip_suffix(".gz").unwrap_or(path);
        let ext = base.rsplit('.').next()?;
        match ext.to_ascii_lowercase().as_str() {
            "cnf" => Some(Format::Dimacs),
            "smt2" | "smt" => Some(Format::SmtLib2),
            "mps" => Some(Format::Mps),
            _ => None,
        }
    }

    /// Guess the format from the content: `p cnf` header, a leading `(`
    /// s-expression, or an MPS `NAME`/`ROWS` section keyword in column 0.
    pub fn sniff(input: &str) -> Option<Format> {
        for line in input.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            if trimmed == "c" || trimmed.starts_with("c ") || trimmed.starts_with('*') {
                continue; // DIMACS / MPS comment
            }
            if trimmed.starts_with(';') {
                continue; // SMT-LIB2 comment
            }
            if trimmed.starts_with('(') {
                return Some(Format::SmtLib2);
            }
            let mut words = trimmed.split_whitespace();
            if trimmed.starts_with('p') && words.nth(1) == Some("cnf") {
                return Some(Format::Dimacs);
            }
            let column_zero = !line.starts_with(char::is_whitespace);
            if column_zero && (trimmed.starts_with("NAME") || trimmed.starts_with("ROWS")) {
                return Some(Format::Mps);
            }
            return None;
        }
        None
    }
}

impl fmt::Display for Format {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Which decision procedure produced an answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Theory {
    /// Propositional CNF, solved by certified CDCL.
    Cnf,
    /// Linear real arithmetic, certified by Farkas multipliers and model re-evaluation.
    Lra,
    /// Fixed-width bit-vectors, bit-blasted onto CDCL.
    Bv,
    /// Ground arrays (QF_AX positive equalities).
    Array,
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Theory::Cnf => "CNF",
            Theory::Lra => "LRA",
            Theory::Bv => "BV",
            Theory::Array => "AX",
        })
    }
}

/// A satisfying assignment as the solver produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Model {
    /// CNF: entry `i` is the value of variable `i + 1`.
    Bool(Vec<bool>),
    /// Named values for SMT-LIB2 / MPS inputs, rendered for display.
    Named(Vec<(String, String)>),
}

/// A checkable certificate for an UNSAT claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    /// DRAT-style clause list for CNF and bit-vector problems. Each entry is one
    /// clause (signed DIMACS literals) derived by reverse unit propagation from the
    /// input plus earlier entries. The last entry is the empty clause. This is the
    /// RUP subset of DRAT: no deletions and no LRAT hints. See `docs/proof-format.md`.
    Drat(Vec<Vec<i32>>),
    /// Farkas multipliers for an LRA problem: `(constraint index, multiplier)` for
    /// every nonzero multiplier, indexed in the order the constraints were lowered.
    Farkas(Vec<(usize, Rational)>),
}

/// Size and cost information for one solve.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stats {
    /// Number of Boolean or real variables in the lowered problem.
    pub variables: usize,
    /// Number of clauses (CNF) or linear constraints (LRA/MPS), after lowering.
    pub constraints: usize,
    /// Wall-clock time spent on the whole call, including parsing.
    pub elapsed: Duration,
    /// CDCL workers that raced for the answer (`1` for sequential).
    pub workers: usize,
}

/// The result of one [`solve_str`] / [`solve_file`] call.
#[derive(Clone, Debug)]
pub struct Report {
    /// Which decision procedure ran.
    pub theory: Theory,
    /// The engine's claim.
    pub claim: SolveResult,
    /// The checker's verdict on `claim` and its witness. Trust the answer only if
    /// this is [`Outcome::Accept`].
    pub verdict: Outcome,
    /// A model, present on SAT when the engine produced one.
    pub model: Option<Model>,
    /// The certificate for UNSAT, present when [`Options::want_proof`] is set.
    pub proof: Option<Proof>,
    /// Indices of the input clauses (CNF) or constraints (LRA/MPS) that are still
    /// needed for the UNSAT claim. Present when [`Options::explain`] is set.
    ///
    /// For CNF this comes from clause deletion: each clause is dropped in turn, and
    /// stays dropped only if the rest is still certified UNSAT. The result is
    /// irreducible, meaning no single clause can be removed, but it is not
    /// necessarily the smallest core.
    pub core: Option<Vec<usize>>,
    /// Sizes and timing.
    pub stats: Stats,
}

/// Start-of-call timestamp. `Instant` panics on `wasm32-unknown-unknown`, which has
/// no clock, so there the elapsed time is reported as zero.
#[derive(Clone, Copy, Debug)]
struct Clock(Option<Instant>);

impl Clock {
    fn start() -> Clock {
        if cfg!(target_arch = "wasm32") {
            Clock(None)
        } else {
            Clock(Some(Instant::now()))
        }
    }

    fn elapsed(self) -> Duration {
        self.0.map_or(Duration::ZERO, |t| t.elapsed())
    }
}

/// Options for a solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    /// Step budget for each engine run before it gives up with `Unknown`.
    pub fuel: u64,
    /// Number of diverse CDCL workers racing on CNF problems. `1` is sequential.
    pub workers: usize,
    /// Wall-clock limit. On expiry the call returns `Unknown` (see [`solve_str`]).
    pub timeout: Option<Duration>,
    /// Attach a [`Proof`] to UNSAT reports.
    pub want_proof: bool,
    /// Attach a [`Report::core`] to UNSAT reports. This is costly for CNF: it
    /// re-solves the formula once per clause.
    pub explain: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            fuel: 10_000_000,
            workers: 1,
            timeout: None,
            want_proof: false,
            explain: false,
        }
    }
}

/// Errors from reading, parsing or lowering an input, or from a standalone check.
#[derive(Debug)]
pub enum Error {
    /// The input could not be read.
    Io {
        /// The path, or `-` for standard input.
        path: String,
        /// The underlying I/O error.
        source: io::Error,
    },
    /// The format was not given and could not be detected.
    UnknownFormat,
    /// The input is malformed. `line` is 1-based, or `0` for the whole document.
    Parse {
        /// The format the input was parsed as.
        format: Format,
        /// The line the error was found on, or `0`.
        line: usize,
        /// What went wrong.
        message: String,
    },
    /// The input parsed but cannot be lowered to a supported theory, or a proof
    /// cannot be checked standalone.
    Unsupported(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Io { path, source } => write!(f, "cannot read '{}': {}", path, source),
            Error::UnknownFormat => {
                write!(
                    f,
                    "cannot detect the input format; pass --format dimacs|smt2|mps"
                )
            }
            Error::Parse {
                format,
                line,
                message,
            } => {
                if *line == 0 {
                    write!(f, "{} parse error: {}", format, message)
                } else {
                    write!(f, "{} parse error at line {}: {}", format, line, message)
                }
            }
            Error::Unsupported(what) => write!(f, "unsupported: {}", what),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Read an input from `path`, or from standard input when `path` is `-`.
///
/// Gzip-compressed input is detected by its magic bytes and decompressed, whatever
/// the file name says.
pub fn read_input(path: &str) -> Result<String, Error> {
    let io_err = |source| Error::Io {
        path: path.to_string(),
        source,
    };
    let bytes = if path == "-" {
        let mut buf = Vec::new();
        io::stdin().read_to_end(&mut buf).map_err(io_err)?;
        buf
    } else {
        std::fs::read(path).map_err(io_err)?
    };
    let text = if bytes.starts_with(&[0x1f, 0x8b]) {
        let mut out = String::new();
        flate2::read::GzDecoder::new(&bytes[..])
            .read_to_string(&mut out)
            .map_err(io_err)?;
        out
    } else {
        String::from_utf8(bytes).map_err(|e| Error::Io {
            path: path.to_string(),
            source: io::Error::new(io::ErrorKind::InvalidData, e),
        })?
    };
    Ok(text)
}

/// Pick the input format: an explicit choice wins, then the file extension, then the
/// content. `path` is `None` for standard input.
pub fn resolve_format(
    explicit: Option<Format>,
    path: Option<&str>,
    input: &str,
) -> Result<Format, Error> {
    if let Some(f) = explicit {
        return Ok(f);
    }
    if let Some(f) = path.and_then(Format::from_path) {
        return Ok(f);
    }
    Format::sniff(input).ok_or(Error::UnknownFormat)
}

/// Solve `input` in the given `format` and certify the answer.
///
/// With [`Options::timeout`] set, the solve runs on a helper thread. If the limit
/// expires first, the call returns a [`Report`] with `Unknown`. The helper thread is
/// then detached and keeps running until the process exits, so a long-lived host
/// should prefer a fuel budget.
pub fn solve_str(input: &str, format: Format, opts: &Options) -> Result<Report, Error> {
    let Some(limit) = opts.timeout else {
        return solve_now(input, format, opts, Clock::start());
    };
    let start = Clock::start();
    let (tx, rx) = mpsc::channel();
    let owned = input.to_string();
    let worker_opts = opts.clone();
    thread::spawn(move || {
        let _ = tx.send(solve_now(&owned, format, &worker_opts, start));
    });
    match rx.recv_timeout(limit) {
        Ok(result) => result,
        Err(_) => Ok(Report {
            theory: Theory::Cnf,
            claim: SolveResult::Unknown,
            verdict: Outcome::Inconclusive,
            model: None,
            proof: None,
            core: None,
            stats: Stats {
                variables: 0,
                constraints: 0,
                elapsed: start.elapsed(),
                workers: opts.workers.max(1),
            },
        }),
    }
}

/// Read a file (or standard input for `-`), detect its format, and solve it.
/// See [`read_input`], [`resolve_format`] and [`solve_str`].
pub fn solve_file(path: &str, format: Option<Format>, opts: &Options) -> Result<Report, Error> {
    let input = read_input(path)?;
    let hint = (path != "-").then_some(path);
    let format = resolve_format(format, hint, &input)?;
    solve_str(&input, format, opts)
}

fn solve_now(input: &str, format: Format, opts: &Options, start: Clock) -> Result<Report, Error> {
    match format {
        Format::Dimacs => {
            let problem = parse_dimacs_located(input).map_err(|e| Error::Parse {
                format,
                line: e.line,
                message: e.error.to_string(),
            })?;
            Ok(solve_cnf(&problem, opts, start))
        }
        Format::Mps => {
            let lra = parse_mps_located(input).map_err(|e| parse_error(format, e))?;
            let names = lra.vars.clone();
            Ok(solve_lra(&lra.constraints, names, opts, start))
        }
        Format::SmtLib2 => solve_smtlib2(input, opts, start),
    }
}

fn parse_error(format: Format, e: Located<crate::parsers::mps::MpsError>) -> Error {
    Error::Parse {
        format,
        line: e.line,
        message: e.error.to_string(),
    }
}

fn solve_smtlib2(input: &str, opts: &Options, start: Clock) -> Result<Report, Error> {
    let script = parse_script_located(input).map_err(smt_located)?;

    // Prefer linear arithmetic, then bit-vectors, then arrays, then propositional.
    match script.to_lra() {
        Ok(prob) => {
            let names = prob.vars.clone();
            return Ok(solve_lra(&prob.constraints, names, opts, start));
        }
        Err(SmtError::Unsupported(_)) => {}
        Err(e) => return Err(smt_error(e)),
    }

    match script.to_bv() {
        Ok(prob) => {
            let c = solve_and_check_bv_certified(prob.var_count, &prob.assertions, opts.fuel);
            let model = c.model.as_ref().map(|values| {
                Model::Named(
                    prob.names
                        .iter()
                        .zip(values)
                        .map(|(n, v)| (n.clone(), v.to_string()))
                        .collect(),
                )
            });
            return Ok(Report {
                theory: Theory::Bv,
                claim: c.claim,
                verdict: c.verdict,
                model,
                proof: if opts.want_proof {
                    c.proof.map(Proof::Drat)
                } else {
                    None
                },
                core: None,
                stats: Stats {
                    variables: prob.var_count as usize,
                    constraints: prob.assertions.len(),
                    elapsed: start.elapsed(),
                    workers: 1,
                },
            });
        }
        Err(SmtError::Unsupported(_)) => {}
        Err(e) => return Err(smt_error(e)),
    }

    match script.to_array() {
        Ok(prob) => {
            let (claim, verdict) = solve_and_check_arrays(
                prob.avars.len() as u32,
                prob.evars.len() as u32,
                &prob.assertions,
                opts.fuel,
            );
            return Ok(Report {
                theory: Theory::Array,
                claim,
                verdict,
                model: None,
                proof: None,
                core: None,
                stats: Stats {
                    variables: prob.avars.len() + prob.evars.len(),
                    constraints: prob.assertions.len(),
                    elapsed: start.elapsed(),
                    workers: 1,
                },
            });
        }
        Err(SmtError::Unsupported(_)) => {}
        Err(e) => return Err(smt_error(e)),
    }

    let problem = script.to_cnf().map_err(|e| {
        Error::Unsupported(format!(
            "{} (only QF_LRA, QF_BV, QF_AX and QF_SAT subsets are supported)",
            e
        ))
    })?;
    Ok(solve_cnf(&problem, opts, start))
}

fn smt_error(e: SmtError) -> Error {
    Error::Parse {
        format: Format::SmtLib2,
        line: 0,
        message: e.to_string(),
    }
}

fn smt_located(e: Located<SmtError>) -> Error {
    Error::Parse {
        format: Format::SmtLib2,
        line: e.line,
        message: e.error.to_string(),
    }
}

fn solve_cnf(problem: &Problem, opts: &Options, start: Clock) -> Report {
    let (cert, _dump) = solve_cnf_certified(problem, opts.fuel, opts.workers);
    let claim = cert.claim;
    let verdict = cert.verdict;

    let core = if opts.explain && claim == SolveResult::Unsat {
        Some(deletion_core(problem, opts.fuel))
    } else {
        None
    };
    Report {
        theory: Theory::Cnf,
        claim,
        verdict,
        model: match (claim, cert.model) {
            (SolveResult::Sat, Some(m)) => Some(Model::Bool(m)),
            _ => None,
        },
        proof: match cert.proof {
            Some(p) if opts.want_proof => Some(Proof::Drat(lrat_to_clauses(&p))),
            _ => None,
        },
        core,
        stats: Stats {
            variables: problem.var_count as usize,
            constraints: problem.clauses.len(),
            elapsed: start.elapsed(),
            workers: opts.workers.max(1),
        },
    }
}

/// Deletion-based UNSAT core over the clause list. Each clause is tentatively
/// dropped, and stays dropped if the rest is still certified UNSAT. Clauses that
/// survive are all needed. A solve that is not certified UNSAT keeps its clause,
/// so the result is always a certified-UNSAT subset.
fn deletion_core(problem: &Problem, fuel: u64) -> Vec<usize> {
    let mut keep: Vec<usize> = (0..problem.clauses.len()).collect();
    let mut pos = 0;
    while pos < keep.len() {
        let trial = Problem {
            var_count: problem.var_count,
            clauses: keep
                .iter()
                .enumerate()
                .filter(|(p, _)| *p != pos)
                .map(|(_, &c)| problem.clauses[c].clone())
                .collect(),
        };
        let (cert, _dump) = solve_cnf_certified(&trial, fuel, 1);
        if cert.claim == SolveResult::Unsat && cert.verdict.is_accept() {
            keep.remove(pos);
        } else {
            pos += 1;
        }
    }
    keep
}

fn solve_lra(
    constraints: &[LinConstraint],
    names: Vec<String>,
    opts: &Options,
    start: Clock,
) -> Report {
    let variables = names.len();
    let (claim, verdict, cert) = solve_and_check_lra_with_cert(constraints, opts.fuel);
    let model = if claim == SolveResult::Sat {
        match lra_model(constraints) {
            Some(Some(values)) => Some(Model::Named(
                names
                    .into_iter()
                    .zip(values.iter().map(|v| v.to_string()))
                    .collect(),
            )),
            _ => None,
        }
    } else {
        None
    };
    let nonzero = |c: &FarkasCertificate| -> Vec<(usize, Rational)> {
        c.multipliers
            .iter()
            .enumerate()
            .filter(|(_, m)| !m.is_zero())
            .map(|(i, m)| (i, *m))
            .collect()
    };
    let core = match (&cert, claim) {
        (Some(c), SolveResult::Unsat) if opts.explain => {
            Some(nonzero(c).into_iter().map(|(i, _)| i).collect())
        }
        _ => None,
    };
    let proof = match &cert {
        Some(c) if opts.want_proof && claim == SolveResult::Unsat => {
            Some(Proof::Farkas(nonzero(c)))
        }
        _ => None,
    };
    Report {
        theory: Theory::Lra,
        claim,
        verdict,
        model,
        proof,
        core,
        stats: Stats {
            variables,
            constraints: constraints.len(),
            elapsed: start.elapsed(),
            workers: 1,
        },
    }
}

/// Convert a checked [`LratProof`] to the DRAT-style clause list reported in
/// [`Proof::Drat`].
pub fn lrat_to_clauses(proof: &LratProof) -> Vec<Vec<i32>> {
    proof
        .steps()
        .iter()
        .map(|step| {
            step.clause
                .iter()
                .map(|lit| {
                    let n = lit.var().get() as i32;
                    if lit.is_positive() {
                        n
                    } else {
                        -n
                    }
                })
                .collect()
        })
        .collect()
}

/// Build a checker-side [`LratProof`] from a DRAT-style clause list, with no hints.
/// Literals must be nonzero; a `0` is rejected by returning `None`.
pub fn clauses_to_lrat(clauses: &[Vec<i32>]) -> Option<LratProof> {
    let mut steps = Vec::with_capacity(clauses.len());
    for clause in clauses {
        let mut lits: Vec<Lit<()>> = Vec::with_capacity(clause.len());
        for &l in clause {
            let v = VarId::new(l.unsigned_abs())?;
            lits.push(Lit::new(v, l > 0));
        }
        steps.push(LratStep {
            clause: lits,
            hints: Vec::new(),
        });
    }
    Some(LratProof::new(steps))
}

/// Check a proof produced by the solver against the problem it was made for,
/// without solving anything. This is what the `check` subcommand runs.
///
/// * DIMACS problems take a DRAT-style clause list (see [`Proof::Drat`]).
/// * SMT-LIB2 (LRA) and MPS problems take the Farkas text written by `--emit-proof`:
///   `#` comments and then `index multiplier` lines.
///
/// Bit-vector proofs are checked against the bit-blasted CNF, which this crate does
/// not yet export, so they return [`Error::Unsupported`].
pub fn check_proof_text(problem: &str, format: Format, proof: &str) -> Result<Outcome, Error> {
    match format {
        Format::Dimacs => {
            let p = parse_dimacs_located(problem).map_err(|e| Error::Parse {
                format,
                line: e.line,
                message: e.error.to_string(),
            })?;
            let clauses = parse_drat_text(proof)?;
            let lrat = clauses_to_lrat(&clauses)
                .ok_or_else(|| Error::Unsupported("proof literal 0 inside a clause".into()))?;
            let cnf = p.as_cnf();
            Ok(check_proof(cnf.clauses(), &lrat, p.var_count))
        }
        Format::Mps => {
            let lra = parse_mps_located(problem).map_err(|e| parse_error(format, e))?;
            check_farkas_text(&lra.constraints, proof)
        }
        Format::SmtLib2 => {
            let script = parse_script_located(problem).map_err(smt_located)?;
            let lra = script.to_lra().map_err(|e| {
                Error::Unsupported(format!("proof checking needs a QF_LRA problem: {}", e))
            })?;
            check_farkas_text(&lra.constraints, proof)
        }
    }
}

fn parse_drat_text(text: &str) -> Result<Vec<Vec<i32>>, Error> {
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    for (idx, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        for tok in line.split_whitespace() {
            if tok == "d" {
                return Err(Error::Unsupported("clause deletions (d lines)".into()));
            }
            let lit: i32 = tok.parse().map_err(|_| Error::Parse {
                format: Format::Dimacs,
                line: idx + 1,
                message: format!("expected an integer literal, found '{}'", tok),
            })?;
            if lit == 0 {
                clauses.push(std::mem::take(&mut current));
            } else {
                current.push(lit);
            }
        }
    }
    if !current.is_empty() {
        return Err(Error::Parse {
            format: Format::Dimacs,
            line: 0,
            message: "proof ends in the middle of a clause (missing final 0)".into(),
        });
    }
    Ok(clauses)
}

fn check_farkas_text(constraints: &[LinConstraint], text: &str) -> Result<Outcome, Error> {
    let mut multipliers = vec![Rational::zero(); constraints.len()];
    for (idx, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split_whitespace();
        let bad = || Error::Parse {
            format: Format::Mps,
            line: idx + 1,
            message: format!("expected 'index multiplier', found '{}'", line),
        };
        let index: usize = parts.next().and_then(|s| s.parse().ok()).ok_or_else(bad)?;
        let value = parts.next().and_then(Rational::parse).ok_or_else(bad)?;
        let slot = multipliers.get_mut(index).ok_or_else(|| Error::Parse {
            format: Format::Mps,
            line: idx + 1,
            message: format!(
                "constraint index {} is out of range (problem has {})",
                index,
                constraints.len()
            ),
        })?;
        *slot = value;
    }
    Ok(check_farkas(
        constraints,
        &FarkasCertificate { multipliers },
    ))
}

impl Report {
    /// Render the report as one JSON object, in the shape `--output json` prints.
    ///
    /// `proof_file` is the path the proof was written to, if one was. Output is
    /// compact and on a single line, with keys `result`, `checker`, `theory`,
    /// `model`, `core`, `proof`, `proof_file` and `stats`.
    pub fn to_json(&self, proof_file: Option<&str>) -> String {
        let result = match self.claim {
            SolveResult::Sat => "sat",
            SolveResult::Unsat => "unsat",
            SolveResult::Unknown => "unknown",
        };
        let checker = if self.verdict.is_accept() {
            "accept"
        } else if self.verdict.is_reject() {
            "reject"
        } else {
            "inconclusive"
        };
        let model = match &self.model {
            Some(Model::Bool(values)) => {
                let lits: Vec<String> = values
                    .iter()
                    .enumerate()
                    .map(|(i, &b)| {
                        let v = (i + 1) as i64;
                        (if b { v } else { -v }).to_string()
                    })
                    .collect();
                format!("[{}]", lits.join(","))
            }
            Some(Model::Named(pairs)) => {
                let fields: Vec<String> = pairs
                    .iter()
                    .map(|(k, v)| format!("{}:{}", json_string(k), json_string(v)))
                    .collect();
                format!("{{{}}}", fields.join(","))
            }
            None => "null".to_string(),
        };
        let core = match &self.core {
            Some(c) => format!(
                "[{}]",
                c.iter().map(usize::to_string).collect::<Vec<_>>().join(",")
            ),
            None => "null".to_string(),
        };
        let proof = match &self.proof {
            Some(Proof::Drat(steps)) => format!("{{\"steps\":{}}}", steps.len()),
            Some(Proof::Farkas(pairs)) => format!("{{\"multipliers\":{}}}", pairs.len()),
            None => "null".to_string(),
        };
        let proof_file = match proof_file {
            Some(p) if self.proof.is_some() => json_string(p),
            _ => "null".to_string(),
        };
        format!(
            "{{\"result\":{},\"checker\":{},\"theory\":{},\"model\":{},\"core\":{},\"proof\":{},\"proof_file\":{},\"stats\":{{\"variables\":{},\"constraints\":{},\"workers\":{},\"elapsed_ms\":{:.3}}}}}",
            json_string(result),
            json_string(checker),
            json_string(&self.theory.to_string()),
            model,
            core,
            proof,
            proof_file,
            self.stats.variables,
            self.stats.constraints,
            self.stats.workers,
            self.stats.elapsed.as_secs_f64() * 1000.0
        )
    }
}

/// Quote and escape `s` as a JSON string.
fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(feature = "serde")]
mod serde_impls {
    use super::{Proof, Report, Stats};
    use serde::ser::{Serialize, SerializeStruct, Serializer};
    use tpt_solver_check::outcome::Outcome;
    use tpt_solver_core::engine::SolveResult;

    fn claim_name(claim: SolveResult) -> &'static str {
        match claim {
            SolveResult::Sat => "sat",
            SolveResult::Unsat => "unsat",
            SolveResult::Unknown => "unknown",
        }
    }

    fn checker_name(verdict: Outcome) -> &'static str {
        if verdict.is_accept() {
            "accept"
        } else if verdict.is_reject() {
            "reject"
        } else {
            "inconclusive"
        }
    }

    impl Serialize for Report {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            let mut st = s.serialize_struct("Report", 7)?;
            st.serialize_field("theory", &self.theory)?;
            st.serialize_field("result", claim_name(self.claim))?;
            st.serialize_field("checker", checker_name(self.verdict))?;
            st.serialize_field("model", &self.model)?;
            st.serialize_field("proof", &self.proof)?;
            st.serialize_field("core", &self.core)?;
            st.serialize_field("stats", &self.stats)?;
            st.end()
        }
    }

    impl Serialize for Stats {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            let mut st = s.serialize_struct("Stats", 4)?;
            st.serialize_field("variables", &self.variables)?;
            st.serialize_field("constraints", &self.constraints)?;
            st.serialize_field("workers", &self.workers)?;
            st.serialize_field("elapsed_ms", &(self.elapsed.as_secs_f64() * 1000.0))?;
            st.end()
        }
    }

    impl Serialize for Proof {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            match self {
                Proof::Drat(clauses) => {
                    let mut st = s.serialize_struct("Proof", 2)?;
                    st.serialize_field("format", "drat")?;
                    st.serialize_field("clauses", clauses)?;
                    st.end()
                }
                Proof::Farkas(pairs) => {
                    let rendered: Vec<(usize, String)> =
                        pairs.iter().map(|(i, m)| (*i, m.to_string())).collect();
                    let mut st = s.serialize_struct("Proof", 2)?;
                    st.serialize_field("format", "farkas")?;
                    st.serialize_field("multipliers", &rendered)?;
                    st.end()
                }
            }
        }
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Theory {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.to_string())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Model {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        match self {
            Model::Bool(values) => {
                let lits: Vec<i64> = values
                    .iter()
                    .enumerate()
                    .map(|(i, &b)| {
                        let v = (i + 1) as i64;
                        if b {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                s.serialize_newtype_variant("Model", 0, "bool", &lits)
            }
            Model::Named(pairs) => s.serialize_newtype_variant("Model", 1, "named", pairs),
        }
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::{solve_str, Format, Options};

    #[test]
    fn report_serializes_with_its_checker_verdict() {
        let opts = Options {
            want_proof: true,
            ..Options::default()
        };
        let report = solve_str("p cnf 1 2\n1 0\n-1 0\n", Format::Dimacs, &opts).unwrap();
        let json = serde_json::to_value(&report).unwrap();
        assert_eq!(json["result"], "unsat");
        assert_eq!(json["checker"], "accept");
        assert_eq!(json["theory"], "CNF");
        assert_eq!(json["proof"]["format"], "drat");
        assert!(json["stats"]["elapsed_ms"].is_f64());
    }

    #[test]
    fn sat_model_serializes_as_literals() {
        let report = solve_str("p cnf 2 1\n-2 0\n", Format::Dimacs, &Options::default()).unwrap();
        let json = serde_json::to_value(&report).unwrap();
        assert_eq!(json["result"], "sat");
        assert_eq!(json["model"]["bool"], serde_json::json!([1, -2]));
    }
}
