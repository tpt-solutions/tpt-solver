//! Python bindings for tpt-solver, built with PyO3 and packaged with maturin.
//!
//! Every function returns a `dict` in the same shape the CLI's `--output json` prints,
//! with the proof and model as real Python lists. The `checker` key says whether the
//! trusted kernel accepted the answer. Only `"accept"` should be trusted.

use ::tpt_solver::api::{self, Format, Model, Options, Proof, Report};
use ::tpt_solver::check::outcome::Outcome;
use ::tpt_solver::core::engine::SolveResult;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyDict;

fn options(fuel: u64, proof: bool, explain: bool) -> Options {
    Options {
        fuel,
        want_proof: proof,
        explain,
        ..Options::default()
    }
}

fn parse_format(name: &str) -> PyResult<Option<Format>> {
    match name {
        "auto" => Ok(None),
        other => Format::from_name(other).map(Some).ok_or_else(|| {
            PyValueError::new_err(format!(
                "unknown format '{other}' (expected auto, dimacs, smt2 or mps)"
            ))
        }),
    }
}

fn to_py_err(e: api::Error) -> PyErr {
    PyValueError::new_err(e.to_string())
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

/// Convert a [`Report`] into a Python dict.
fn report_dict<'py>(py: Python<'py>, report: &Report) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    let result = match report.claim {
        SolveResult::Sat => "sat",
        SolveResult::Unsat => "unsat",
        SolveResult::Unknown => "unknown",
    };
    d.set_item("result", result)?;
    d.set_item("checker", checker_label(report.verdict))?;
    d.set_item("theory", report.theory.to_string())?;

    match &report.model {
        Some(Model::Bool(values)) => {
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
            d.set_item("model", lits)?;
        }
        Some(Model::Named(pairs)) => {
            let named = PyDict::new(py);
            for (name, value) in pairs {
                named.set_item(name, value)?;
            }
            d.set_item("model", named)?;
        }
        None => d.set_item("model", py.None())?,
    }

    match &report.proof {
        Some(Proof::Drat(clauses)) => d.set_item("proof", clauses.clone())?,
        Some(Proof::Farkas(pairs)) => {
            let list: Vec<(usize, String)> =
                pairs.iter().map(|(i, m)| (*i, m.to_string())).collect();
            d.set_item("proof", list)?;
        }
        None => d.set_item("proof", py.None())?,
    }

    match &report.core {
        Some(core) => d.set_item("core", core.clone())?,
        None => d.set_item("core", py.None())?,
    }

    let stats = PyDict::new(py);
    stats.set_item("variables", report.stats.variables)?;
    stats.set_item("constraints", report.stats.constraints)?;
    stats.set_item("elapsed_ms", report.stats.elapsed.as_secs_f64() * 1000.0)?;
    d.set_item("stats", stats)?;
    Ok(d)
}

/// Solve `text` in `format` (`"auto"`, `"dimacs"`, `"smt2"` or `"mps"`).
///
/// Returns a dict with `result` (`"sat"`, `"unsat"` or `"unknown"`), `checker`,
/// `theory`, `model`, `proof` (DRAT clauses or Farkas pairs), `core` and `stats`.
/// Raises `ValueError` on malformed input.
#[pyfunction]
#[pyo3(signature = (text, format = "auto", fuel = 10_000_000, proof = false, explain = false))]
fn solve<'py>(
    py: Python<'py>,
    text: &str,
    format: &str,
    fuel: u64,
    proof: bool,
    explain: bool,
) -> PyResult<Bound<'py, PyDict>> {
    let explicit = parse_format(format)?;
    let format = api::resolve_format(explicit, None, text).map_err(to_py_err)?;
    let report = api::solve_str(text, format, &options(fuel, proof, explain)).map_err(to_py_err)?;
    report_dict(py, &report)
}

/// Solve a CNF given as a list of clauses, each a list of nonzero DIMACS literals.
///
/// `num_vars` defaults to the largest variable mentioned. Raises `ValueError` on a
/// literal of `0`.
#[pyfunction]
#[pyo3(signature = (clauses, num_vars = None, fuel = 10_000_000, proof = false, explain = false))]
fn solve_cnf(
    py: Python<'_>,
    clauses: Vec<Vec<i32>>,
    num_vars: Option<u32>,
    fuel: u64,
    proof: bool,
    explain: bool,
) -> PyResult<Bound<'_, PyDict>> {
    let mut max_var = 0u32;
    for clause in &clauses {
        for &lit in clause {
            if lit == 0 {
                return Err(PyValueError::new_err("literal 0 is not allowed"));
            }
            max_var = max_var.max(lit.unsigned_abs());
        }
    }
    let var_count = num_vars.unwrap_or(max_var).max(max_var);
    let mut text = format!("p cnf {} {}\n", var_count, clauses.len());
    for clause in &clauses {
        for lit in clause {
            text.push_str(&format!("{lit} "));
        }
        text.push_str("0\n");
    }
    let report =
        api::solve_str(&text, Format::Dimacs, &options(fuel, proof, explain)).map_err(to_py_err)?;
    report_dict(py, &report)
}

/// Check a proof against its problem without solving. Returns `"accept"`,
/// `"reject"` or `"inconclusive"`.
#[pyfunction]
#[pyo3(signature = (problem, proof, format = "auto"))]
fn check(problem: &str, proof: &str, format: &str) -> PyResult<&'static str> {
    let explicit = parse_format(format)?;
    let format = api::resolve_format(explicit, None, problem).map_err(to_py_err)?;
    let verdict = api::check_proof_text(problem, format, proof).map_err(to_py_err)?;
    Ok(checker_label(verdict))
}

/// The `tpt_solver` extension module.
#[pymodule]
fn tpt_solver(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(solve, m)?)?;
    m.add_function(wrap_pyfunction!(solve_cnf, m)?)?;
    m.add_function(wrap_pyfunction!(check, m)?)?;
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    Ok(())
}
