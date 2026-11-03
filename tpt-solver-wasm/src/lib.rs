//! WebAssembly bindings for the tpt-solver playground.
//!
//! Both functions return a JSON string in the same shape the command line prints with
//! `--output json`, so the browser page and the CLI report identically. Failures return
//! `{"error": "..."}`.
//!
//! The browser has no threads, so the portfolio is not available here: every solve is
//! sequential.

use tpt_solver::api::{self, Format, Options};
use wasm_bindgen::prelude::*;

/// Solve `input` and return the certified report as JSON.
///
/// `format` is `"auto"`, `"dimacs"`, `"smt2"` or `"mps"`. `fuel` caps the engine's
/// steps, so a hard instance returns `unknown` rather than freezing the page.
#[wasm_bindgen]
pub fn solve(input: &str, format: &str, fuel: f64) -> String {
    let options = Options {
        fuel: fuel.max(0.0) as u64,
        want_proof: true,
        ..Options::default()
    };
    let format = match explicit_format(format) {
        Ok(f) => f,
        Err(msg) => return error_json(&msg),
    };
    match api::resolve_format(format, None, input) {
        Ok(f) => match api::solve_str(input, f, &options) {
            Ok(report) => report.to_json(None),
            Err(e) => error_json(&e.to_string()),
        },
        Err(e) => error_json(&e.to_string()),
    }
}

/// Check a proof against its problem, without solving. Returns JSON with a
/// `checker` field: `accept`, `reject` or `inconclusive`.
#[wasm_bindgen]
pub fn check(problem: &str, format: &str, proof: &str) -> String {
    let format = match explicit_format(format) {
        Ok(explicit) => match api::resolve_format(explicit, None, problem) {
            Ok(f) => f,
            Err(e) => return error_json(&e.to_string()),
        },
        Err(msg) => return error_json(&msg),
    };
    match api::check_proof_text(problem, format, proof) {
        Ok(verdict) => {
            let label = if verdict.is_accept() {
                "accept"
            } else if verdict.is_reject() {
                "reject"
            } else {
                "inconclusive"
            };
            format!("{{\"checker\":\"{}\"}}", label)
        }
        Err(e) => error_json(&e.to_string()),
    }
}

fn explicit_format(name: &str) -> Result<Option<Format>, String> {
    match name {
        "auto" => Ok(None),
        other => Format::from_name(other)
            .map(Some)
            .ok_or_else(|| format!("unknown format '{other}'")),
    }
}

fn error_json(message: &str) -> String {
    let escaped = message
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n");
    format!("{{\"error\":\"{escaped}\"}}")
}
