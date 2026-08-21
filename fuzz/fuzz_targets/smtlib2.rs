#![no_main]
//! Fuzz target for the SMT-LIB2 parser. Parsers are the highest-value fuzzing
//! surface of the suite: malformed/truncated/malicious input should never panic or
//! unwind unsafely. Run with `cargo +nightly fuzz run smtlib2`.

use libfuzzer_sys::fuzz_target;
use tpt_solver::parsers::smtlib2::parse_script;
use tpt_solver::reference::{solve_and_check_cdcl, solve_and_check_lra};

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    // The parser must never panic on arbitrary bytes that happen to be valid UTF-8.
    let Ok(script) = parse_script(text) else {
        return;
    };
    // Lowering + solving must likewise be panic-free; the trusted checker validates
    // any answer, so we only assert here that nothing unwinds.
    if let Ok(prob) = script.to_lra() {
        let _ = solve_and_check_lra(&prob.constraints, 1_000_000);
    }
    if let Ok(problem) = script.to_cnf() {
        let _ = solve_and_check_cdcl(&problem, 1_000_000);
    }
});
