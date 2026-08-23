#![no_main]
//! Fuzz target for the LP-MPS parser. Parsers are the highest-value fuzzing surface
//! of the suite: malformed/truncated/malicious input should never panic or unwind
//! unsafely. Run with `cargo +nightly fuzz run mps`.

use libfuzzer_sys::fuzz_target;
use tpt_solver::parsers::mps::parse_mps;
use tpt_solver::reference::solve_and_check_lra;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    // The parser must never panic on arbitrary bytes that happen to be valid UTF-8.
    if let Ok(prob) = parse_mps(text) {
        // And solving the parsed problem must also be panic-free; the result is
        // validated by the trusted checker but we do not assert on it here.
        let _ = solve_and_check_lra(&prob.constraints, 1_000_000);
    }
});
