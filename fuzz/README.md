# tpt-solver-fuzz

Continuous fuzzing targets for the [`tpt-solver`](https://crates.io/crates/tpt-solver) suite.
These are `cargo-fuzz` harnesses that hammer the untrusted parsers and engines with
untrusted, machine-generated input to surface panics, overflows, and (via the differential
oracle tests in the main workspace) soundness regressions.

Dual licensed under **MIT or Apache-2.0**, at your option — Copyright (c) 2026 TPT
Solutions.

> This crate is **not published** to crates.io (`publish = false`). It lives at the workspace
> root as its own detached cargo-fuzz workspace.

## Targets

| Target | Exercises |
|--------|-----------|
| `dimacs` | `tpt_solver::parsers::dimacs::parse_dimacs` — DIMACS CNF parsing robustness. |
| `smtlib2` | `parse_script` → `to_lra` / `to_cnf` / `to_bv` / `to_array` — SMT-LIB2 lowerings. |
| `mps` | `tpt_solver::parsers::mps::parse_mps` — LP-MPS parsing robustness. |

## Running

```sh
# Requires a nightly toolchain (cargo-fuzz needs it).
cargo +nightly fuzz run dimacs
cargo +nightly fuzz run smtlib2
cargo +nightly fuzz run mps

# Short smoke-test for CI:
cargo +nightly fuzz run dimacs -- -max_total_time=30
```

Each target feeds fuzzed bytes straight into the corresponding parser. The parsers are
expected to return `Err` on malformed input, never to panic or overflow — a crash here is a
real bug in the periphery crate.

## Differential soundness

Beyond parser crashes, the suite's *differential* tests (in the main `tpt-solver` crate) push
random and fuzzed problems through the engine and compare the engine's claim against
exhaustive brute-force enumeration and against Z3, trusting only `Accept`ed answers. Those
live in the published workspace; this crate covers the parser-input surface that feeds them.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE))
* MIT license ([LICENSE-MIT](../LICENSE-MIT))

at your option.
