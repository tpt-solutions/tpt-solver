# tpt-solver

A high-performance constraint, SAT, and SMT solver suite in pure Rust, built on a
**certificate architecture**: an untrusted, aggressively-optimized search engine
paired with a small, independently-verified checker kernel that revalidates every
answer.

Dual licensed under **MIT or Apache-2.0**, at your option — Copyright (c) 2026 TPT
Solutions.

## The idea

Instead of asking one large, performance-critical crate to be both fast and formally
proven, tpt-solver isolates trust into a small, dedicated checker
([`tpt-solver-check`](tpt-solver-check)) that revalidates every answer, and lets the
search engine ([`tpt-solver-core`](tpt-solver-core)) be as complex and fast as it
needs to be. This is the same trusted-kernel principle behind LCF-style proof
assistants and behind how SAT competitions certify solver output today (DRAT/LRAT
proofs, checked by tools like `drat-trim` and the machine-verified `cake_lpr`).

- **SAT / UNSAT** — verified via LRAT/RUP certificate checking (Phase 2) and, for SAT
  answers, by substituting the model back into the original formula.
- **LRA** — verified via Farkas certificates (Phase 3).
- The checker reports **three** outcomes — `Accept` / `Reject` / `Inconclusive` — so a
  real engine bug is never confused with a checker resource problem.

## Workspace layout

| Crate | Role | Trust |
|-------|------|-------|
| `tpt-solver-core` | Search engine (CDCL, DPLL(T), Simplex) | Untrusted, `no_std` + `alloc`, zero deps |
| `tpt-solver-check` | Certificate checker kernel | **Trusted**, `no_std` + `alloc`, zero deps |
| `tpt-solver` | Parsers, CLI, e-graph preprocessing, glue | Periphery, MIT deps allowed |

## Status

Phases 0–6 (SAT/LRA/BV/array theories, certificate checking, parsers, portfolio
solving, CLI proof and core export flags) are complete; Phase 7 is in progress. See
`docs/internal/todo.md` for the full phased plan and what's left.

## Building and testing

```sh
cargo build --workspace
cargo test  --workspace
```

## Installing

```sh
cargo install --path tpt-solver
```

This builds the `tpt-solver` binary from source. There is no crates.io release
yet. Prebuilt binaries for Linux, macOS and Windows are attached to tagged
(`v*`) GitHub Releases by the `release` workflow.

## CLI usage

```sh
tpt-solver                            # run the built-in demo
tpt-solver FILE.cnf                   # DIMACS CNF, solved by certified CDCL
tpt-solver FILE.smt2                  # SMT-LIB2 (LRA, BV, arrays, or propositional)
tpt-solver FILE.mps                   # LP-MPS, feasibility only (the objective is dropped)
tpt-solver FILE.cnf.gz                # gzip input, detected by content
tpt-solver - --format dimacs          # read standard input
tpt-solver FILE --output competition  # `s`/`v` lines, exit codes 10 (SAT), 20 (UNSAT), 0
tpt-solver FILE --output json         # one JSON object on stdout
tpt-solver FILE --emit-proof P        # on UNSAT, write the checked certificate to P
tpt-solver FILE --explain             # on UNSAT, list the clauses or constraints needed
tpt-solver FILE --timeout 5 --fuel N  # wall-clock and step limits; expiry gives `unknown`
tpt-solver FILE --parallel N          # race N diverse CDCL workers (CNF only)
tpt-solver check PROBLEM PROOF        # check a proof file without solving
tpt-solver bench --seeds 5            # random 3-SAT ladder, CSV on stdout
tpt-solver completions bash           # shell completion script
tpt-solver man                        # man page
```

Every printed result is what the trusted checker (`tpt-solver-check`) accepted. Run
`tpt-solver --help` for every flag. Exit codes in the default mode: `0` for an
accepted answer or `unknown`, `1` when the checker refused a SAT or UNSAT claim, and
`2` for usage, I/O, or parse errors.

The proof formats are described in
[`docs/src/proof-format.md`](docs/src/proof-format.md). The user guide is in `docs/`,
and it can be built with `mdbook build docs`.

For using the crates as a library, see
[`tpt-solver/examples/lib_usage.rs`](tpt-solver/examples/lib_usage.rs) (run with
`cargo run --example lib_usage`) and the [library chapter](docs/src/library.md).

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
