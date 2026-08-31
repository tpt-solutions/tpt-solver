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

Phases 0–5 (SAT/LRA/BV/array theories, certificate checking, parsers, portfolio
solving) are complete; see `todo.md` for the full phased plan and what's left.

## Building and testing

```sh
cargo build --workspace
cargo test  --workspace
```

## Installing

```sh
cargo install --path tpt-solver
```

This builds the `tpt-solver` binary from source (no crates.io publish yet, no
prebuilt release binaries other than what the `release` GitHub Actions workflow
attaches to tagged releases).

## CLI usage

```sh
tpt-solver                          # run built-in demo (reference + CDCL, both certified)
tpt-solver FILE.cnf                 # parse a DIMACS CNF, solve with CDCL, certify answer
tpt-solver FILE.smt2                # parse an SMT-LIB2 script, solve (LRA or SAT), certify
tpt-solver FILE.mps                 # parse a free-format LP-MPS file, solve the LRA
                                     # feasibility system (no objective optimization), certify
tpt-solver FILE.cnf --fuel N        # step budget before giving up with `Unknown`
tpt-solver FILE.cnf --parallel N    # race N diverse CDCL workers (DIMACS only)
tpt-solver FILE.cnf --emit-proof P  # on UNSAT, dump the checked certificate to file P
tpt-solver FILE.smt2 --explain      # on UNSAT (LRA only), print the implicated constraints
tpt-solver --bench                  # local 3-SAT performance ladder
```

Every printed verdict is what the trusted checker (`tpt-solver-check`) actually
accepted, not just what the engine claimed — run `tpt-solver --help` for the full
flag reference.

For using the crates as a library instead of through the CLI, see
[`tpt-solver/examples/lib_usage.rs`](tpt-solver/examples/lib_usage.rs) (run with
`cargo run --example lib_usage`).

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
