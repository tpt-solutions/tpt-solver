# tpt-solver

The **periphery** of the [`tpt-solver`](https://crates.io/crates/tpt-solver) suite: parsers,
a CLI, e-graph preprocessing, and the integration glue that ties the untrusted
[`tpt-solver-core`](https://crates.io/crates/tpt-solver-core) engine to the trusted
[`tpt-solver-check`](https://crates.io/crates/tpt-solver-check) kernel.

Dual licensed under **MIT or Apache-2.0**, at your option — Copyright (c) 2026 TPT
Solutions.

## What this crate is

`tpt-solver` is the part of the suite you actually *run* and *feed files to*. The core engine
and the checker kernel forbid dependencies to keep the trusted boundary small; this crate is
the layer that is allowed MIT-compatible dependencies (e.g. `clap`, `proptest`) that the
zero-dependency crates forbid.

## Modules

| Module | Responsibility |
|--------|----------------|
| `parsers::dimacs` | Safe DIMACS CNF parser. |
| `parsers::smtlib2` | SMT-LIB2 tokenizer, S-expression parser, term AST, and lowerings to QF_LRA, QF_BV, QF_AX, and QF_SAT (Tseitin CNF). |
| `parsers::mps` | Free-format LP-MPS (`ROWS`/`COLUMNS`/`RHS`/`RANGES`/`BOUNDS`/`ENDATA`) parser that lowers to the same `LraProblem` the SMT-LIB2 LRA path uses (feasibility only — the objective row is dropped). |
| `egraph` | In-house, dependency-free e-graph Boolean-fragment preprocessing (equality saturation over `and`/`or`/`not`/`xor`/`iff`/`ite`) bounded like every other loop in the suite; verified by truth-table equivalence, not just a re-solve comparison. |
| `policy` | Tiered, fail-closed live-request fallback (`solve_certified`): reseed-and-recheck on rejected SAT, fall back to the reference DPLL, then `Unknown` as the true last resort. `solve_certified_portfolio` gives the parallel path the same policy. |
| `portfolio` | Parallel portfolio SAT solving: diverse CDCL workers race the same CNF on OS threads behind a cooperative-cancellation flag. |
| `reference` | Reference DPLL solver and the end-to-end `solve_and_check_*` integration entry points (CDCL, LRA, BV, arrays) that return a `(claim, verdict)` pair. |

The `tpt_solver::core` and `tpt_solver::check` re-exports point at the engine and kernel
crates respectively, so downstream code can depend on one crate.

## CLI

```text
tpt-solver                 # run the built-in demo (reference + CDCL, both certified)
tpt-solver FILE.cnf        # parse DIMACS CNF, solve with CDCL, certify the answer
tpt-solver FILE.smt2       # parse SMT-LIB2, solve (LRA/BV/AX/SAT), certify
tpt-solver FILE.mps        # parse LP-MPS, solve the LRA feasibility system, certify
tpt-solver FILE.cnf --fuel N
tpt-solver FILE.cnf --parallel N   # race N diverse CDCL workers (DIMACS only)
tpt-solver --bench         # offline random 3-SAT ladder through the certified pipeline
```

Every printed verdict is what the trusted checker (`tpt-solver-check`) returned — that is the
only answer that may be trusted. A richer `clap`-based CLI (`--help`/`--version`,
`--emit-proof`, `--explain`) is planned for a later phase.

## Usage as a library

```toml
[dependencies]
tpt-solver = "0.1"
```

```rust
use tpt_solver::reference::solve_and_check_cdcl;
use tpt_solver::parsers::dimacs::parse_dimacs;
use tpt_solver::engine::SolveResult;
use tpt_solver::check::outcome::Outcome;

let input = "p cnf 3 4\n1 2 0\n-1 3 0\n-2 3 0\n-3 0";
let problem = parse_dimacs(input).expect("parse");
let (claim, verdict) = solve_and_check_cdcl(&problem, 1_000_000);
assert_eq!(claim, SolveResult::Unsat);
assert_eq!(verdict, Outcome::Accept);
```

## Cargo features

| Feature | Default | Meaning |
|---------|---------|---------|
| `std` | on | Standard-library support. |

## Building and testing

```sh
cargo build -p tpt-solver
cargo test  -p tpt-solver

# Differential lane vs Z3 (no-ops if `z3` is not on PATH, so offline runs stay green):
cargo test  -p tpt-solver
```

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE))
* MIT license ([LICENSE-MIT](../LICENSE-MIT))

at your option.
