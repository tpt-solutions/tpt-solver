# tpt-solver-core

The **untrusted** solving engine of the [`tpt-solver`](https://crates.io/crates/tpt-solver)
suite: an aggressively-optimized constraint, SAT, and SMT search engine (CDCL, DPLL(T),
Simplex, Fourier–Motzkin) whose answers are **never** trusted blindly — every result is
revalidated by the companion [`tpt-solver-check`](https://crates.io/crates/tpt-solver-check)
trusted kernel.

Dual licensed under **MIT or Apache-2.0**, at your option — Copyright (c) 2026 TPT
Solutions.

## Why this crate exists

Instead of asking one large, performance-critical crate to be both fast *and* formally
proven, `tpt-solver` isolates trust into a small, dedicated checker and lets this engine be
as complex and fast as it needs to be. This is the same trusted-kernel principle behind
LCF-style proof assistants and behind how SAT competitions certify solver output today
(DRAT/LRAT proofs, checked by tools like `drat-trim` and the machine-verified `cake_lpr`).

This crate is therefore **fast and untrusted**: it may be wrong, but it is *honest*. On any
path where it cannot guarantee a correct answer it returns `Unknown` (via the fuel system)
rather than guessing, panicking, or looping forever.

## Design constraints

* **`no_std` + `alloc`, zero runtime dependencies by default.** The `std` feature (on by
  default) simply lifts the `no_std` restriction so `std`-only dev tooling (e.g.
  `proptest`) can be used in tests. A normal build pulls in no third-party crates.
* **`#![deny(clippy::unwrap_used, clippy::panic)]`.** The engine must never panic or unwrap
  on a fallible path; everything returns `Result`/`Option` or consumes *fuel* and returns
  `Unknown`.
* **Built-in fuel system.** Every loop consumes fuel and returns `Unknown` on depletion
  rather than looping forever or panicking.

## Modules

| Module | Responsibility |
|--------|----------------|
| `ir` | Unified intermediate representation: `VarId`/`ClauseId` newtypes, session-tagged phantom types, and typestate for the solver lifecycle (`Solver<Solving>` vs `Solver<Model>`). |
| `rational` | A custom `i128`-backed exact `Rational`. Differentially fuzzed against `num-rational` as a dev-dependency-only oracle (never a runtime dependency of this `no_std` crate). |
| `fuel` | The fuel accounting system that bounds every loop. |
| `memory` | Arena + trail-stack memory for O(1) backtracking. |
| `cancel` | Cooperative cancellation flag (`Arc<AtomicBool>`) polled once per search step; the only shared mutable state the portfolio introduces, model-checked under `loom`. |
| `sat` | CDCL SAT engine: two-watched literals, VSIDS, restarts, clause deletion, first-UIP analysis, LRAT proof emission. |
| `lra` | Quantifier-free linear real arithmetic (QF_LRA): Fourier–Motzkin (UNSAT/Farkas) plus a two-phase Simplex `lra_model` for model extraction. |
| `bv` | Fixed-width (≤64-bit) bit-vector theory via eager bit-blasting onto the certified CDCL engine. |
| `array` | QF_AX ground positive equalities over `select`/`store`, solved by congruence closure modulo the select-over-store axioms. |
| `engine` | The top-level `SolveResult` (`Sat`/`Unsat`/`Unknown`) and the orchestration types tying the theories together. |
| `kani_harnesses` | Kani proof harnesses (only compiled under `cfg(kani)`) for fuel, literal-packing, and trail/arena backtracking. |

## Usage

```toml
[dependencies]
tpt-solver-core = "0.1"
```

A minimal DIMACS-style solve, with a fuel budget:

```rust
use tpt_solver_core::sat::solve_cnf;
use tpt_solver_core::engine::SolveResult;

let var_count = 3u32;
let clauses = vec![
    vec![1, 2],
    vec![-1, 3],
    vec![-2, 3],
    vec![-3],
];

match solve_cnf(var_count, &clauses, 1_000_000) {
    SolveResult::Sat => println!("satisfiable"),
    SolveResult::Unsat => println!("unsatisfiable"),
    SolveResult::Unknown => println!("ran out of fuel"),
}
```

Bit-vector and array problems go through `bv::solve_bv` / `array::solve_arrays`, and LRA
through `lra::fourier_motzkin` / `lra::lra_model`. **None of these results should be trusted
on their own** — hand them to `tpt-solver-check` for revalidation.

## Cargo features

| Feature | Default | Meaning |
|---------|---------|---------|
| `std` | on | Lifts the `no_std` restriction; required only for `std`-only dev tooling. |
| `loom` | off | Pulls in `loom` and enables the `cfg(loom)` model-check of the portfolio cancellation flag. |

## Building and testing

```sh
cargo build -p tpt-solver-core
cargo test  -p tpt-solver-core

# Model-check the concurrency under loom:
cargo test -p tpt-solver-core --features loom

# Kani proofs (requires the Kani toolchain):
cargo kani -p tpt-solver-core
```

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE))
* MIT license ([LICENSE-MIT](../LICENSE-MIT))

at your option.
