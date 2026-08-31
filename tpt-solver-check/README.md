# tpt-solver-check

The **trusted kernel** of the [`tpt-solver`](https://crates.io/crates/tpt-solver) suite: a
small, independently-checkable crate that revalidates *every* answer produced by the
untrusted [`tpt-solver-core`](https://crates.io/crates/tpt-solver-core) engine.

Dual licensed under **MIT or Apache-2.0**, at your option — Copyright (c) 2026 TPT
Solutions.

## Why this crate exists

This crate is deliberately tiny. It is the *only* place whose correctness the whole
system's answers rely on, so it is kept as small and as self-contained as possible
(`no_std` + `alloc`, zero dependencies), and it is the target of formal contracts
(`tpt-telos`).

It never trusts the engine. Every answer from `tpt-solver-core` is revalidated here
independently:

* **UNSAT** — via a certificate checker: **LRAT** for SAT-propositional (RUP core) and
  **Farkas** for LRA, verified clause-by-clause or coefficient-by-coefficient against the
  original problem.
* **SAT** — by substituting the returned assignment back into the original formula and
  checking satisfaction. This alone catches the overwhelming majority of "wrong SAT answer"
  bugs at near-zero cost.

## The three-way outcome

The checker reports one of three outcomes (`outcome::Outcome`) — never a bare boolean — so
that a real solver bug (`Reject`) is never confused with a checker resource problem
(`Inconclusive`):

* `Accept` — the checker independently reproduced and validated the engine's claim.
* `Reject` — the engine's claim is demonstrably wrong; treat it as a bug report.
* `Inconclusive` — the checker could not decide (e.g. a too-short model it refuses to
  zero-pad). Fail-closed: the answer is *not* trusted.

## Modules

| Module | Responsibility |
|--------|----------------|
| `outcome` | The three-way `Outcome` (`Accept` / `Reject` / `Inconclusive`) type and rate tracking. |
| `sat` | SAT model recheck plus the RUP/LRAT unit-propagation checker. |
| `lrat` | LRAT proof checking: clause-by-clause RUP re-derivation against the original clauses. |
| `lra` | Farkas certificate checking and SAT model recheck for QF_LRA. |
| `bv` | Independently-written bit-vector model evaluator and UNSAT certificate checker. |
| `array` | Congruence-closure certificate replay with the kernel's own union-find for QF_AX. |

## Usage

```toml
[dependencies]
tpt-solver-check = "0.1"
tpt-solver-core = "0.1"
```

```rust
use tpt_solver_core::sat::solve_cnf;
use tpt_solver_core::engine::SolveResult;
use tpt_solver_check::sat::check_cdcl_answer;
use tpt_solver_check::outcome::Outcome;

let clauses = vec![vec![1, 2], vec![-1, 3], vec![-2, 3], vec![-3]];
let claim = solve_cnf(3, &clauses, 1_000_000);

// `check_cdcl_answer` re-derives the UNSAT proof (or re-checks the SAT model)
// independently of the engine that produced `claim`.
let verdict = check_cdcl_answer(3, &clauses, &claim);
assert_eq!(verdict, Outcome::Accept);
```

Always gate on `Outcome::Accept` before trusting an answer. `Reject` means the engine was
wrong; `Inconclusive` means the kernel could not decide and the answer must not be trusted.

## Cargo features

| Feature | Default | Meaning |
|---------|---------|---------|
| `std` | on | Lifts the `no_std` restriction; required only for `std`-only dev tooling. |

## Building and testing

```sh
cargo build -p tpt-solver-check
cargo test  -p tpt-solver-check
```

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE))
* MIT license ([LICENSE-MIT](../LICENSE-MIT))

at your option.
