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

Phase 0 (project setup) and the Phase 1 foundation (IR newtypes with session tagging,
typestate lifecycle, arena/trail memory, fuel system, RUP checker, reference solver)
are in place. See `todo.md` for the full phased plan.

## Building and testing

```sh
cargo build --workspace
cargo test  --workspace
```

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
