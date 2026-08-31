# Changelog

All notable changes to the `tpt-solver-core` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — 2026-08-31

Initial public workspace release of the three-crate `tpt-solver` suite.

### Added

- **Exact math.** A custom `i128`-backed `Rational` (`rational`) that is
  differentially fuzzed against `num-rational` as a dev-dependency-only oracle, never a
  runtime dependency.
- **Unified IR** (`ir`): `VarId(NonZeroU32)` / `ClauseId(NonZeroU32)` newtypes,
  generation/session-tagged phantom types that prevent stale-ID reuse across incremental
  push/pop, and a typestate for the solver lifecycle (`Solver<Solving>` vs `Solver<Model>`).
- **Arena + trail-stack memory** (`memory`) for O(1) backtracking and **fuel system**
  (`fuel`) bounding every loop — depletion returns `Unknown` rather than looping or
  panicking.
- **CDCL SAT engine** (`sat`): two-watched literals, VSIDS branching, restart strategy,
  clause deletion, first-UIP conflict analysis, and LRAT proof emission.
- **QF_LRA theory** (`lra`): Fourier–Motzkin (UNSAT/Farkas certificate) plus a two-phase
  Simplex `lra_model` for model extraction.
- **Bit-vector theory** (`bv`): fixed-width (≤64-bit) word-level fragment solved by eager
  bit-blasting onto the certified CDCL engine.
- **Array theory** (`array`): QF_AX ground positive equalities over `select`/`store`, solved
  by congruence closure modulo the select-over-store axioms, with ban-and-retry on
  invalidated walkthrough assumptions.
- **Cooperative cancellation** (`cancel`): the single shared mutable flag the portfolio
  introduces, polled once per search step and model-checked under `loom`.
- **Kani proof harnesses** (`kani_harnesses`, `cfg(kani)`) on fuel, literal-packing, and
  trail/arena backtracking.
- **`no_std` + `alloc`, zero runtime dependencies** by default; `#![deny(clippy::unwrap_used,
  clippy::panic)]` lint gate; `loom` and `std` features.

### Fixed

- CDCL two-watched-literal invariant corrupted by missing literal dedupe/tautology detection
  on clause literals (soundness).
- Simplex Phase-1 artificial columns re-entering the basis as if cost 0 (soundness).
- `cancel_until` shrinking the trail below the propagation head (soundness).
- `reduce_db` rebuilding watchers on already-false literals so surviving clauses were never
  revisited (soundness).
- `analyze` collecting current-level literals into the learnt clause, producing
  non-asserting clauses (soundness).
- Two further `analyze` first-UIP bugs exposed by the BV certification tests: marking
  satisfied literals `seen`, and an index-0 resolution skip that dropped a real antecedent
  literal, yielding a wrong-polarity unit clause (soundness).

[0.1.0]: https://github.com/tpt-solutions/tpt-solver/releases/tag/v0.1.0
