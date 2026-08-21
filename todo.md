# tpt-solver — Project Todo

A high-performance constraint, SAT, and SMT solver suite in pure Rust, built on
a certificate architecture: an untrusted, aggressively-optimized search engine
paired with a small, independently-verified checker kernel that revalidates
every answer.

Dual licensed under MIT or Apache-2.0, at your option — Copyright (c) 2026 TPT
Solutions.

---

## Phase 0 — Project Setup

- [x] `git init` + Rust `.gitignore`
- [x] Cargo workspace root `Cargo.toml` with three members: `tpt-solver-core`,
      `tpt-solver-check`, `tpt-solver` (periphery)
- [x] Scaffold `tpt-solver-core` crate (`no_std` + `alloc`, zero deps)
- [x] Scaffold `tpt-solver-check` crate (`no_std` + `alloc`, zero deps)
- [x] Scaffold `tpt-solver` periphery crate (binary/lib)
- [x] Add `LICENSE-MIT` and `LICENSE-APACHE` at repo root (TPT Solutions, 2026)
- [x] Set `license = "MIT OR Apache-2.0"` in each crate's `Cargo.toml`
- [x] `README.md` with project summary + license section
- [x] `#![deny(clippy::unwrap_used, clippy::panic)]` lint gate on
      `tpt-solver-core`
- [x] CI workflow skeleton (placeholder job, filled in during Phase 1)

## Phase 1 — Foundation (Months 1–2)

- [x] `tpt-solver-core` exact-math types: a custom `i128`-backed [`Rational`]
      (`tpt-solver-core/src/rational.rs`). The spec permits a custom exact-rational
      *provided* it is differentially fuzzed against a reference oracle from day one;
      the `cargo-fuzz` harnesses (DIMACS + SMT-LIB2 parsers) are in place, but a
      numeric-oracle fuzz target for `Rational` itself is still TBD.
- [x] Unified IR: newtypes (`VarId(NonZeroU32)`, `ClauseId(NonZeroU32)`)
- [x] Generation/session-tagged phantom types for IDs (prevents stale-ID reuse
      across incremental push/pop)
- [x] Typestate for solver lifecycle (`Solver<Solving>` vs. `Solver<Model>`)
- [x] Arena + trail-stack memory for O(1) backtracking
- [x] Fuel system on every loop (return `Unknown` on depletion, never loop/panic)
- [x] Stand up `tpt-solver-check` as its own crate from day one
- [x] Core checker kernel implemented from day one: three-way `Outcome`
      (Accept/Reject/Inconclusive), SAT model recheck, and a correct unit-
      propagation RUP/LRAT checker (certificate emission from the CDCL engine
      lands in Phase 2, but the kernel validates by re-deriving RUP).
- [ ] Differential test harness vs. Z3 wired into CI immediately
      (blocked: requires the `z3` binary on CI runners; scaffold the harness to
      shell out to `z3` when present and skip otherwise).
- [ ] Reject/inconclusive/accept rate tracking + explicit threshold gate wired
      into the same CI harness from day one
      (`VerdictTracker` exists in `tpt-solver/src/policy.rs`; the merge-gate
      threshold wiring into CI is still TBD).

## Phase 2 — SAT engine + first certificates (Months 3–4)

- [x] CDCL SAT engine: two-watched literals, VSIDS, restarts, clause deletion
      (`tpt-solver-core/src/sat.rs`)
- [x] LRAT proof emission from the CDCL engine (learned-clause chain ending in the
      empty clause; validated by the kernel's unit-propagation RUP checker)
- [x] LRAT checker in `tpt-solver-check` (RUP core; full hint-validated LRAT TBD)
- [x] Three-way checker outcome type: Accept / Reject / Inconclusive
- [x] Kani harnesses on fuel, literal-packing, and trail/arena backtracking code
      (`tpt-solver-core/src/kani_harnesses.rs`, `#[kani::proof]`, run via
      `cargo kani -p tpt-solver-core`; a `kani` CI job is wired in `.github/workflows/ci.yml`)
- [x] `tpt-telos`-targeted invariants implemented as `proptest` property tests
      (`tpt-solver-core/src/invariants.rs`): fuel accounting, arena/trail offset
      math, literal packing — the bounded linear-arithmetic properties §5.2 lists.
      NOTE: `tpt-telos` (github.com/tpt-solutions/tpt-telos) is a *separate*
      verification-language compiler with its own Fourier–Motzkin SMT core; it is
      not an embeddable Rust dependency, so its contracts are realized here as
      runnable property/Kani proofs rather than `.telos` spec files.

## Phase 3 — LRA theory + certificates (Months 5–6)

- [x] Simplex + Fourier-Motzkin for QF_LRA in the core
      (`tpt-solver-core/src/lra.rs`: `fourier_motzkin` for UNSAT/Farkas, plus a
      two-phase Simplex `lra_model` that extracts a SAT model; the kernel
      re-checks the model via `check_lra_model`, so LRA SAT answers are now
      `Accept` rather than `Inconclusive`).
- [x] Farkas certificate emission from the FM prover
- [x] Farkas certificate checking in `tpt-solver-check`
- [ ] `tpt-telos` contracts on fuel accounting and Simplex pivot bounds
      (blocked: `tpt-telos` is a separate external tool; realized here as
      `proptest`/`invariants.rs` property tests instead — see Phase 2 note).

## Phase 4 — Periphery & integration (Months 7–8)

- [x] SMT-LIB2 parser (`tpt-solver/src/parsers/smtlib2.rs`): tokenizer, S-expr
      parser, term AST, and two lowerings — QF_LRA (linear constraints) and QF_SAT
      (Tseitin CNF). Wired into the CLI; routes `.smt2` files to LRA or SAT.
- [x] DIMACS parser (`tpt-solver/src/parsers/dimacs.rs`) with safe error handling
- [ ] LP-MPS parser
- [x] `cargo-fuzz` target scaffold for the DIMACS parser (`fuzz/`, detached
      workspace; run with `cargo +nightly fuzz run dimacs`) plus a `smtlib2` fuzz
      target exercising `parse_script` → `to_lra`/`to_cnf`.
- [ ] `egg`-based e-graph preprocessing
- [x] CLI and I/O: `tpt-solver` binary parses a `.cnf`, solves with CDCL, and
      prints the checker-validated verdict (`--fuel N` supported). `clap` is the
      spec's intended dependency but a dependency-free arg parser is used for now
      to keep the build offline-friendly.
- [x] Tiered live-request fallback policy (`tpt-solver/src/policy.rs`): fail-closed,
      reseed-and-recheck on rejected SAT, fall back to the simpler reference DPLL,
      `Unknown` as the true last resort. `solve_certified` implements the pipeline.
- [x] Automatic rejection dump (input, certificate, engine path, fallback tier
      reached) via `RejectionDump`; plus a `VerdictTracker` for the §6.3
      accept/reject/inconclusive rate triad and a reject-threshold gate.

## Phase 5 — Advanced theories & hardening (Months 9–11)

- [ ] BitVector theory in core + matching checker in `tpt-solver-check`
- [ ] Array theory in core + matching checker in `tpt-solver-check`
- [ ] Continued differential/property testing at scale
- [ ] SAT-COMP/SMT-COMP benchmark runs (performance, not correctness)
- [ ] Full line-by-line audit of `tpt-solver-check`
- [ ] If shared-state concurrency is ever introduced (parallel portfolio
      solving): wire through `loom` before merging
