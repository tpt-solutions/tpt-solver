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
      the `cargo-fuzz` harnesses (DIMACS + SMT-LIB2 parsers) are in place, and
      `rational.rs`'s `oracle` proptest module now differentially checks
      add/mul/neg/cmp/checked_div/is_zero/is_negative against `num-rational`'s
      arbitrary-precision `Ratio` (a dev-dependency-only oracle, never a runtime
      dependency of this `no_std` crate).
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
- [x] Differential test harness vs. Z3 wired into CI immediately
      (`differential-z3` job in `.github/workflows/ci.yml` installs `z3` via apt
      and runs `differential_vs_z3_when_available`, which shells out to `z3` on
      `PATH` and no-ops elsewhere so local/offline runs stay green).
- [x] Reject/inconclusive/accept rate tracking + explicit threshold gate wired
      into the same CI harness from day one
      (`VerdictTracker` + `differential_corpus_agrees_and_is_accepted` gate the
      reject rate at 0.0 on every `cargo test`, which runs in the `build-and-test`
      CI job). Found and fixed two real soundness bugs while getting this gate to
      actually pass: `tpt-solver-core/src/sat.rs` didn't dedupe/detect-tautology
      on clause literals, so a duplicated literal corrupted the two-watched-literal
      invariant; `tpt-solver-core/src/lra.rs`'s two-phase Simplex let artificial
      columns (Phase-1 cost 1) re-enter the basis as if their cost were 0. Also
      fixed pre-existing `cargo fmt`/`cargo clippy -D warnings` failures across the
      workspace so the CI gates this item depends on can actually go green.

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
- [x] `tpt-telos` contracts on fuel accounting and Simplex pivot bounds
      (blocked: `tpt-telos` is a separate external tool; realized here as
      `proptest`/`invariants.rs` property tests instead — see Phase 2 note.
      `lra_model_terminates_and_is_self_consistent` in
      `tpt-solver-core/src/invariants.rs` covers the Simplex side and caught the
      artificial-variable re-entry bug fixed in Phase 1 above).

## Phase 4 — Periphery & integration (Months 7–8)

- [x] SMT-LIB2 parser (`tpt-solver/src/parsers/smtlib2.rs`): tokenizer, S-expr
      parser, term AST, and two lowerings — QF_LRA (linear constraints) and QF_SAT
      (Tseitin CNF). Wired into the CLI; routes `.smt2` files to LRA or SAT.
- [x] DIMACS parser (`tpt-solver/src/parsers/dimacs.rs`) with safe error handling
- [x] LP-MPS parser (`tpt-solver/src/parsers/mps.rs`): free-format MPS (`ROWS`,
      `COLUMNS`, `RHS`, `RANGES`, `BOUNDS`, `ENDATA`); lowers to the same
      `LraProblem` the SMT-LIB2 LRA path uses, so it's solved via the existing
      FM/Simplex engine and re-checked by the kernel. `N` rows (incl. the
      objective) are parsed but dropped — this is a feasibility engine, not an LP
      optimizer. Wired into the CLI (`tpt-solver FILE.mps`) and given a
      `cargo-fuzz` target (`fuzz/fuzz_targets/mps.rs`).
- [x] `cargo-fuzz` target scaffold for the DIMACS parser (`fuzz/`, detached
      workspace; run with `cargo +nightly fuzz run dimacs`) plus a `smtlib2` fuzz
      target exercising `parse_script` → `to_lra`/`to_cnf`.
- [x] `egg`-based e-graph preprocessing (`tpt-solver/src/egraph.rs`): equality
      saturation over the Boolean fragment (`and`/`or`/`not`/`xor`/`iff`/`ite`)
      that `Script::to_cnf` Tseitin-encodes, wired in as a pass before encoding.
      Bounded like every other loop in the suite (node/iteration limits, no
      unbounded saturation). Verified with a direct semantic check, not just a
      re-solve comparison: a `proptest` generates random small formulas and
      checks the original and simplified terms agree on *every* assignment of
      their variables (truth-table equivalence), plus targeted unit tests for
      individual rewrites (double-negation, annihilators, etc).
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

- [x] BitVector theory in core + matching checker in `tpt-solver-check`
      (`tpt-solver-core/src/bv.rs` + `tpt-solver-check/src/bv.rs`). Fragment:
      fixed-width (≤64-bit) word-level terms over var/const/not/neg/and/or/
      xor/add/sub, constant shifts, concat and extract; assertions are unsigned
      equality and `<`. Decision procedure is eager **bit-blasting onto the
      existing certified CDCL** (`sat::solve_cnf`) — SAT answers are decoded to
      word models and re-certified by the kernel's *independently written*
      evaluator (`check_bv_model`; short models are `Inconclusive`, never
      zero-padded); UNSAT ships the blast plus the CDCL LRAT proof, revalidated
      by `check_bv_unsat` via the existing RUP checker. Documented residual
      trust surface: the encoder circuits are not re-derived by the kernel;
      that gap is closed by differential brute-force property tests (`oracle`
      module: engine verdict must agree with exhaustive enumeration on random
      small-width problems, both directions).
- [x] Array theory in core + matching checker in `tpt-solver-check`
      (`tpt-solver-core/src/array.rs` + `tpt-solver-check/src/array.rs`).
      Fragment: QF_AX ground **positive equalities** over element terms
      (var/const/select) and array terms (avar/constarray/store) — no
      disequalities yet, so every UNSAT manifests as two distinct constants
      proven equal, exactly what the certificate captures. Engine: congruence
      closure modulo the select-over-store axioms (same-index, walkthrough,
      constant-array, congruence), fuel-bounded; walkthrough assumptions that
      get invalidated by later index merges trigger a ban-and-retry so shipped
      facts always satisfy their preconditions. Certificates list axiom
      instances whose *local* term shape the kernel checks syntactically and
      whose preconditions it decides with its own union-find at replay time
      (`check_ax_unsat`, stratified application); constants can only enter a
      class through input assertions or store/constarray operands embedded in
      the checked shape, so fabricated facts cannot manufacture a clash. The
      engine additionally replays every certificate with its own naive mirror
      of the kernel algorithm before claiming `Unsat`, and self-evaluates every
      model before claiming `Sat` (both degrade to `Unknown`/`Inconclusive`
      rather than guessing). Models are concrete arrays (default + sorted
      finite entries), re-checked by `check_array_model`. Wired end-to-end via
      `solve_and_check_bv` / `solve_and_check_arrays` in
      `tpt-solver/src/reference.rs` with certified SAT+UNSAT round-trip tests.
- [x] Continued differential/property testing at scale (ongoing; this pass added
      `differential_lra_vs_z3_when_available` in `tpt-solver/src/differential.rs`
      — the Z3 differential lane previously only covered QF_SAT, not QF_LRA — plus
      the Simplex pivot-bounds property test noted in Phase 3 and the e-graph
      truth-table property test noted in Phase 4. Real bugs found this pass:
      see the Phase 1 CDCL/Simplex notes and the audit finding below).
      This phase's additions found **three real CDCL soundness bugs** in
      `tpt-solver-core/src/sat.rs` (all exposed by the BV certification tests,
      all fix verified by the full suite): (1) `cancel_until` shrank the trail
      below the propagation head, letting `propagate` become a no-op after any
      backjump so pure decisions could produce clause-violating "Sat" models —
      head now clamped; (2) `reduce_db` rebuilt watchers blindly on
      `lits[0..2]`, which can watch two already-false literals so a surviving
      clause is never visited again — rebuild now watches non-false literals
      and reports level-0 falsification; (3) `analyze` collected current-level
      literals into the learnt clause (non-MiniSat semantics), producing
      non-asserting clauses whose swallowed enqueue failures let search wander
      past real contradictions — rewritten as proper first-UIP analysis, and
      `add_learnt` now surfaces falsified learnts as UNSAT instead of ignoring
      the failed enqueue.
      This pass's oracle tests (`solve_cnf_agrees_with_brute_force`,
      `blast_bv_agrees_with_semantics`) caught **two further `analyze()` bugs**
      in that same first-UIP rewrite: (4) satisfied literals were being marked
      `seen` during clause-literal scanning, corrupting the path-count and
      sending the trail scan into an unrecoverable empty-learnt bail that
      burned all fuel to `Unknown` — fixed by only marking a literal `seen`
      when it is actually falsified (`self.value(q) == Some(false)`); (5) the
      resolution step assumed, MiniSat-style, that a reason clause always has
      its propagated literal at index 0, but this engine's `propagate` has no
      such invariant (a watch swap can leave the propagated literal at index 1
      instead), so skipping index 0 on non-initial steps silently dropped a
      real antecedent literal — this produced a *wrong-polarity* unit learnt
      clause (e.g. asserting a gate output must be `true` when it is
      structurally forced `false`), a genuine soundness bug, not just an
      Unknown. Fixed by scanning every literal unconditionally; the earlier
      `value(q) == Some(false)` guard already excludes the pivot correctly, so
      the index-based skip was both unneeded and unsafe. Regression tests
      `bv::tests::bv_self_xor_equation_is_sat` and
      `sat::tests::solve_cnf_agrees_with_brute_force` cover these.
- [ ] SAT-COMP/SMT-COMP benchmark runs (performance, not correctness) — still
      open: requires competition hardware, benchmark corpora, and run windows;
      nothing to execute offline.
- [x] Full line-by-line audit of `tpt-solver-check` — found and fixed a **critical
      soundness bug** in `lrat.rs`'s `check_rup`: unit propagation recorded only
      the *variable* of a pending unit literal and always assigned it `True`,
      ignoring polarity. For a negative unit literal (e.g. a lone clause `(¬x)`,
      itself satisfiable by `x = false`) this drove the checker to a false
      self-conflict, so `check_proof` could `Accept` a bogus UNSAT proof for a
      satisfiable formula — the trusted kernel accepting a wrong answer, the one
      thing the whole certificate architecture exists to prevent. Fixed by
      tracking the desired post-propagation state alongside the variable index.
      Also hardened `lra.rs`'s `check_lra_model` to return `Inconclusive` on a
      too-short model instead of silently zero-padding missing coordinates.
      `sat.rs`/`outcome.rs` reviewed with no issues found. Regression tests added
      for both.
- [ ] If shared-state concurrency is ever introduced (parallel portfolio
      solving): wire through `loom` before merging
