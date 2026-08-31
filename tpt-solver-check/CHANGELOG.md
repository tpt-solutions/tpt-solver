# Changelog

All notable changes to the `tpt-solver-check` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — 2026-08-31

Initial public workspace release of the three-crate `tpt-solver` suite.

### Added

- **Three-way outcome** (`outcome`): `Accept` / `Reject` / `Inconclusive`, plus
  accept/reject/inconclusive rate tracking behind the `VerdictTracker` idiom used by the
  differential test gates.
- **SAT model recheck** (`sat`): substitutes the engine's returned assignment back into the
  original formula and checks satisfaction — the cheap, high-yield catch for wrong SAT
  answers.
- **RUP / LRAT checker** (`lrat`): unit-propagation RUP core that re-derives every learned
  clause from the original clauses; validates the CDCL engine's LRAT proof emission.
- **Farkas certificate checking** (`lra`): coefficient-by-coefficient revalidation of the
  Fourier–Motzkin UNSAT certificate, plus an LRA SAT model recheck.
- **Bit-vector checking** (`bv`): an *independently written* model evaluator and UNSAT
  certificate checker that reuses the RUP core (short models are `Inconclusive`, never
  zero-padded).
- **Array checking** (`array`): congruence-closure certificate replay whose axiom
  preconditions are decided with the kernel's own union-find at replay time, so fabricated
  facts cannot manufacture a class clash.
- **`no_std` + `alloc`, zero dependencies**; `#![deny(clippy::unwrap_used, clippy::panic)]`
  lint gate; `std` feature.

### Fixed

- **Critical soundness bug in `lrat::check_rup`.** Unit propagation tracked only the
  *variable* of a pending unit literal and always assigned it `True`, ignoring polarity. For
  a negative unit literal this drove the checker to a false self-conflict, so `check_proof`
  could `Accept` a bogus UNSAT proof for a satisfiable formula — the trusted kernel accepting
  a wrong answer. Fixed by tracking the desired post-propagation state alongside the variable
  index.
- Hardened `lra::check_lra_model` to return `Inconclusive` on a too-short model instead of
  silently zero-padding missing coordinates.

[0.1.0]: https://github.com/tpt-solutions/tpt-solver/releases/tag/v0.1.0
