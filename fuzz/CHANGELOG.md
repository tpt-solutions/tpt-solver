# Changelog

All notable changes to the `tpt-solver-fuzz` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

> This crate is a development-only, detached `cargo-fuzz` workspace and is **not published**
> to crates.io. Its version is pinned at `0.0.0` to signal that it tracks the main workspace
> rather than shipping independently.

## [0.0.0] — 2026-08-31

Fuzzing scaffolding for the `tpt-solver` suite, introduced alongside the Phase 4 periphery.

### Added

- **`dimacs` target** — fuzzes `tpt_solver::parsers::dimacs::parse_dimacs`.
- **`smtlib2` target** — fuzzes `parse_script` and its `to_lra` / `to_cnf` / `to_bv` /
  `to_array` lowerings.
- **`mps` target** — fuzzes `tpt_solver::parsers::mps::parse_mps`.
- Detached `cargo-fuzz` workspace wired to the main `tpt-solver` crate via `path`
  dependencies; `publish = false`.

[0.0.0]: https://github.com/tpt-solutions/tpt-solver/releases/tag/v0.1.0
