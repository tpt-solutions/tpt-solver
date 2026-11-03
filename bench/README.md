# Benchmarks

Two harnesses measure tpt-solver. Neither needs a competition corpus, so both run in
CI-sized time.

- **Criterion** (`tpt-solver/benches/solve.rs`) times the certified CDCL pipeline and
  the full `solve_str` path on random 3-SAT. Run it with
  `cargo bench -p tpt-solver --bench solve`.
- **Corpus runner** (`bench/run.py`) runs the release binary over the instances in
  `bench/corpus/` and writes `bench/results.csv`. The run fails if the checker rejects
  any answer.

```sh
python bench/gen_corpus.py   # regenerate the corpus (deterministic)
cargo build --release -p tpt-solver
python bench/run.py          # results in bench/results.csv
```

The `bench` subcommand of the CLI is a separate CSV ladder. It is useful for watching
performance across commits.

## Competitor comparison

If `z3` is on PATH, `run.py` records its verdict in the `z3` column, so answers can
be compared against an external oracle. Comparison against minisat or Kissat needs
those binaries installed, and the runner does not invoke them yet. The corpus is
small, so timings should be read as regression signals, not as competition results.

## Corpus

Uniform random 3-SAT at clause-to-variable ratio 4.26, for n in {20, 50, 75, 100} with
seeds 1 to 3. These are the only instances in the repository. SATLIB and SMT-LIB
benchmark sets are not vendored, because of their size and licensing.

The nightly workflow (`.github/workflows/nightly.yml`) runs both harnesses and keeps
the results as artifacts.
