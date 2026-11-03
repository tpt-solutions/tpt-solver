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

`run.py --oracle CMD` runs an external SAT-competition solver on every instance and
fails the run if its verdict disagrees with a certified answer. Quote paths that contain
spaces, because the command is split like a shell command line. For example:

```sh
python bench/run.py --oracle "minisat"
```

minisat is not vendored or installed by this repository. `z3` on PATH fills the `z3`
column in the same way. Neither oracle was run in this environment, so comparison
results are not yet recorded.

## Corpus

Uniform random 3-SAT at clause-to-variable ratio 4.26, for n in {20, 50, 75, 100} with
seeds 1 to 3. These are the only instances in the repository. SATLIB and SMT-LIB
benchmark sets are not vendored, because of their size and licensing.

The nightly workflow (`.github/workflows/nightly.yml`) runs both harnesses and keeps
the results as artifacts.
