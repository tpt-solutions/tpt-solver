"""Generate the deterministic random 3-SAT corpus used by bench/run.py.

Instances are uniform random 3-SAT near the satisfiability threshold (clause/variable
ratio 4.26), written in DIMACS CNF. Output is reproducible: the same seeds always produce
the same files, so results can be compared across commits.
"""

import pathlib
import random

HERE = pathlib.Path(__file__).resolve().parent
SIZES = [20, 50, 75, 100]
SEEDS = [1, 2, 3]


def random_3sat(n, seed):
    rng = random.Random(seed * 1_000_003 + n)
    m = round(n * 4.26)
    lines = [f"c random 3-SAT, n={n}, seed={seed}", f"p cnf {n} {m}"]
    for _ in range(m):
        variables = rng.sample(range(1, n + 1), 3)
        lits = [v if rng.random() < 0.5 else -v for v in variables]
        lines.append(" ".join(map(str, lits)) + " 0")
    return "\n".join(lines) + "\n"


def main():
    out = HERE / "corpus"
    out.mkdir(exist_ok=True)
    for n in SIZES:
        for seed in SEEDS:
            path = out / f"r3sat-n{n}-s{seed}.cnf"
            path.write_text(random_3sat(n, seed), encoding="utf-8")
    print(f"wrote {len(SIZES) * len(SEEDS)} instances to {out}")


if __name__ == "__main__":
    main()
