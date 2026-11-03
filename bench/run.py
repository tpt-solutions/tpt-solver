"""Run tpt-solver over the corpus and write a CSV of results and timings.

    python bench/run.py [--solver PATH] [--fuel N] [--out FILE]

Each instance runs through the certified CLI (`--output json`). The run fails, with a
non-zero exit code, if the checker rejects any answer, because that means the trusted
kernel refused the engine. When `z3` is on PATH its verdict is recorded as an external
cross-check. Otherwise the column is left empty.
"""

import argparse
import csv
import json
import pathlib
import shutil
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent


def default_solver():
    exe = "tpt-solver.exe" if sys.platform == "win32" else "tpt-solver"
    for profile in ("release", "debug"):
        candidate = HERE.parent / "target" / profile / exe
        if candidate.exists():
            return candidate
    return pathlib.Path(exe)


def z3_verdict(path):
    if shutil.which("z3") is None:
        return ""
    proc = subprocess.run(["z3", str(path)], capture_output=True, text=True, timeout=600)
    words = proc.stdout.split()
    return words[0] if words else ""


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--solver", default=str(default_solver()))
    parser.add_argument("--fuel", type=int, default=50_000_000)
    parser.add_argument("--out", default=str(HERE / "results.csv"))
    args = parser.parse_args()

    files = sorted((HERE / "corpus").glob("*.cnf"))
    rejected = 0
    with open(args.out, "w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["instance", "result", "checker", "solver_ms", "wall_ms", "z3"])
        for path in files:
            start = time.perf_counter()
            proc = subprocess.run(
                [args.solver, str(path), "--output", "json", "--fuel", str(args.fuel)],
                capture_output=True,
                text=True,
                timeout=900,
            )
            wall_ms = (time.perf_counter() - start) * 1000
            if proc.returncode not in (0, 1):
                sys.exit(f"{path.name}: solver failed (exit {proc.returncode}): {proc.stderr}")
            report = json.loads(proc.stdout)
            if report["checker"] == "reject":
                rejected += 1
            writer.writerow([
                path.name,
                report["result"],
                report["checker"],
                f"{report['stats']['elapsed_ms']:.3f}",
                f"{wall_ms:.3f}",
                z3_verdict(path),
            ])
            print(f"{path.name:24} {report['result']:8} {report['checker']:13} "
                  f"{report['stats']['elapsed_ms']:10.3f} ms")
    print(f"wrote {args.out}")
    if rejected:
        sys.exit(f"{rejected} answer(s) rejected by the checker")


if __name__ == "__main__":
    main()
