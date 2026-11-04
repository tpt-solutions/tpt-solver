//! Criterion benchmarks for the certified pipeline.
//!
//! Run with `cargo bench -p tpt-solver`. Each group times the work that a user sees:
//! parsing, the engine, and the checker that revalidates the answer.

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use tpt_solver::api::{solve_str, Format, Options};
use tpt_solver::policy::solve_cnf_certified;
use tpt_solver::reference::Problem;

/// A deterministic random 3-SAT instance near the phase transition.
fn random_3sat(n: u32, seed: u64) -> Problem {
    let mut state = seed;
    let mut next = move || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state >> 33
    };
    let m = (n as f64 * 4.26).round() as usize;
    let mut clauses = Vec::with_capacity(m);
    for _ in 0..m {
        let mut clause = Vec::with_capacity(3);
        for _ in 0..3 {
            let v = 1 + (next() % n as u64) as i32;
            clause.push(if next() % 2 == 0 { v } else { -v });
        }
        clauses.push(clause);
    }
    Problem {
        var_count: n,
        clauses,
    }
}

fn dimacs_text(problem: &Problem) -> String {
    let mut text = format!("p cnf {} {}\n", problem.var_count, problem.clauses.len());
    for clause in &problem.clauses {
        for lit in clause {
            text.push_str(&format!("{lit} "));
        }
        text.push_str("0\n");
    }
    text
}

fn bench_certified_cdcl(c: &mut Criterion) {
    let mut group = c.benchmark_group("certified_cdcl");
    for &n in &[100u32, 200] {
        let problem = random_3sat(n, 0xBADC0DE ^ n as u64);
        group.bench_function(format!("random3sat_{n}"), |b| {
            b.iter(|| black_box(solve_cnf_certified(black_box(&problem), 50_000_000, 1)))
        });
    }
    group.finish();
}

fn bench_parse_and_solve(c: &mut Criterion) {
    let text = dimacs_text(&random_3sat(200, 7));
    let opts = Options {
        fuel: 50_000_000,
        ..Options::default()
    };
    c.bench_function("api_solve_str_dimacs_200", |b| {
        b.iter(|| black_box(solve_str(black_box(&text), Format::Dimacs, &opts)))
    });
}

criterion_group!(benches, bench_certified_cdcl, bench_parse_and_solve);
criterion_main!(benches);
