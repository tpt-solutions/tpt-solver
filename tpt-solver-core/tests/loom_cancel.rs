//! Loom model check for `cancel::Cancel` — the one piece of shared-state
//! concurrency the engine introduces (for racing portfolio SAT workers).
//!
//! Runs only under `--cfg loom` (loom explores every thread interleaving, so
//! it must not run as part of the normal `cargo test` loop):
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p tpt-solver-core --release --features loom --test loom_cancel -- --test-threads=1
//! ```

#![cfg(loom)]

#[test]
fn cancel_is_eventually_observed_after_request() {
    // A single spinning observer: loom exhaustively explores every
    // interleaving of `request`'s store against `is_set`'s loads, so this
    // proves the flag is never lost or reordered away, however the scheduler
    // interleaves the two threads. (A second, concurrently-spinning observer
    // was tried too, but two unbounded spin loops multiply loom's explored
    // state space past its branch budget — a model-checker capacity limit,
    // not a soundness question; a single observer already exercises the
    // exact store/load pair every worker in a real race depends on.)
    loom::model(|| {
        let cancel = tpt_solver_core::cancel::Cancel::shared();
        let worker = cancel.clone();
        let t = loom::thread::spawn(move || {
            while !worker.is_set() {
                loom::thread::yield_now();
            }
        });
        cancel.request();
        t.join().unwrap();
    });
}
