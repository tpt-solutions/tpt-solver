//! Cooperative cancellation for portfolio-style racing (Phase 5).
//!
//! A [`Cancel`] handle wraps one shared flag. Any clone can [`request`] it;
//! any clone can cheaply poll [`is_set`] from inside a hot search loop. This
//! is the *only* shared mutable state a caller can introduce into the engine
//! (e.g. to race several [`crate::sat::solve_cnf_worker`] calls on separate
//! threads and stop the losers once a winner is checker-accepted) — every
//! other loop in the engine remains single-threaded and untouched.
//!
//! [`request`]: Cancel::request
//! [`is_set`]: Cancel::is_set
//!
//! Under `--cfg loom` the flag is backed by `loom`'s shadow `Arc`/`AtomicBool`
//! instead of the real ones, so `tests/loom_cancel.rs` can model-check every
//! thread interleaving of a `request`/`is_set` pair.

#[cfg(not(loom))]
use alloc::sync::Arc;
#[cfg(not(loom))]
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(loom)]
use loom::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// A cheaply-`Clone`-able cancellation handle.
///
/// `Cancel::none()` is a permanent no-op (never set, `request` does nothing) —
/// the default for every solve that isn't part of a portfolio race.
#[derive(Clone, Debug, Default)]
pub struct Cancel(Option<Arc<AtomicBool>>);

impl Cancel {
    /// A handle that is never set and whose `request` is a no-op.
    #[inline]
    pub fn none() -> Cancel {
        Cancel(None)
    }

    /// A fresh, real handle. Clone it to share one flag across threads.
    pub fn shared() -> Cancel {
        Cancel(Some(Arc::new(AtomicBool::new(false))))
    }

    /// Ask every clone of this handle to stop. No-op on `Cancel::none()`.
    #[inline]
    pub fn request(&self) {
        if let Some(flag) = &self.0 {
            flag.store(true, Ordering::Relaxed);
        }
    }

    /// Whether cancellation has been requested on any clone of this handle.
    #[inline]
    pub fn is_set(&self) -> bool {
        match &self.0 {
            Some(flag) => flag.load(Ordering::Relaxed),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn none_is_never_set() {
        let c = Cancel::none();
        assert!(!c.is_set());
        c.request();
        assert!(!c.is_set());
    }

    #[test]
    fn shared_clone_observes_request() {
        let a = Cancel::shared();
        let b = a.clone();
        assert!(!a.is_set());
        assert!(!b.is_set());
        b.request();
        assert!(a.is_set());
        assert!(b.is_set());
    }
}
