//! Structural memory: arenas and trail stacks for O(1) backtracking.
//!
//! Search in SAT/SMT is a depth-first exploration of a decision tree. The cheapest
//! way to backtrack is *not* to free memory but to keep a **trail** of what changed
//! and rewind it to a saved length. These structures support exactly that.

extern crate alloc;
use alloc::vec::Vec;

/// A trail: an append-only log that can be rewound to a previously-saved length in
/// O(1) time (the contents are simply forgotten, not individually dropped — `T` must
/// be `Copy` or trivially droppable for that to be sound-free; we require `T: Copy`).
#[derive(Clone, Debug, Default)]
pub struct Trail<T> {
    data: Vec<T>,
}

impl<T: Copy> Trail<T> {
    /// A marker for the current end of the trail, usable with [`Trail::truncate`].
    #[inline]
    pub fn checkpoint(&self) -> usize {
        self.data.len()
    }

    /// Push a value onto the trail.
    #[inline]
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }

    /// Number of entries currently on the trail.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Whether the trail is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Rewind the trail to `checkpoint`, discarding newer entries.
    #[inline]
    pub fn truncate(&mut self, checkpoint: usize) {
        self.data.truncate(checkpoint);
    }

    /// Iterate the entries currently on the trail.
    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.data.iter()
    }

    /// The entry at `index`, if present.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
}

impl<T: Copy> core::ops::Index<usize> for Trail<T> {
    type Output = T;
    #[inline]
    fn index(&self, index: usize) -> &T {
        &self.data[index]
    }
}

impl<T: Copy> Trail<T> {
    /// Drain the trail, returning all entries and resetting to empty.
    #[inline]
    pub fn drain_all(&mut self) -> Vec<T> {
        core::mem::take(&mut self.data)
    }
}

/// A bump-style arena that hands out dense, stable indices and can be reset to a
/// previously-saved size. Unlike [`Trail`], stored values are addressed by index and
/// outlive a `truncate` of *other* trails that reference them.
#[derive(Clone, Debug, Default)]
pub struct Arena<T> {
    data: Vec<T>,
}

impl<T> Arena<T> {
    /// A marker for the current capacity/length, usable with [`Arena::reset`].
    #[inline]
    pub fn watermark(&self) -> usize {
        self.data.len()
    }

    /// Append a value, returning its 0-based index.
    #[inline]
    pub fn push(&mut self, value: T) -> usize {
        let idx = self.data.len();
        self.data.push(value);
        idx
    }

    /// Number of stored values.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Whether the arena is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Discard all values at or above `watermark`.
    #[inline]
    pub fn reset(&mut self, watermark: usize) {
        self.data.truncate(watermark);
    }

    /// The value at `index`, if present.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// Mutable access to the value at `index`, if present.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.data.get_mut(index)
    }
}

impl<T> core::ops::Index<usize> for Arena<T> {
    type Output = T;
    #[inline]
    fn index(&self, index: usize) -> &T {
        &self.data[index]
    }
}

impl<T> core::ops::IndexMut<usize> for Arena<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.data[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trail_rewind() {
        let mut t: Trail<u32> = Trail::default();
        let c = t.checkpoint();
        t.push(1);
        t.push(2);
        assert_eq!(t.len(), 2);
        t.truncate(c);
        assert_eq!(t.len(), 0);
    }

    #[test]
    fn arena_reset() {
        let mut a: Arena<u32> = Arena::default();
        let w = a.watermark();
        let _ = a.push(10);
        let _ = a.push(20);
        assert_eq!(a.len(), 2);
        a.reset(w);
        assert_eq!(a.len(), 0);
    }
}
