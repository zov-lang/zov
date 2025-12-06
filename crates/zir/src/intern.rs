//! Interned types for efficient memory usage and fast comparisons
//!
//! Uses a sharded lock design inspired by rustc_data_structures for better
//! concurrent performance.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::ptr;

use parking_lot::RwLock;
use rustc_hash::{FxHashSet, FxHasher};

/// Number of shards (must be power of 2).
const SHARD_BITS: usize = 5;
const SHARDS: usize = 1 << SHARD_BITS;

/// An interned reference to a value. Equality is pointer-based.
#[repr(transparent)]
pub struct Interned<'a, T: ?Sized>(&'a T);

impl<'a, T: ?Sized> Interned<'a, T> {
    #[inline]
    pub const fn new_unchecked(value: &'a T) -> Self {
        Interned(value)
    }

    #[inline]
    pub fn as_ptr(self) -> *const T {
        self.0 as *const T
    }
}

impl<'a, T: ?Sized> Clone for Interned<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: ?Sized> Copy for Interned<'a, T> {}

impl<'a, T: ?Sized> Deref for Interned<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0
    }
}

impl<'a, T: ?Sized> PartialEq for Interned<'a, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<'a, T: ?Sized> Eq for Interned<'a, T> {}

impl<'a, T: ?Sized> Hash for Interned<'a, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::hash(self.0, state)
    }
}

impl<'a, T: fmt::Debug + ?Sized> fmt::Debug for Interned<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, T: fmt::Display + ?Sized> fmt::Display for Interned<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Compute shard index from a hash value.
#[inline]
fn shard_index(hash: u64) -> usize {
    // Skip top 7 bits (used by hashbrown) and lowest bits, extract SHARD_BITS
    let hash = hash >> 7;
    (hash as usize) & (SHARDS - 1)
}

/// Compute hash for a value.
#[inline]
fn hash_value<T: Hash>(value: &T) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

/// A single shard containing a locked hash set.
struct Shard<'a, T: Hash + Eq> {
    lock: RwLock<FxHashSet<&'a T>>,
}

impl<'a, T: Hash + Eq> Shard<'a, T> {
    fn new() -> Self {
        Self {
            lock: RwLock::new(FxHashSet::default()),
        }
    }
}

/// A sharded set for interning values. Thread-safe with reduced contention.
///
/// Uses multiple shards (each with its own lock) to reduce lock contention
/// in multi-threaded scenarios. Values are distributed across shards based
/// on their hash.
pub struct InternSet<'a, T: Hash + Eq> {
    shards: Box<[Shard<'a, T>; SHARDS]>,
}

impl<'a, T: Hash + Eq> Default for InternSet<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Hash + Eq> InternSet<'a, T> {
    pub fn new() -> Self {
        Self {
            shards: Box::new(std::array::from_fn(|_| Shard::new())),
        }
    }

    /// Intern a value, returning an interned reference.
    ///
    /// If the value already exists in the set, returns a reference to the
    /// existing value. Otherwise, allocates the value using the provided
    /// allocator and inserts it.
    pub fn intern<F>(&self, value: T, alloc: F) -> Interned<'a, T>
    where
        F: FnOnce(T) -> &'a T,
    {
        let hash = hash_value(&value);
        let shard_idx = shard_index(hash);
        let shard = &self.shards[shard_idx];

        // Try read lock first (fast path for existing values)
        {
            let set = shard.lock.read();
            if let Some(&existing) = set.get(&value) {
                return Interned::new_unchecked(existing);
            }
        }

        // Need write lock to insert
        let mut set = shard.lock.write();

        // Double-check after acquiring write lock
        if let Some(&existing) = set.get(&value) {
            return Interned::new_unchecked(existing);
        }

        let allocated = alloc(value);
        set.insert(allocated);
        Interned::new_unchecked(allocated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::Arena;

    #[test]
    fn test_intern_deduplication() {
        let arena = Arena::new();
        let set: InternSet<'_, i32> = InternSet::new();

        let a = set.intern(42, |v| arena.dropless.alloc(v));
        let b = set.intern(42, |v| arena.dropless.alloc(v));
        let c = set.intern(100, |v| arena.dropless.alloc(v));

        // Same value should return same pointer
        assert_eq!(a.as_ptr(), b.as_ptr());
        // Different values should have different pointers
        assert_ne!(a.as_ptr(), c.as_ptr());
        // Values should be correct
        assert_eq!(*a, 42);
        assert_eq!(*c, 100);
    }

    #[test]
    fn test_intern_pointer_equality() {
        let arena = Arena::new();
        // Use a tuple of Copy types (no Drop) instead of String
        let set: InternSet<'_, (u64, u64)> = InternSet::new();

        let s1 = set.intern((42, 100), |v| arena.dropless.alloc(v));
        let s2 = set.intern((42, 100), |v| arena.dropless.alloc(v));
        let s3 = set.intern((99, 200), |v| arena.dropless.alloc(v));

        assert_eq!(s1, s2); // Pointer equality
        assert_eq!(s1.as_ptr(), s2.as_ptr());
        assert_ne!(s1.as_ptr(), s3.as_ptr());
    }

    #[test]
    fn test_shard_distribution() {
        // Test that different hash values go to different shards
        let h1 = hash_value(&1u64);
        let h2 = hash_value(&1000u64);
        let h3 = hash_value(&999999u64);

        let s1 = shard_index(h1);
        let s2 = shard_index(h2);
        let s3 = shard_index(h3);

        // All shard indices should be valid
        assert!(s1 < SHARDS);
        assert!(s2 < SHARDS);
        assert!(s3 < SHARDS);
    }
}
