//! Interned types for efficient memory usage and fast comparisons

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::ptr;

use parking_lot::RwLock;
use rustc_hash::FxHashSet;

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

/// A set for interning values. Thread-safe.
pub struct InternSet<'a, T: Hash + Eq> {
    set: RwLock<FxHashSet<&'a T>>,
}

impl<'a, T: Hash + Eq> Default for InternSet<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Hash + Eq> InternSet<'a, T> {
    pub fn new() -> Self {
        Self {
            set: RwLock::new(FxHashSet::default()),
        }
    }

    pub fn intern<F>(&self, value: T, alloc: F) -> Interned<'a, T>
    where
        F: FnOnce(T) -> &'a T,
    {
        {
            let set = self.set.read();
            if let Some(&existing) = set.get(&value) {
                return Interned::new_unchecked(existing);
            }
        }

        let mut set = self.set.write();
        if let Some(&existing) = set.get(&value) {
            return Interned::new_unchecked(existing);
        }

        let allocated = alloc(value);
        set.insert(allocated);
        Interned::new_unchecked(allocated)
    }
}
