//! Index types and IndexVec for arena-based data structures

use std::fmt;
use std::hash::Hash;

pub use index_vec::IndexVec;

/// A trait for index types used in arena-based collections.
pub trait Idx: Copy + Eq + Hash + fmt::Debug + 'static {
    fn new(idx: usize) -> Self;
    fn index(self) -> usize;

    #[inline]
    fn from_u32(idx: u32) -> Self {
        Self::new(idx as usize)
    }

    #[inline]
    fn as_u32(self) -> u32 {
        self.index() as u32
    }
}

/// Macro to define new index types.
#[macro_export]
macro_rules! define_index {
    ($(#[$attr:meta])* $vis:vis struct $name:ident = u32;) => {
        $(#[$attr])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $name(u32);

        impl $crate::idx::Idx for $name {
            #[inline]
            fn new(idx: usize) -> Self {
                debug_assert!(idx <= u32::MAX as usize);
                Self(idx as u32)
            }

            #[inline]
            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl index_vec::Idx for $name {
            fn from_usize(idx: usize) -> Self {
                debug_assert!(idx <= u32::MAX as usize);
                Self(idx as u32)
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

pub use define_index;
