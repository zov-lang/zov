//! Arena-allocated immutable lists

use std::alloc::Layout;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::{fmt, ptr, slice};

use crate::arena::{Arena, DroplessArena};

/// Opaque contents marker for the List type.
#[repr(C)]
struct OpaqueListContents {
    _data: [u8; 0],
}

/// An arena-allocated, immutable list of elements.
/// Memory layout: [length: usize][elements: T...][OpaqueListContents]
#[repr(C)]
pub struct List<T> {
    len: usize,
    data: [T; 0],
    opaque: OpaqueListContents,
}

impl<T> List<T> {
    /// Returns the number of elements in the list.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the list is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns a pointer to the first element.
    #[inline]
    fn as_ptr(&self) -> *const T {
        self.data.as_ptr()
    }

    /// Returns the list as a slice.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    /// Returns an empty list.
    pub fn empty<'zir>() -> &'zir List<T> {
        #[repr(C, align(64))]
        struct EmptyList {
            len: usize,
        }

        static EMPTY: EmptyList = EmptyList { len: 0 };

        unsafe { &*ptr::addr_of!(EMPTY).cast::<List<T>>() }
    }
}

impl<T: Copy> List<T> {
    /// Allocates a list from a slice in the given arena.
    pub fn from_arena<'zir>(arena: &'zir Arena<'zir>, slice: &[T]) -> &'zir List<T> {
        if slice.is_empty() {
            return List::empty();
        }

        Self::from_dropless_arena(&arena.dropless, slice)
    }

    /// Allocates a list from a slice in a dropless arena.
    pub fn from_dropless_arena<'zir>(arena: &'zir DroplessArena, slice: &[T]) -> &'zir List<T> {
        if slice.is_empty() {
            return List::empty();
        }

        let (layout, _offset) =
            Layout::new::<usize>().extend(Layout::for_value::<[T]>(slice)).unwrap();

        let mem = arena.alloc_raw(layout) as *mut List<T>;

        unsafe {
            ptr::addr_of_mut!((*mem).len).write(slice.len());
            ptr::addr_of_mut!((*mem).data)
                .cast::<T>()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            &*mem
        }
    }
}

impl<T> Deref for List<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other) || self.as_slice() == other.as_slice()
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T: Hash> Hash for List<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state)
    }
}
