//! Arena-based memory allocation for compiler data structures

use std::alloc::Layout;
use std::cell::{Cell, RefCell};
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::slice;

const PAGE: usize = 4096;
const HUGE_PAGE: usize = 2 * 1024 * 1024;

/// A typed arena that allocates objects of a single type.
pub struct TypedArena<T> {
    ptr: Cell<*mut T>,
    end: Cell<*mut T>,
    chunks: RefCell<Vec<ArenaChunk<T>>>,
}

struct ArenaChunk<T> {
    storage: Box<[MaybeUninit<T>]>,
}

impl<T> ArenaChunk<T> {
    #[inline]
    fn new(capacity: usize) -> Self {
        Self {
            storage: Box::new_uninit_slice(capacity),
        }
    }

    #[inline]
    fn start(&mut self) -> *mut T {
        self.storage.as_mut_ptr().cast()
    }

    #[inline]
    fn end(&mut self) -> *mut T {
        unsafe { self.start().add(self.storage.len()) }
    }
}

impl<T> Default for TypedArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> TypedArena<T> {
    pub fn new() -> Self {
        Self {
            ptr: Cell::new(ptr::null_mut()),
            end: Cell::new(ptr::null_mut()),
            chunks: RefCell::new(Vec::new()),
        }
    }

    fn grow(&self, additional: usize) {
        let elem_size = mem::size_of::<T>();
        let min_capacity = self.chunks.borrow().last().map_or(0, |c| c.storage.len()) * 2;
        let min_capacity = min_capacity.max(additional);

        let new_capacity = if elem_size == 0 {
            usize::MAX
        } else {
            let target_bytes = min_capacity.saturating_mul(elem_size);
            let next_page = if target_bytes <= PAGE {
                PAGE
            } else if target_bytes <= HUGE_PAGE {
                HUGE_PAGE
            } else {
                target_bytes
            };
            next_page / elem_size
        };

        let mut chunk = ArenaChunk::<T>::new(new_capacity.max(additional));
        self.ptr.set(chunk.start());
        self.end.set(chunk.end());
        self.chunks.borrow_mut().push(chunk);
    }

    #[inline]
    pub fn alloc(&self, value: T) -> &mut T {
        if self.ptr == self.end {
            self.grow(1);
        }

        unsafe {
            let ptr = self.ptr.get();
            ptr.write(value);
            self.ptr.set(ptr.add(1));
            &mut *ptr
        }
    }

    pub fn alloc_slice(&self, slice: &[T]) -> &mut [T]
    where
        T: Copy,
    {
        if slice.is_empty() {
            return &mut [];
        }

        let available = unsafe { self.end.get().offset_from(self.ptr.get()) as usize };
        if available < slice.len() {
            self.grow(slice.len());
        }

        unsafe {
            let ptr = self.ptr.get();
            ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len());
            self.ptr.set(ptr.add(slice.len()));
            slice::from_raw_parts_mut(ptr, slice.len())
        }
    }
}

impl<T> Drop for TypedArena<T> {
    fn drop(&mut self) {
        if !mem::needs_drop::<T>() {
            return;
        }

        let chunks = self.chunks.get_mut();
        if let Some(last) = chunks.last_mut() {
            let start = last.start();
            let end = self.ptr.get();
            let len = unsafe { end.offset_from(start) as usize };
            for i in 0..len {
                unsafe { ptr::drop_in_place(start.add(i)) };
            }
        }

        for chunk in chunks.iter_mut().rev().skip(1) {
            let len = chunk.storage.len();
            for i in 0..len {
                unsafe { ptr::drop_in_place(chunk.start().add(i)) };
            }
        }
    }
}

/// An arena that allocates values that do not need to be dropped.
pub struct DroplessArena {
    ptr: Cell<*mut u8>,
    end: Cell<*mut u8>,
    chunks: RefCell<Vec<Box<[MaybeUninit<u8>]>>>,
}

impl Default for DroplessArena {
    fn default() -> Self {
        Self::new()
    }
}

impl DroplessArena {
    pub fn new() -> Self {
        Self {
            ptr: Cell::new(ptr::null_mut()),
            end: Cell::new(ptr::null_mut()),
            chunks: RefCell::new(Vec::new()),
        }
    }

    fn grow(&self, layout: Layout) {
        let min_size = self.chunks.borrow().last().map_or(0, |c| c.len()) * 2;
        let min_size = min_size.max(layout.size());

        let new_size = if min_size <= PAGE {
            PAGE
        } else if min_size <= HUGE_PAGE {
            HUGE_PAGE
        } else {
            min_size
        };

        let mut chunk = Box::new_uninit_slice(new_size);
        self.ptr.set(chunk.as_mut_ptr().cast());
        self.end.set(unsafe { chunk.as_mut_ptr().add(new_size).cast() });
        self.chunks.borrow_mut().push(chunk);
    }

    #[inline]
    fn align_ptr(&self, align: usize) -> *mut u8 {
        let ptr = self.ptr.get() as usize;
        let aligned = (ptr + align - 1) & !(align - 1);
        aligned as *mut u8
    }

    pub fn alloc_raw(&self, layout: Layout) -> *mut u8 {
        let aligned = self.align_ptr(layout.align());
        let end = unsafe { aligned.add(layout.size()) };

        if end > self.end.get() {
            self.grow(layout);
            return self.alloc_raw(layout);
        }

        self.ptr.set(end);
        aligned
    }

    #[inline]
    pub fn alloc<T>(&self, value: T) -> &mut T {
        assert!(!mem::needs_drop::<T>());

        let ptr = self.alloc_raw(Layout::new::<T>()).cast::<T>();
        unsafe {
            ptr.write(value);
            &mut *ptr
        }
    }

    pub fn alloc_slice<T: Copy>(&self, slice: &[T]) -> &[T] {
        if slice.is_empty() {
            return &[];
        }

        let layout = Layout::for_value(slice);
        let ptr = self.alloc_raw(layout).cast::<T>();
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len());
            slice::from_raw_parts(ptr, slice.len())
        }
    }
}

/// Combined arena holding all typed arenas for the compiler.
#[derive(Default)]
pub struct Arena<'zir> {
    pub dropless: DroplessArena,
    _marker: std::marker::PhantomData<&'zir ()>,
}

impl<'zir> Arena<'zir> {
    pub fn new() -> Self {
        Self {
            dropless: DroplessArena::new(),
            _marker: std::marker::PhantomData,
        }
    }
}
