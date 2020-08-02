// use std::alloc::AllocRef;
// use alloc_wg::alloc::{AllocRef, Layout, AllocInit, MemoryBlock, AllocErr, ReallocPlacement};
use std::alloc::{AllocRef, Layout, AllocInit, MemoryBlock, AllocErr, ReallocPlacement};
use alloc_wg::vec::Vec;
use std::ptr::NonNull;

use crate::ffi;

// #[repr(transparent)]
// #[derive(Debug, Default, Copy, Clone)]
// pub struct MemFile(pub Vec<u8, SqliteAlloc>);
pub type MemFile = Vec<u8, SqliteAlloc>;

#[derive(Debug, Default, Copy, Clone)]
pub struct SqliteAlloc;

impl MemFile {
    pub fn new() -> Self {
        Self::new_in(SqliteAlloc)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, SqliteAlloc)
    }
}

unsafe impl AllocRef for SqliteAlloc {
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        unsafe {
            let size = layout.size();
            if size == 0 {
                Ok(MemoryBlock { ptr: layout.dangling(), size: 0 })
            } else {
                let raw_ptr = ffi::sqlite3_malloc64(size as _);
                let size = ffi::sqlite3_msize(raw_ptr) as _;
                let ptr = NonNull::new(raw_ptr as *mut u8).ok_or(AllocErr)?;
                let memory = MemoryBlock { ptr, size };
                init.init(memory);
                Ok(memory)
            }
        }
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            ffi::sqlite3_free(ptr.as_ptr() as _)
        }
    }

    unsafe fn grow(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size >= size,
            "`new_size` must be greater than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if layout.size() == 0 => {
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                self.alloc(new_layout, init)
            }
            ReallocPlacement::MayMove => {
                let ptr = ffi::sqlite3_realloc64(ptr.as_ptr() as _, new_size as _);
                let new_size = ffi::sqlite3_msize(ptr) as _;
                let memory =
                    MemoryBlock { ptr: NonNull::new(ptr as *mut u8).ok_or(AllocErr)?, size: new_size };
                init.init_offset(memory, size);
                Ok(memory)
            }
        }
    }

    unsafe fn shrink(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size <= size,
            "`new_size` must be smaller than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if new_size == 0 => {
                self.dealloc(ptr, layout);
                Ok(MemoryBlock { ptr: layout.dangling(), size: 0 })
            }
            ReallocPlacement::MayMove => {
                let ptr = ffi::sqlite3_realloc64(ptr.as_ptr() as _, new_size as _);
                let new_size = ffi::sqlite3_msize(ptr) as _;
                Ok(MemoryBlock { ptr: NonNull::new(ptr as *mut u8).ok_or(AllocErr)?, size: new_size })
            }
        }
    }
}
