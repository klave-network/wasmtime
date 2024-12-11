use crate::prelude::*;
use crate::runtime::vm::{HostAlignedByteCount, SendSyncPtr};
use anyhow::{anyhow, bail, Result};
use std::ffi::{c_int, c_void};
use std::fs::File;
use std::ops::Range;
use std::path::Path;
use std::ptr::{self, NonNull};

/// Open a file so that it can be mmap'd for executing.
#[cfg(feature = "std")]
pub fn open_file_for_mmap(_path: &Path) -> Result<File> {
    bail!("not supported on sgx");
}

#[derive(Debug)]
pub struct Mmap {
    memory: SendSyncPtr<[u8]>,
}

extern "C" {
    pub fn sgx_mm_alloc(
        addr: *const c_void,
        length: usize,
        flags: c_int,
        handler: *const c_void,
        handler_private: *mut c_void,
        out_addr: *mut *mut c_void,
    ) -> c_int;
    pub fn sgx_mm_dealloc(addr: *const c_void, length: usize) -> c_int;
    pub fn sgx_mm_modify_permissions(addr: *const c_void, length: usize, prot: c_int) -> c_int;
}

impl Mmap {
    pub fn new_empty() -> Mmap {
        Mmap {
            memory: SendSyncPtr::from(&mut [][..]),
        }
    }

    fn new_internal(size: HostAlignedByteCount, commit: bool) -> Result<Self> {
        let flags: c_int = if commit { 2 } else { 1 }; // SGX_EMA_COMMIT_NOW or SGX_EMA_RESERVE
        let mut ptr: *mut c_void = ptr::null_mut();
        let res = unsafe {
            sgx_mm_alloc(
                ptr::null_mut(),
                size.byte_count(),
                flags,
                ptr::null_mut(),
                ptr::null_mut(),
                &mut ptr,
            )
        };
        if res != 0 {
            return Err(anyhow!(res));
        }
        let memory = std::ptr::slice_from_raw_parts_mut(ptr.cast(), size.byte_count());
        let memory = SendSyncPtr::new(NonNull::new(memory).unwrap());
        Ok(Mmap { memory })
    }

    pub fn new(size: HostAlignedByteCount) -> Result<Self> {
        Self::new_internal(size, true)
    }

    pub fn reserve(size: HostAlignedByteCount) -> Result<Self> {
        Self::new_internal(size, false)
    }

    #[cfg(feature = "std")]
    pub fn from_file(_file: &File) -> Result<Self> {
        bail!("not supported on sgx");
    }

    pub fn make_accessible(
        &self,
        start: HostAlignedByteCount,
        len: HostAlignedByteCount,
    ) -> Result<()> {
        let start_addr = unsafe {
            self.memory
                .as_ptr()
                .cast::<u8>()
                .add(start.byte_count())
                .cast()
        };
        let mut ptr: *mut c_void = ptr::null_mut();
        let res = unsafe {
            sgx_mm_alloc(
                start_addr,
                len.byte_count(),
                2, // SGX_EMA_COMMIT_NOW
                ptr::null_mut(),
                ptr::null_mut(),
                &mut ptr,
            )
        };
        if res != 0 {
            return Err(anyhow!(res));
        }
        let res = unsafe {
            sgx_mm_modify_permissions(
                start_addr, len.byte_count(), 3, // SGX_EMA_PROT_READ_WRITE
            )
        };
        if res != 0 {
            return Err(anyhow!(res));
        }

        Ok(())
    }

    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.memory.as_ptr() as *const u8
    }

    #[inline]
    pub fn as_mut_ptr(&self) -> *mut u8 {
        self.memory.as_ptr().cast()
    }

    #[inline]
    pub fn len(&self) -> usize {
        unsafe { (*self.memory.as_ptr()).len() }
    }

    pub unsafe fn make_executable(
        &self,
        range: Range<usize>,
        _enable_branch_protection: bool,
    ) -> Result<()> {
        let base = self.memory.as_ptr().cast::<u8>().add(range.start).cast();
        let len = range.end - range.start;
        // contrary to mprotect, sgx_mm_modify_permissions expects len to be a multiple of the page size (else EINVAL)
        let page_size = crate::runtime::vm::host_page_size();
        let len = (len + (page_size - 1)) & !(page_size - 1);

        let res = sgx_mm_modify_permissions(
            base, len, 5, // SGX_EMA_PROT_READ_EXEC
        );
        if res != 0 {
            return Err(anyhow!(res));
        }

        Ok(())
    }

    pub unsafe fn make_readonly(&self, range: Range<usize>) -> Result<()> {
        let base = self.memory.as_ptr().cast::<u8>().add(range.start).cast();
        let len = range.end - range.start;
        // contrary to mprotect, sgx_mm_modify_permissions expects len to be a multiple of the page size (else EINVAL)
        let page_size = crate::runtime::vm::host_page_size();
        let len = (len + (page_size - 1)) & !(page_size - 1);

        let res = sgx_mm_modify_permissions(
            base, len, 1, // SGX_EMA_PROT_READ
        );
        if res != 0 {
            return Err(anyhow!(res));
        }

        Ok(())
    }
}

impl Drop for Mmap {
    fn drop(&mut self) {
        unsafe {
            let ptr = self.memory.as_ptr().cast();
            let len = (*self.memory.as_ptr()).len();
            if len == 0 {
                return;
            }
            sgx_mm_dealloc(ptr, len);
        }
    }
}
