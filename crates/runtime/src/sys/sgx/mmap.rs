use crate::SendSyncPtr;
use anyhow::{anyhow, bail, Result};
use std::fs::File;
use std::ops::Range;
use std::path::Path;
use std::ptr::{self, NonNull};
use std::ffi::{c_int, c_void};

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
    pub fn sgx_mm_modify_permissions(addr: *const c_void, length: usize, prot: c_int)
        -> c_int;
}

impl Mmap {
    pub fn new_empty() -> Mmap {
        Mmap {
            memory: SendSyncPtr::from(&mut [][..]),
        }
    }

    fn new_internal(size: usize, commit: bool) -> Result<Self> {
        let flags: c_int = if commit { 2 } else { 1 }; // SGX_EMA_COMMIT_NOW or SGX_EMA_RESERVE
        let mut ptr: *mut c_void = ptr::null_mut();
        let res = unsafe {
            sgx_mm_alloc(
                ptr::null_mut(),
                size,
                flags,
                ptr::null_mut(),
                ptr::null_mut(),
                &mut ptr
            )
        };
        if res != 0 {
            return Err(anyhow!(res));
        }
        let memory = std::ptr::slice_from_raw_parts_mut(ptr.cast(), size);
        let memory = SendSyncPtr::new(NonNull::new(memory).unwrap());
        Ok(Mmap { memory })
    }

    pub fn new(size: usize) -> Result<Self> {
        Self::new_internal(size, true)
    }

    pub fn reserve(size: usize) -> Result<Self> {
        Self::new_internal(size, false)
    }

    pub fn from_file(_path: &Path) -> Result<(Self, File)> {
        bail!("not supported on sgx");
    }

    pub fn make_accessible(&mut self, start: usize, len: usize) -> Result<()> {
        let start_addr = unsafe { self.memory.as_ptr().cast::<u8>().add(start).cast() };
        let mut ptr: *mut c_void = ptr::null_mut();
        let res = unsafe {
            sgx_mm_alloc(
                start_addr,
                len,
                2, // SGX_EMA_COMMIT_NOW
                ptr::null_mut(),
                ptr::null_mut(),
                &mut ptr
            )
        };
        if res != 0 {
            return Err(anyhow!(res));
        }
        let res = unsafe {
            sgx_mm_modify_permissions(
                start_addr,
                len,
                3 // SGX_EMA_PROT_READ_WRITE
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
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
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
        let page_size = crate::page_size();
        let len = (len + (page_size - 1)) & !(page_size - 1);

        let res = sgx_mm_modify_permissions(
            base,
            len,
            5 // SGX_EMA_PROT_READ_EXEC
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
        let page_size = crate::page_size();
        let len = (len + (page_size - 1)) & !(page_size - 1);

        let res = sgx_mm_modify_permissions(
            base,
            len,
            1 // SGX_EMA_PROT_READ
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
