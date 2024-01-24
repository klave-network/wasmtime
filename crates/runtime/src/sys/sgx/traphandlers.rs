//! Trap handling on Unix based on POSIX signals.

use crate::traphandlers::tls;
use crate::VMContext;
use std::veh::{ExceptionHandler, ExceptionInfo, ExceptionVector, HandleResult};

extern "C" {
    fn sgx_register_exception_handler(
        first: i32,
        handler: ExceptionHandler,
    ) -> *const std::ffi::c_void;
}

#[link(name = "wasmtime-helpers")]
extern "C" {
    #[wasmtime_versioned_export_macros::versioned_link]
    #[allow(improper_ctypes)]
    pub fn wasmtime_setjmp(
        jmp_buf: *mut *const u8,
        callback: extern "C" fn(*mut u8, *mut VMContext),
        payload: *mut u8,
        callee: *mut VMContext,
    ) -> i32;

    #[wasmtime_versioned_export_macros::versioned_link]
    pub fn wasmtime_longjmp(jmp_buf: *const u8) -> !;
}

/// Function which may handle custom signals while processing traps.
pub type SignalHandler<'a> =
    dyn Fn(&mut ExceptionInfo) -> bool + Send + Sync + 'a;

extern "C" fn sgx_exception_handler(exception_info: &mut ExceptionInfo) -> HandleResult {
    let handled = tls::with(|info| {
        // If no wasm code is executing, we don't handle this as a wasm
        // trap.
        let info = match info {
            Some(info) => info,
            None => return false,
        };

        // If we hit an exception while handling a previous trap, that's
        // quite bad, so bail out and let the system handle this
        // recursive segfault.
        //
        // Otherwise flag ourselves as handling a trap, do the trap
        // handling, and reset our trap handling flag. Then we figure
        // out what to do based on the result of the trap handling.
        let (pc, fp) = unsafe { get_pc_and_fp(exception_info) };
        // let jmp_buf = info.take_jmp_buf_if_trap(pc, |handler| handler(signum, siginfo, context));
        let jmp_buf = info.take_jmp_buf_if_trap(pc, |_| false);

        // Figure out what to do based on the result of this handling of
        // the trap. Note that our sentinel value of 1 means that the
        // exception was handled by a custom exception handler, so we
        // keep executing.
        if jmp_buf.is_null() {
            return false;
        }
        if jmp_buf as usize == 1 {
            return true;
        }
        let faulting_addr = match exception_info {
            ExceptionInfo { vector: ExceptionVector::GP | ExceptionVector::PF, exinfo, .. } => Some(exinfo.faulting_address as usize),
            _ => None,
        };
        info.set_jit_trap(pc, fp, faulting_addr);
        unsafe { wasmtime_longjmp(jmp_buf) }
    });
    if handled {
        HandleResult::Execution
    }
    else {
        HandleResult::Search
    }
}

#[no_mangle]
pub unsafe fn platform_init(macos_use_mach_ports: bool) {
    // Either mach ports shouldn't be in use or we shouldn't be on macOS,
    // otherwise the `machports.rs` module should be used instead.
    assert!(!macos_use_mach_ports || !cfg!(target_os = "macos"));

    let sgx_handler: ExceptionHandler = sgx_exception_handler;
    // don't use std(sgx_trts)::veh::register_exception, which is not "use_sgx_sdk" compatible
    sgx_register_exception_handler(1, sgx_handler);
}

unsafe fn get_pc_and_fp(exception_info: &mut ExceptionInfo) -> (*const u8, usize) {
    (
        exception_info.context.rip  as *const u8,
        exception_info.context.rbp  as usize
    )
}

pub fn lazy_per_thread_init() {}
