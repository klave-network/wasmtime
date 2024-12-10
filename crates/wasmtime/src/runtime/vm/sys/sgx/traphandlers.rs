//! Trap handling on Unix based on POSIX signals.

use crate::prelude::Box;
use crate::runtime::vm::VMContext;
use crate::runtime::vm::traphandlers::{tls, TrapRegisters, TrapTest};
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
        callback: extern "C" fn(*mut u8, *mut VMContext) -> bool,
        payload: *mut u8,
        callee: *mut VMContext,
    ) -> bool;

    #[wasmtime_versioned_export_macros::versioned_link]
    pub fn wasmtime_longjmp(jmp_buf: *const u8) -> !;
}

/// Function which may handle custom signals while processing traps.
pub type SignalHandler =
    Box<dyn Fn(&mut ExceptionInfo) -> bool + Send + Sync>;

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
        let regs = unsafe { get_trap_registers(exception_info) };
        let faulting_addr = match exception_info {
            ExceptionInfo {
                vector: ExceptionVector::GP | ExceptionVector::PF,
                exinfo,
                ..
            } => Some(exinfo.faulting_address as usize),
            _ => None,
        };

        let test = info.test_if_trap(regs, faulting_addr, |_| false);

        // Figure out what to do based on the result of this handling of
        // the trap. Note that our sentinel value of 1 means that the
        // exception was handled by a custom exception handler, so we
        // keep executing.
        let jmp_buf = match test {
            TrapTest::NotWasm => return false,
            TrapTest::HandledByEmbedder => return true,
            TrapTest::Trap { jmp_buf } => jmp_buf,
        };

        unsafe { wasmtime_longjmp(jmp_buf) }
    });
    if handled {
        HandleResult::Execution
    } else {
        HandleResult::Search
    }
}

pub struct TrapHandler;

impl TrapHandler {
    pub unsafe fn new(macos_use_mach_ports: bool) -> TrapHandler {
        // Either mach ports shouldn't be in use or we shouldn't be on macOS,
        // otherwise the `machports.rs` module should be used instead.
        assert!(!macos_use_mach_ports || !cfg!(target_os = "macos"));

        let sgx_handler: ExceptionHandler = sgx_exception_handler;
        // don't use std(sgx_trts)::veh::register_exception, which is not "use_sgx_sdk" compatible
        sgx_register_exception_handler(1, sgx_handler);

        TrapHandler
    }

    pub fn validate_config(&self, macos_use_mach_ports: bool) {
        assert!(!macos_use_mach_ports || !cfg!(target_os = "macos"));
    }
}

unsafe fn get_trap_registers(exception_info: &mut ExceptionInfo) -> TrapRegisters {
    TrapRegisters {
        pc: exception_info.context.rip as usize,
        fp: exception_info.context.rbp as usize,
    }
}

pub fn lazy_per_thread_init() {}
