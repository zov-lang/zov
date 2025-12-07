//! Low-level LLVM FFI wrapper
//!
//! This module provides safe wrappers around the raw LLVM C API exposed by `llvm-sys`.
//! The design is inspired by rustc's `rustc_llvm` crate.
//!
//! # Safety
//!
//! All public functions in this module are safe to call, but internally they
//! use unsafe FFI calls. The wrappers ensure proper initialization, null checking,
//! and lifetime management.
//!
//! # Architecture
//!
//! The module is organized into several submodules:
//!
//! - `core`: Basic LLVM types (Context, Module, Type, Value)
//! - `builder`: IR builder for creating instructions
//! - `target`: Target machine configuration
//! - `pass`: Optimization pass management
//!
//! All LLVM objects are wrapped in Rust types that handle memory management.

#![cfg(feature = "llvm")]

use std::ffi::CStr;
use std::sync::Once;

// Re-export llvm-sys for internal use
pub use llvm_sys as sys;

static INIT: Once = Once::new();

/// Initialize LLVM subsystems.
///
/// This must be called before using any LLVM functionality.
/// It is safe to call multiple times; subsequent calls are no-ops.
pub fn init() {
    INIT.call_once(|| {
        unsafe {
            // Initialize all targets for code generation
            sys::target::LLVM_InitializeAllTargetInfos();
            sys::target::LLVM_InitializeAllTargets();
            sys::target::LLVM_InitializeAllTargetMCs();
            sys::target::LLVM_InitializeAllAsmPrinters();
            sys::target::LLVM_InitializeAllAsmParsers();
        }
    });
}

/// Returns the LLVM version string.
pub fn version() -> String {
    let major = unsafe { sys::core::LLVMGetMajorVersion() };
    let minor = unsafe { sys::core::LLVMGetMinorVersion() };
    let patch = unsafe { sys::core::LLVMGetPatchVersion() };
    format!("{}.{}.{}", major, minor, patch)
}

/// LLVM context wrapper.
///
/// The context owns all LLVM objects created within it. When the context
/// is dropped, all associated objects are freed.
pub struct Context {
    raw: sys::prelude::LLVMContextRef,
}

impl Context {
    /// Creates a new LLVM context.
    pub fn new() -> Self {
        let raw = unsafe { sys::core::LLVMContextCreate() };
        assert!(!raw.is_null(), "Failed to create LLVM context");
        Self { raw }
    }

    /// Returns the raw LLVM context reference.
    pub fn as_raw(&self) -> sys::prelude::LLVMContextRef {
        self.raw
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            sys::core::LLVMContextDispose(self.raw);
        }
    }
}

/// LLVM module wrapper.
///
/// A module contains functions and global variables. It is owned by
/// a context and must not outlive it.
pub struct Module<'ctx> {
    raw: sys::prelude::LLVMModuleRef,
    _context: std::marker::PhantomData<&'ctx Context>,
}

impl<'ctx> Module<'ctx> {
    /// Creates a new module in the given context.
    pub fn new(context: &'ctx Context, name: &str) -> Self {
        let c_name = std::ffi::CString::new(name).expect("Module name contains null byte");
        let raw = unsafe {
            sys::core::LLVMModuleCreateWithNameInContext(c_name.as_ptr(), context.as_raw())
        };
        assert!(!raw.is_null(), "Failed to create LLVM module");
        Self { raw, _context: std::marker::PhantomData }
    }

    /// Returns the raw LLVM module reference.
    pub fn as_raw(&self) -> sys::prelude::LLVMModuleRef {
        self.raw
    }

    /// Prints the module as LLVM IR to a string.
    pub fn to_string(&self) -> String {
        unsafe {
            let c_str = sys::core::LLVMPrintModuleToString(self.raw);
            if c_str.is_null() {
                return String::new();
            }
            let result = CStr::from_ptr(c_str).to_string_lossy().into_owned();
            sys::core::LLVMDisposeMessage(c_str);
            result
        }
    }

    /// Sets the target triple for this module.
    pub fn set_target_triple(&self, triple: &str) {
        let c_triple = std::ffi::CString::new(triple).expect("Triple contains null byte");
        unsafe {
            sys::core::LLVMSetTarget(self.raw, c_triple.as_ptr());
        }
    }
}

impl Drop for Module<'_> {
    fn drop(&mut self) {
        unsafe {
            sys::core::LLVMDisposeModule(self.raw);
        }
    }
}

/// LLVM type wrapper.
///
/// Types in LLVM are immutable and owned by the context.
#[derive(Clone, Copy)]
pub struct Type<'ctx> {
    raw: sys::prelude::LLVMTypeRef,
    _context: std::marker::PhantomData<&'ctx Context>,
}

impl<'ctx> Type<'ctx> {
    /// Creates a new type wrapper from a raw reference.
    ///
    /// # Safety
    ///
    /// The raw reference must be valid and owned by the associated context.
    pub unsafe fn from_raw(raw: sys::prelude::LLVMTypeRef) -> Self {
        Self { raw, _context: std::marker::PhantomData }
    }

    /// Returns the raw LLVM type reference.
    pub fn as_raw(self) -> sys::prelude::LLVMTypeRef {
        self.raw
    }

    /// Creates an i1 (boolean) type.
    pub fn i1(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt1TypeInContext(context.as_raw())) }
    }

    /// Creates an i8 type.
    pub fn i8(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt8TypeInContext(context.as_raw())) }
    }

    /// Creates an i16 type.
    pub fn i16(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt16TypeInContext(context.as_raw())) }
    }

    /// Creates an i32 type.
    pub fn i32(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt32TypeInContext(context.as_raw())) }
    }

    /// Creates an i64 type.
    pub fn i64(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt64TypeInContext(context.as_raw())) }
    }

    /// Creates an i128 type.
    pub fn i128(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMInt128TypeInContext(context.as_raw())) }
    }

    /// Creates an integer type with the specified bit width.
    pub fn int(context: &'ctx Context, bits: u32) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMIntTypeInContext(context.as_raw(), bits)) }
    }

    /// Creates a pointer type.
    pub fn ptr(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMPointerTypeInContext(context.as_raw(), 0)) }
    }

    /// Creates a void type.
    pub fn void(context: &'ctx Context) -> Self {
        unsafe { Self::from_raw(sys::core::LLVMVoidTypeInContext(context.as_raw())) }
    }

    /// Creates a function type.
    pub fn function(ret: Type<'ctx>, params: &[Type<'ctx>], is_var_arg: bool) -> Self {
        let mut param_types: Vec<_> = params.iter().map(|t| t.as_raw()).collect();
        unsafe {
            Self::from_raw(sys::core::LLVMFunctionType(
                ret.as_raw(),
                param_types.as_mut_ptr(),
                params.len() as u32,
                is_var_arg as i32,
            ))
        }
    }
}

/// LLVM value wrapper.
///
/// Values represent SSA values in LLVM IR.
#[derive(Clone, Copy)]
pub struct Value<'ctx> {
    raw: sys::prelude::LLVMValueRef,
    _context: std::marker::PhantomData<&'ctx Context>,
}

impl<'ctx> Value<'ctx> {
    /// Creates a new value wrapper from a raw reference.
    ///
    /// # Safety
    ///
    /// The raw reference must be valid and owned by the associated context.
    pub unsafe fn from_raw(raw: sys::prelude::LLVMValueRef) -> Self {
        Self { raw, _context: std::marker::PhantomData }
    }

    /// Returns the raw LLVM value reference.
    pub fn as_raw(self) -> sys::prelude::LLVMValueRef {
        self.raw
    }

    /// Returns the type of this value.
    pub fn get_type(self) -> Type<'ctx> {
        unsafe { Type::from_raw(sys::core::LLVMTypeOf(self.raw)) }
    }

    /// Sets the name of this value.
    pub fn set_name(self, name: &str) {
        let c_name = std::ffi::CString::new(name).expect("Name contains null byte");
        unsafe {
            sys::core::LLVMSetValueName2(self.raw, c_name.as_ptr(), name.len());
        }
    }
}

/// LLVM basic block wrapper.
#[derive(Clone, Copy)]
pub struct BasicBlock<'ctx> {
    raw: sys::prelude::LLVMBasicBlockRef,
    _context: std::marker::PhantomData<&'ctx Context>,
}

impl<'ctx> BasicBlock<'ctx> {
    /// Creates a new basic block wrapper from a raw reference.
    ///
    /// # Safety
    ///
    /// The raw reference must be valid and owned by the associated context.
    pub unsafe fn from_raw(raw: sys::prelude::LLVMBasicBlockRef) -> Self {
        Self { raw, _context: std::marker::PhantomData }
    }

    /// Returns the raw LLVM basic block reference.
    pub fn as_raw(self) -> sys::prelude::LLVMBasicBlockRef {
        self.raw
    }
}

/// LLVM IR builder wrapper.
pub struct Builder<'ctx> {
    raw: sys::prelude::LLVMBuilderRef,
    _context: std::marker::PhantomData<&'ctx Context>,
}

impl<'ctx> Builder<'ctx> {
    /// Creates a new IR builder in the given context.
    pub fn new(context: &'ctx Context) -> Self {
        let raw = unsafe { sys::core::LLVMCreateBuilderInContext(context.as_raw()) };
        assert!(!raw.is_null(), "Failed to create LLVM builder");
        Self { raw, _context: std::marker::PhantomData }
    }

    /// Positions the builder at the end of the given basic block.
    pub fn position_at_end(&self, block: BasicBlock<'ctx>) {
        unsafe {
            sys::core::LLVMPositionBuilderAtEnd(self.raw, block.as_raw());
        }
    }

    /// Creates an integer addition instruction.
    pub fn add(&self, lhs: Value<'ctx>, rhs: Value<'ctx>, name: &str) -> Value<'ctx> {
        let c_name = std::ffi::CString::new(name).expect("Name contains null byte");
        unsafe {
            Value::from_raw(sys::core::LLVMBuildAdd(
                self.raw,
                lhs.as_raw(),
                rhs.as_raw(),
                c_name.as_ptr(),
            ))
        }
    }

    /// Creates a return instruction.
    pub fn ret(&self, value: Value<'ctx>) -> Value<'ctx> {
        unsafe { Value::from_raw(sys::core::LLVMBuildRet(self.raw, value.as_raw())) }
    }

    /// Creates a void return instruction.
    pub fn ret_void(&self) -> Value<'ctx> {
        unsafe { Value::from_raw(sys::core::LLVMBuildRetVoid(self.raw)) }
    }
}

impl Drop for Builder<'_> {
    fn drop(&mut self) {
        unsafe {
            sys::core::LLVMDisposeBuilder(self.raw);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init() {
        init();
        // Should be safe to call multiple times
        init();
    }

    #[test]
    fn test_version() {
        init();
        let ver = version();
        assert!(!ver.is_empty());
        // Version should be something like "19.0.0"
        assert!(ver.contains('.'));
    }

    #[test]
    fn test_context_creation() {
        init();
        let _context = Context::new();
        // Context should be dropped properly
    }

    #[test]
    fn test_module_creation() {
        init();
        let context = Context::new();
        let module = Module::new(&context, "test");
        let ir = module.to_string();
        assert!(ir.contains("test"));
    }

    #[test]
    fn test_types() {
        init();
        let context = Context::new();

        let _i1 = Type::i1(&context);
        let _i8 = Type::i8(&context);
        let _i16 = Type::i16(&context);
        let _i32 = Type::i32(&context);
        let _i64 = Type::i64(&context);
        let _i128 = Type::i128(&context);
        let _ptr = Type::ptr(&context);
        let _void = Type::void(&context);

        // Custom width
        let _i256 = Type::int(&context, 256);
    }
}
