//! Backend-agnostic code generation traits for ZIR
//!
//! This crate provides the abstraction layer for code generation backends.
//! It defines traits that allow different backends (Cranelift, LLVM, etc.)
//! to implement code generation in a unified way.
//!
//! # Design
//!
//! The design is inspired by rustc's `rustc_codegen_ssa` crate, which provides
//! backend-agnostic functions that depend on traits implemented by each backend.
//!
//! # Key Traits
//!
//! - [`CodegenBackend`]: The main trait for code generation backends
//!
//! # Testing
//!
//! The [`testing`] module provides utilities for writing backend-agnostic
//! tests that can verify any implementation of [`CodegenBackend`].
//!
//! # Example
//!
//! ```ignore
//! use zir_codegen::{CodegenBackend, CodegenConfig, CodegenResult};
//!
//! let backend = SomeCraneliftBackend::new(CodegenConfig::default())?;
//! let result = backend.compile_function(body, signature)?;
//! ```

pub mod testing;

use std::any::Any;
use std::fmt;

use zir::mir::Body;

/// Configuration for code generation.
#[derive(Clone, Debug, Default)]
pub struct CodegenConfig {
    /// Whether to enable optimizations.
    pub optimize: bool,
    /// Whether to emit debug info.
    pub debug_info: bool,
}

/// Errors that can occur during code generation.
#[derive(Debug)]
pub enum CodegenError {
    /// Backend-specific module error.
    Module(String),
    /// Unsupported type.
    UnsupportedType(String),
    /// Invalid MIR.
    InvalidMir(String),
    /// Backend not available.
    BackendUnavailable(String),
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodegenError::Module(msg) => write!(f, "module error: {}", msg),
            CodegenError::UnsupportedType(ty) => write!(f, "unsupported type: {}", ty),
            CodegenError::InvalidMir(msg) => write!(f, "invalid MIR: {}", msg),
            CodegenError::BackendUnavailable(msg) => write!(f, "backend unavailable: {}", msg),
        }
    }
}

impl std::error::Error for CodegenError {}

/// Result type for codegen operations.
pub type CodegenResult<T> = Result<T, CodegenError>;

/// Compiled module output.
///
/// This struct represents the result of compiling a module,
/// containing the object code and any metadata.
#[derive(Debug)]
pub struct CompiledModule {
    /// Name of the compiled module.
    pub name: String,
    /// Path to the object file, if emitted.
    pub object_path: Option<std::path::PathBuf>,
    /// Raw object code, if kept in memory.
    pub object_code: Option<Vec<u8>>,
}

/// Code generation results from a backend.
#[derive(Debug, Default)]
pub struct CodegenResults {
    /// Compiled modules.
    pub modules: Vec<CompiledModule>,
}

/// IR output format for testing and debugging.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrOutput {
    /// Textual IR representation (e.g., CLIF for Cranelift).
    Text(String),
    /// Binary IR representation.
    Binary(Vec<u8>),
}

/// Function signature for code generation.
///
/// This is a backend-agnostic representation of a function signature.
#[derive(Clone, Debug, Default)]
pub struct FunctionSignature {
    /// Parameter types.
    pub params: Vec<TypeDesc>,
    /// Return types.
    pub returns: Vec<TypeDesc>,
}

/// Type descriptor for function signatures.
#[derive(Clone, Debug)]
pub enum TypeDesc {
    /// Boolean type.
    Bool,
    /// Signed integer with bit width.
    Int(u32),
    /// Unsigned integer with bit width.
    Uint(u32),
    /// Pointer-sized signed integer.
    Isize,
    /// Pointer-sized unsigned integer.
    Usize,
    /// Pointer type.
    Ptr,
}

impl FunctionSignature {
    /// Creates a new empty signature.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a parameter type.
    pub fn with_param(mut self, ty: TypeDesc) -> Self {
        self.params.push(ty);
        self
    }

    /// Adds a return type.
    pub fn with_return(mut self, ty: TypeDesc) -> Self {
        self.returns.push(ty);
        self
    }
}

/// The main trait for code generation backends.
///
/// This trait abstracts over different code generation backends
/// (Cranelift, LLVM, etc.) and provides a unified interface for
/// compiling MIR to machine code.
///
/// # Backend Responsibilities
///
/// Backends implementing this trait should:
/// 1. Initialize their internal state in `new()`
/// 2. Compile MIR functions to their native IR in `compile_function()`
/// 3. Emit final object code or execute JIT in `finalize()`
///
/// # Example Implementation
///
/// ```ignore
/// struct MyCraneliftBackend { /* ... */ }
///
/// impl CodegenBackend for MyCraneliftBackend {
///     fn compile_function<'zir>(
///         &mut self,
///         body: &Body<'zir>,
///         signature: FunctionSignature,
///     ) -> CodegenResult<()> {
///         // Convert MIR to Cranelift IR
///         // Add to module
///         Ok(())
///     }
///
///     fn compile_to_ir<'zir>(
///         &mut self,
///         body: &Body<'zir>,
///         signature: FunctionSignature,
///     ) -> CodegenResult<IrOutput> {
///         // Return CLIF text representation
///         Ok(IrOutput::Text(clif_text))
///     }
///
///     fn finalize(self: Box<Self>) -> CodegenResult<CodegenResults> {
///         // Finalize the module and return compiled code
///         Ok(CodegenResults::default())
///     }
/// }
/// ```
pub trait CodegenBackend: Any {
    /// Returns the name of this backend.
    fn name(&self) -> &'static str;

    /// Compiles a MIR function body.
    ///
    /// This method translates MIR to the backend's native IR format
    /// and adds it to the current module being built.
    fn compile_function<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<()>;

    /// Compiles a MIR function and returns the IR representation.
    ///
    /// This method is useful for testing the code generation output
    /// without actually executing the generated code. The returned
    /// IR can be compared against expected snapshots.
    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<IrOutput>;

    /// Finalizes the compilation and returns the results.
    ///
    /// After all functions have been compiled, this method finalizes
    /// the module and produces the final output (object files, etc.).
    fn finalize(self: Box<Self>) -> CodegenResult<CodegenResults>;

    /// Returns the configuration for this backend.
    fn config(&self) -> &CodegenConfig;
}

/// Factory function type for creating backends.
pub type BackendFactory = fn(CodegenConfig) -> CodegenResult<Box<dyn CodegenBackend>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen_config_default() {
        let config = CodegenConfig::default();
        assert!(!config.optimize);
        assert!(!config.debug_info);
    }

    #[test]
    fn test_function_signature_builder() {
        let sig = FunctionSignature::new()
            .with_param(TypeDesc::Int(64))
            .with_param(TypeDesc::Int(64))
            .with_return(TypeDesc::Int(64));

        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
    }

    #[test]
    fn test_codegen_error_display() {
        let err = CodegenError::Module("test error".into());
        assert_eq!(err.to_string(), "module error: test error");

        let err = CodegenError::UnsupportedType("i256".into());
        assert_eq!(err.to_string(), "unsupported type: i256");

        let err = CodegenError::InvalidMir("bad block".into());
        assert_eq!(err.to_string(), "invalid MIR: bad block");

        let err = CodegenError::BackendUnavailable("LLVM".into());
        assert_eq!(err.to_string(), "backend unavailable: LLVM");
    }

    #[test]
    fn test_ir_output_equality() {
        let text1 = IrOutput::Text("function f() {}".into());
        let text2 = IrOutput::Text("function f() {}".into());
        let text3 = IrOutput::Text("function g() {}".into());

        assert_eq!(text1, text2);
        assert_ne!(text1, text3);
    }
}
