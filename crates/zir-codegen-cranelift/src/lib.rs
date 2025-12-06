//! Cranelift code generation backend for ZIR
//!
//! Translates ZIR MIR to Cranelift IR and generates native code.

mod analyze;
mod context;
mod place;
mod value;

pub use context::{CodegenContext, FunctionCodegen};
use cranelift::prelude::*;
use cranelift_codegen::ir::types;
use cranelift_codegen::isa::TargetIsa;
use cranelift_jit::{JITBuilder, JITModule};
use zir::ty::{IntWidth, Ty, TyKind};

/// Configuration for code generation.
#[derive(Clone, Debug)]
pub struct CodegenConfig {
    /// Whether to enable optimizations.
    pub optimize: bool,
    /// Whether to emit debug info.
    pub debug_info: bool,
}

impl Default for CodegenConfig {
    fn default() -> Self {
        Self { optimize: true, debug_info: false }
    }
}

/// Result type for codegen operations.
pub type CodegenResult<T> = Result<T, CodegenError>;

/// Errors that can occur during code generation.
#[derive(Debug)]
pub enum CodegenError {
    /// Cranelift module error.
    Module(String),
    /// Unsupported type.
    UnsupportedType(String),
    /// Invalid MIR.
    InvalidMir(String),
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenError::Module(msg) => write!(f, "module error: {}", msg),
            CodegenError::UnsupportedType(ty) => write!(f, "unsupported type: {}", ty),
            CodegenError::InvalidMir(msg) => write!(f, "invalid MIR: {}", msg),
        }
    }
}

impl std::error::Error for CodegenError {}

/// Creates a JIT module for the current target.
pub fn create_jit_module() -> CodegenResult<JITModule> {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();

    let isa_builder =
        cranelift_native::builder().map_err(|e| CodegenError::Module(e.to_string()))?;

    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CodegenError::Module(e.to_string()))?;

    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    let module = JITModule::new(builder);

    Ok(module)
}

/// Converts a ZIR type to a Cranelift type.
pub fn clif_type<'zir>(ty: Ty<'zir>, ptr_type: types::Type) -> Option<types::Type> {
    match &*ty {
        TyKind::Bool => Some(types::I8),
        TyKind::Int(width) | TyKind::Uint(width) => int_width_to_clif(*width, ptr_type),
        TyKind::Ptr(..) | TyKind::Ref(..) => Some(ptr_type),
        TyKind::Unit => None,
        TyKind::Tuple(elems) if elems.is_empty() => None,
        TyKind::Never => None,
        _ => None,
    }
}

/// Converts an integer width to a Cranelift type.
fn int_width_to_clif(width: IntWidth, ptr_type: types::Type) -> Option<types::Type> {
    match width {
        IntWidth::Size => Some(ptr_type),
        IntWidth::Fixed(bits) => match bits {
            1..=8 => Some(types::I8),
            9..=16 => Some(types::I16),
            17..=32 => Some(types::I32),
            33..=64 => Some(types::I64),
            65..=128 => Some(types::I128),
            _ => None, // Larger types need special handling
        },
    }
}

/// Returns the pointer type for the target.
pub fn pointer_type(isa: &dyn TargetIsa) -> types::Type {
    isa.pointer_type()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_jit_module() {
        let module = create_jit_module();
        assert!(module.is_ok());
    }
}
