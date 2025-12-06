//! Cranelift code generation backend for ZIR
//!
//! Translates ZIR MIR to Cranelift IR and generates native code.
//!
//! This crate implements the [`zir_codegen::CodegenBackend`] trait
//! using Cranelift as the code generation backend.
//!
//! # Example
//!
//! ```ignore
//! use zir_codegen::{CodegenBackend, CodegenConfig, FunctionSignature, TypeDesc};
//! use zir_codegen_cranelift::CraneliftBackend;
//!
//! // Create a backend
//! let mut backend = CraneliftBackend::new(CodegenConfig::default())?;
//!
//! // Compile a function
//! let sig = FunctionSignature::new()
//!     .with_param(TypeDesc::Int(64))
//!     .with_return(TypeDesc::Int(64));
//! let ir = backend.compile_to_ir(&body, sig)?;
//! ```

mod analyze;
mod context;
mod place;
mod value;

pub use context::{CodegenContext, FunctionCodegen};
use cranelift::prelude::*;
use cranelift_codegen::ir::types;
use cranelift_codegen::isa::TargetIsa;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::Module;
use zir::mir::Body;
use zir::ty::{IntWidth, Ty, TyKind};
use zir_codegen::{
    CodegenBackend, CodegenConfig, CodegenError, CodegenResult, CodegenResults, FunctionSignature,
    IrOutput, TypeDesc,
};

/// Cranelift-based code generation backend.
///
/// This backend uses Cranelift to generate native code from ZIR MIR.
/// It supports both JIT compilation and object file generation.
pub struct CraneliftBackend {
    /// The codegen context.
    ctx: CodegenContext<JITModule>,
    /// Configuration for this backend.
    config: CodegenConfig,
}

impl CraneliftBackend {
    /// Creates a new Cranelift backend.
    pub fn new(config: CodegenConfig) -> CodegenResult<Self> {
        let module = create_jit_module()?;
        let ctx = CodegenContext::new(module);
        Ok(Self { ctx, config })
    }

    /// Returns a reference to the underlying codegen context.
    pub fn context(&self) -> &CodegenContext<JITModule> {
        &self.ctx
    }

    /// Returns a mutable reference to the underlying codegen context.
    pub fn context_mut(&mut self) -> &mut CodegenContext<JITModule> {
        &mut self.ctx
    }

    /// Converts a backend-agnostic signature to a Cranelift signature.
    fn convert_signature(&self, sig: &FunctionSignature) -> Signature {
        let mut clif_sig = self.ctx.module.make_signature();

        for param in &sig.params {
            if let Some(ty) = type_desc_to_clif(param, self.ctx.ptr_type) {
                clif_sig.params.push(AbiParam::new(ty));
            }
        }

        for ret in &sig.returns {
            if let Some(ty) = type_desc_to_clif(ret, self.ctx.ptr_type) {
                clif_sig.returns.push(AbiParam::new(ty));
            }
        }

        clif_sig
    }
}

impl CodegenBackend for CraneliftBackend {
    fn name(&self) -> &'static str {
        "cranelift"
    }

    fn compile_function<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<()> {
        let clif_sig = self.convert_signature(&signature);
        let func_id = self
            .ctx
            .declare_function("_anon", clif_sig.clone())
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        self.ctx
            .define_function(func_id, body, clif_sig)
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        Ok(())
    }

    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<IrOutput> {
        let clif_sig = self.convert_signature(&signature);
        let clif_text = self
            .ctx
            .compile_to_clif(body, clif_sig)
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        Ok(IrOutput::Text(clif_text))
    }

    fn finalize(self: Box<Self>) -> CodegenResult<CodegenResults> {
        // For JIT, we don't produce object files
        Ok(CodegenResults::default())
    }

    fn config(&self) -> &CodegenConfig {
        &self.config
    }
}

/// Converts a [`TypeDesc`] to a Cranelift type.
fn type_desc_to_clif(ty: &TypeDesc, ptr_type: types::Type) -> Option<types::Type> {
    match ty {
        TypeDesc::Bool => Some(types::I8),
        TypeDesc::Int(bits) | TypeDesc::Uint(bits) => match *bits {
            1..=8 => Some(types::I8),
            9..=16 => Some(types::I16),
            17..=32 => Some(types::I32),
            33..=64 => Some(types::I64),
            65..=128 => Some(types::I128),
            _ => None,
        },
        TypeDesc::Isize | TypeDesc::Usize | TypeDesc::Ptr => Some(ptr_type),
    }
}

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

/// Creates a Cranelift backend as a boxed trait object.
///
/// This is the factory function for creating Cranelift backends in a
/// backend-agnostic way. It returns a `Box<dyn CodegenBackend>` which
/// can be used with the testing utilities in `zir_codegen::testing`.
///
/// # Example
///
/// ```ignore
/// use zir_codegen::{CodegenConfig, testing::run_standard_tests};
/// use zir_codegen_cranelift::create_backend;
///
/// let results = run_standard_tests(create_backend)?;
/// ```
pub fn create_backend(config: CodegenConfig) -> CodegenResult<Box<dyn CodegenBackend>> {
    Ok(Box::new(CraneliftBackend::new(config)?))
}
