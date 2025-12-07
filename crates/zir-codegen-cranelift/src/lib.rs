//! Cranelift code generation backend for ZIR.

mod analyze;
mod context;
mod place;
mod value;

use std::collections::HashMap;
use std::io::Write;

pub use context::{CodegenContext, FunctionCodegen};
use cranelift::prelude::*;
use cranelift_codegen::ir::types;
use cranelift_codegen::isa::TargetIsa;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::Module;
use zir::mir::Body;
use zir::ty::{IntWidth, Ty, TyKind};
use zir_codegen::{
    CodegenBackend, CodegenConfig, CodegenResults, CodegenUnit, CompiledModule, FunctionSignature,
    OngoingCodegen, OutputFilenames, Result, Session, TargetConfig, TypeDesc, WorkProduct,
    WorkProductId,
};

pub struct CraneliftBackend {
    ctx: CodegenContext<JITModule>,
}

struct CraneliftCodegenResult {
    modules: Vec<CompiledModule>,
}

impl CraneliftBackend {
    pub fn new() -> Self {
        let module = create_jit_module();
        let ctx = CodegenContext::new(module);
        Self { ctx }
    }

    pub fn context(&self) -> &CodegenContext<JITModule> {
        &self.ctx
    }

    pub fn context_mut(&mut self) -> &mut CodegenContext<JITModule> {
        &mut self.ctx
    }

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

    fn target_config(&self, _sess: &Session) -> TargetConfig {
        TargetConfig {
            target_features: vec![],
            unstable_target_features: vec![],
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
        }
    }

    fn print(&self, out: &mut dyn Write) {
        writeln!(out, "Cranelift backend").unwrap();
        writeln!(out, "  pointer type: {}", self.ctx.ptr_type).unwrap();
    }

    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> Result<OngoingCodegen> {
        let mut modules = Vec::new();

        for (idx, (body, signature)) in unit.bodies.iter().enumerate() {
            let clif_sig = self.convert_signature(signature);
            let clif_text = self.ctx.compile_to_clif(body, clif_sig)?;

            // Create a compiled module with IR text for in-memory testing
            let module_name = format!("{}_{}", unit.name, idx);
            let module = CompiledModule::with_ir_text(module_name, clif_text);
            modules.push(module);
        }

        Ok(Box::new(CraneliftCodegenResult { modules }))
    }

    fn join_codegen(
        &self,
        ongoing: OngoingCodegen,
        _sess: &Session,
        _outputs: &OutputFilenames,
    ) -> (CodegenResults, HashMap<WorkProductId, WorkProduct>) {
        // Downcast the ongoing codegen to our internal type
        let result = ongoing
            .downcast::<CraneliftCodegenResult>()
            .expect("invalid ongoing codegen type - expected CraneliftCodegenResult");

        // Return the compiled modules with their IR text
        let results = CodegenResults { modules: result.modules, linker_args: Vec::new() };

        (results, HashMap::new())
    }

    fn link(&self, _sess: &Session, _results: CodegenResults, _outputs: &OutputFilenames) {}

    fn config(&self) -> CodegenConfig {
        CodegenConfig::default()
    }

    fn compile_function<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> Result<()> {
        let clif_sig = self.convert_signature(&signature);
        let func_id = self.ctx.declare_function("_anon", clif_sig.clone())?;
        self.ctx.define_function(func_id, body, clif_sig)?;
        Ok(())
    }

    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> Result<String> {
        let clif_sig = self.convert_signature(&signature);
        self.ctx.compile_to_clif(body, clif_sig)
    }

    fn finalize(self: Box<Self>) -> CodegenResults {
        CodegenResults::default()
    }
}

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

pub fn create_jit_module() -> JITModule {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();

    let isa_builder = cranelift_native::builder().expect("failed to create ISA builder");

    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("failed to finish ISA builder");

    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    JITModule::new(builder)
}

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

fn int_width_to_clif(width: IntWidth, ptr_type: types::Type) -> Option<types::Type> {
    match width {
        IntWidth::Size => Some(ptr_type),
        IntWidth::Fixed(bits) => match bits {
            1..=8 => Some(types::I8),
            9..=16 => Some(types::I16),
            17..=32 => Some(types::I32),
            33..=64 => Some(types::I64),
            65..=128 => Some(types::I128),
            _ => None,
        },
    }
}

pub fn pointer_type(isa: &dyn TargetIsa) -> types::Type {
    isa.pointer_type()
}

impl Default for CraneliftBackend {
    fn default() -> Self {
        Self::new()
    }
}
