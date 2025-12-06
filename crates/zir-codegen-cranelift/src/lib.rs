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
    use cranelift_module::Module;
    use zir::idx::Idx;
    use zir::intern::InternSet;
    use zir::mir::*;
    use zir::ty::*;
    use zir::{Arena, IndexVec};

    #[test]
    fn test_create_jit_module() {
        let module = create_jit_module();
        assert!(module.is_ok());
    }

    /// Helper to create a simple function that returns a constant.
    fn create_const_function<'a>(arena: &'a Arena<'a>, value: i64) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });

        let mut body = Body::new(local_decls, 0);

        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Const(
                    ConstValue::Scalar(ScalarRepr::from_u64(value as u64)),
                    i64_ty,
                )),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb0);

        body
    }

    /// Helper to create an add function: fn add(a: i64, b: i64) -> i64 { a + b }
    fn create_add_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        // _0: return place
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        // _1: first argument (a)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _2: second argument (b)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });

        let mut body = Body::new(local_decls, 2);

        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::from_local(Local::new(1))),
                    Operand::Copy(Place::from_local(Local::new(2))),
                ),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb0);

        body
    }

    /// Helper to create a max function with branching.
    fn create_max_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
        let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        // _0: return place
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        // _1: first argument (a)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _2: second argument (b)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _3: comparison result
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

        let mut body = Body::new(local_decls, 2);

        // bb0: _3 = Gt(_1, _2); switchInt(_3) -> [0: bb2, otherwise: bb1]
        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(3)),
                Rvalue::BinaryOp(
                    BinOp::Gt,
                    Operand::Copy(Place::from_local(Local::new(1))),
                    Operand::Copy(Place::from_local(Local::new(2))),
                ),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(Local::new(3))),
                targets: SwitchTargets::if_else(0, BasicBlock::new(2), BasicBlock::new(1)),
            },
        });
        body.basic_blocks.push(bb0);

        // bb1 (true branch): _0 = copy _1; goto -> bb3
        let mut bb1 = BasicBlockData::new();
        bb1.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Copy(Place::from_local(Local::new(1)))),
            ),
        });
        bb1.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Goto { target: BasicBlock::new(3) },
        });
        body.basic_blocks.push(bb1);

        // bb2 (false branch): _0 = copy _2; goto -> bb3
        let mut bb2 = BasicBlockData::new();
        bb2.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Copy(Place::from_local(Local::new(2)))),
            ),
        });
        bb2.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Goto { target: BasicBlock::new(3) },
        });
        body.basic_blocks.push(bb2);

        // bb3 (join point): return
        let mut bb3 = BasicBlockData::new();
        bb3.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb3);

        body
    }

    /// Compiles a MIR body to CLIF IR and returns the textual representation.
    fn compile_to_clif(body: &Body<'_>, sig: Signature) -> CodegenResult<String> {
        let module = create_jit_module()?;
        let mut ctx = CodegenContext::new(module);
        ctx.compile_to_clif(body, sig)
    }

    #[test]
    fn test_clif_const_42() {
        let arena = Arena::new();
        let body = create_const_function(&arena, 42);

        // Build signature for () -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        let clif = compile_to_clif(&body, sig).unwrap();
        insta::assert_snapshot!(clif);
    }

    #[test]
    fn test_clif_const_negative() {
        let arena = Arena::new();
        let body = create_const_function(&arena, -123);

        // Build signature for () -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        let clif = compile_to_clif(&body, sig).unwrap();
        insta::assert_snapshot!(clif);
    }

    #[test]
    fn test_clif_add_function() {
        let arena = Arena::new();
        let body = create_add_function(&arena);

        // Create signature: (i64, i64) -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let clif = compile_to_clif(&body, sig).unwrap();
        insta::assert_snapshot!(clif);
    }

    #[test]
    fn test_clif_max_function() {
        let arena = Arena::new();
        let body = create_max_function(&arena);

        // Create signature: (i64, i64) -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let clif = compile_to_clif(&body, sig).unwrap();
        insta::assert_snapshot!(clif);
    }
}
