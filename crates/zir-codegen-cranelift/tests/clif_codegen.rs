//! CLIF codegen tests for zir-codegen-cranelift
//!
//! These tests verify that MIR is correctly compiled to Cranelift IR (CLIF).
//! We use the backend-agnostic `CodegenBackend` trait and snapshot testing
//! to compare the generated CLIF output.

use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir::{Arena, IndexVec};
use zir_codegen::{CodegenBackend, CodegenConfig, FunctionSignature, IrOutput, TypeDesc};
use zir_codegen_cranelift::CraneliftBackend;

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

/// Compiles a MIR body to CLIF IR using the backend-agnostic trait.
fn compile_to_clif(body: &Body<'_>, sig: FunctionSignature) -> zir_codegen::CodegenResult<String> {
    let mut backend = CraneliftBackend::new(CodegenConfig::default())?;
    let ir = backend.compile_to_ir(body, sig)?;
    match ir {
        IrOutput::Text(text) => Ok(text),
        IrOutput::Binary(_) => panic!("Expected text output"),
    }
}

#[test]
fn test_backend_name() {
    let backend = CraneliftBackend::new(CodegenConfig::default()).unwrap();
    assert_eq!(backend.name(), "cranelift");
}

#[test]
fn test_clif_const_42() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 42);

    // Build signature for () -> i64
    let sig = FunctionSignature::new().with_return(TypeDesc::Int(64));

    let clif = compile_to_clif(&body, sig).unwrap();
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_const_negative() {
    let arena = Arena::new();
    let body = create_const_function(&arena, -123);

    // Build signature for () -> i64
    let sig = FunctionSignature::new().with_return(TypeDesc::Int(64));

    let clif = compile_to_clif(&body, sig).unwrap();
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_add_function() {
    let arena = Arena::new();
    let body = create_add_function(&arena);

    // Create signature: (i64, i64) -> i64
    let sig = FunctionSignature::new()
        .with_param(TypeDesc::Int(64))
        .with_param(TypeDesc::Int(64))
        .with_return(TypeDesc::Int(64));

    let clif = compile_to_clif(&body, sig).unwrap();
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_max_function() {
    let arena = Arena::new();
    let body = create_max_function(&arena);

    // Create signature: (i64, i64) -> i64
    let sig = FunctionSignature::new()
        .with_param(TypeDesc::Int(64))
        .with_param(TypeDesc::Int(64))
        .with_return(TypeDesc::Int(64));

    let clif = compile_to_clif(&body, sig).unwrap();
    insta::assert_snapshot!(clif);
}
