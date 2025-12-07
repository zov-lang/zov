//! Backend-agnostic testing utilities for code generation.

use crate::{CodegenBackend, CodegenConfig, FunctionSignature, Result, TypeDesc};
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir::{Arena, IndexVec};

/// Creates a simple function that returns a constant i64 value.
pub fn create_const_function<'a>(arena: &'a Arena<'a>, value: i64) -> Body<'a> {
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

/// Creates an add function: `fn add(a: i64, b: i64) -> i64 { a + b }`
pub fn create_add_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
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

/// Creates a max function with branching: `fn max(a: i64, b: i64) -> i64`
pub fn create_max_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
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

pub fn sig_void_to_i64() -> FunctionSignature {
    FunctionSignature::new().with_return(TypeDesc::Int(64))
}

pub fn sig_i64_i64_to_i64() -> FunctionSignature {
    FunctionSignature::new()
        .with_param(TypeDesc::Int(64))
        .with_param(TypeDesc::Int(64))
        .with_return(TypeDesc::Int(64))
}

pub fn compile_to_ir_text(
    backend: &mut dyn CodegenBackend,
    body: &Body<'_>,
    sig: FunctionSignature,
) -> Result<String> {
    backend.compile_to_ir(body, sig)
}

pub struct CodegenTestCase<'a> {
    pub name: &'static str,
    pub body: Body<'a>,
    pub signature: FunctionSignature,
}

impl<'a> CodegenTestCase<'a> {
    pub fn new(name: &'static str, body: Body<'a>, signature: FunctionSignature) -> Self {
        Self { name, body, signature }
    }

    pub fn run(&self, backend: &mut dyn CodegenBackend) -> Result<String> {
        compile_to_ir_text(backend, &self.body, self.signature.clone())
    }
}

pub fn standard_test_cases<'a>(arena: &'a Arena<'a>) -> Vec<CodegenTestCase<'a>> {
    vec![
        CodegenTestCase::new("const_42", create_const_function(arena, 42), sig_void_to_i64()),
        CodegenTestCase::new(
            "const_negative",
            create_const_function(arena, -123),
            sig_void_to_i64(),
        ),
        CodegenTestCase::new("add_function", create_add_function(arena), sig_i64_i64_to_i64()),
        CodegenTestCase::new("max_function", create_max_function(arena), sig_i64_i64_to_i64()),
    ]
}

pub fn run_standard_tests<F>(factory: F) -> Result<Vec<(&'static str, String)>>
where
    F: Fn(CodegenConfig) -> Box<dyn CodegenBackend>,
{
    let arena = Arena::new();
    let test_cases = standard_test_cases(&arena);
    let mut results = Vec::new();

    for test in &test_cases {
        let mut backend = factory(CodegenConfig::default());
        let ir = test.run(backend.as_mut())?;
        results.push((test.name, ir));
    }

    Ok(results)
}
