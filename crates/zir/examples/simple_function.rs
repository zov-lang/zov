//! Example: Creating and printing MIR for a simple function
//!
//! This demonstrates how to:
//! - Create arenas for memory allocation
//! - Define types using the type system
//! - Build MIR with basic blocks, statements, and terminators
//! - Pretty print the MIR

use zir::arena::Arena;
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir::IndexVec;

fn main() {
    println!("ZIR Example: Simple Function");
    println!("=============================\n");

    // Create arena for allocations
    let arena = Arena::new();

    // Create type intern set for deduplication
    let types = InternSet::new();

    // Intern common types
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| arena.dropless.alloc(kind));

    // Build: fn add(a: i64, b: i64) -> i64 { a + b }
    let add_body = build_add_function(&arena, i64_ty);
    println!("{}", add_body.pretty_with_name("add"));

    // Build: fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
    let bool_ty = types.intern(TyKind::Bool, |kind| arena.dropless.alloc(kind));
    let max_body = build_max_function(&arena, i64_ty, bool_ty);
    println!("{}", max_body.pretty_with_name("max"));

    // Build: fn count_to_n(n: i64) -> i64 { let mut i = 0; while i < n { i += 1; } i }
    let loop_body = build_loop_function(&arena, i64_ty, bool_ty);
    println!("{}", loop_body.pretty_with_name("count_to_n"));
}

/// Build MIR for: fn add(a: i64, b: i64) -> i64 { a + b }
fn build_add_function<'zir>(_arena: &'zir Arena, i64_ty: Ty<'zir>) -> Body<'zir> {
    // Local declarations:
    // _0: return place (i64)
    // _1: arg a (i64)
    // _2: arg b (i64)
    let mut local_decls = IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });

    let mut body = Body::new(local_decls, 2);

    // bb0: { _0 = Add(_1, _2); return; }
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

/// Build MIR for: fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
fn build_max_function<'zir>(_arena: &'zir Arena, i64_ty: Ty<'zir>, bool_ty: Ty<'zir>) -> Body<'zir> {
    // Local declarations:
    // _0: return place (i64)
    // _1: arg a (i64)
    // _2: arg b (i64)
    // _3: comparison result (bool)
    let mut local_decls = IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

    let mut body = Body::new(local_decls, 2);

    // bb0: { _3 = Gt(_1, _2); switchInt(_3) -> [0: bb2, otherwise: bb1] }
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

    // bb1 (true branch): { _0 = _1; goto -> bb3 }
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

    // bb2 (false branch): { _0 = _2; goto -> bb3 }
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

    // bb3 (join): { return }
    let mut bb3 = BasicBlockData::new();
    bb3.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });
    body.basic_blocks.push(bb3);

    body
}

/// Build MIR for: fn count_to_n(n: i64) -> i64 { let mut i = 0; while i < n { i += 1; } i }
fn build_loop_function<'zir>(_arena: &'zir Arena, i64_ty: Ty<'zir>, bool_ty: Ty<'zir>) -> Body<'zir> {
    // Local declarations:
    // _0: return place (i64)
    // _1: arg n (i64)
    // _2: counter i (i64)
    // _3: comparison result (bool)
    let mut local_decls = IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

    let mut body = Body::new(local_decls, 1);

    // bb0: { _2 = 0; goto -> bb1 }
    let mut bb0 = BasicBlockData::new();
    bb0.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(2)),
            Rvalue::Use(Operand::Const(
                ConstValue::Scalar(ScalarRepr::from_u64(0)),
                i64_ty,
            )),
        ),
    });
    bb0.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Goto { target: BasicBlock::new(1) },
    });
    body.basic_blocks.push(bb0);

    // bb1 (loop header): { _3 = Lt(_2, _1); switchInt(_3) -> [0: bb3, otherwise: bb2] }
    let mut bb1 = BasicBlockData::new();
    bb1.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(3)),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::from_local(Local::new(2))),
                Operand::Copy(Place::from_local(Local::new(1))),
            ),
        ),
    });
    bb1.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from_local(Local::new(3))),
            targets: SwitchTargets::if_else(0, BasicBlock::new(3), BasicBlock::new(2)),
        },
    });
    body.basic_blocks.push(bb1);

    // bb2 (loop body): { _2 = Add(_2, 1); goto -> bb1 }
    let mut bb2 = BasicBlockData::new();
    bb2.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(2)),
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::from_local(Local::new(2))),
                Operand::Const(ConstValue::Scalar(ScalarRepr::from_u64(1)), i64_ty),
            ),
        ),
    });
    bb2.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Goto { target: BasicBlock::new(1) },
    });
    body.basic_blocks.push(bb2);

    // bb3 (exit): { _0 = _2; return }
    let mut bb3 = BasicBlockData::new();
    bb3.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(0)),
            Rvalue::Use(Operand::Copy(Place::from_local(Local::new(2)))),
        ),
    });
    bb3.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });
    body.basic_blocks.push(bb3);

    body
}
