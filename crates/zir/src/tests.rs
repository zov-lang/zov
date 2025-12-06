//! Tests for zir crate

use crate::arena::Arena;
use crate::idx::Idx;
use crate::intern::InternSet;
use crate::list::List;
use crate::mir::*;
use crate::ty::*;
use crate::IndexVec;

#[test]
fn test_arena_allocation() {
    let arena = Arena::new();
    let types: &[i32] = arena.dropless.alloc_slice(&[1, 2, 3, 4, 5]);
    assert_eq!(types, &[1, 2, 3, 4, 5]);
}

#[test]
fn test_list_creation() {
    let arena = Arena::new();
    let list = List::from_arena(&arena, &[1u32, 2, 3]);
    assert_eq!(list.len(), 3);
    assert_eq!(list[0], 1);
    assert_eq!(list[1], 2);
    assert_eq!(list[2], 3);
}

#[test]
fn test_empty_list() {
    let empty: &List<u32> = List::empty();
    assert!(empty.is_empty());
    assert_eq!(empty.len(), 0);
}

#[test]
fn test_int_width() {
    let u8_width = IntWidth::Fixed(8);
    let u256_width = IntWidth::Fixed(256);

    assert_eq!(u8_width.bytes(8), 1);
    assert_eq!(u256_width.bytes(8), 32);

    assert_eq!(IntWidth::Size.bytes(8), 8);
    assert_eq!(IntWidth::Size.bytes(4), 4);
}

#[test]
fn test_basic_block_creation() {
    let mut blocks = BasicBlocks::new();
    let bb0 = blocks.push(BasicBlockData::new());
    let bb1 = blocks.push(BasicBlockData::new());

    assert_eq!(bb0.index(), 0);
    assert_eq!(bb1.index(), 1);
    assert_eq!(blocks.len(), 2);
}

#[test]
fn test_switch_targets() {
    let targets = SwitchTargets::if_else(0, BasicBlock::new(1), BasicBlock::new(2));
    assert_eq!(targets.otherwise(), BasicBlock::new(2));

    let all = targets.all_targets();
    assert_eq!(all.len(), 2);
    assert!(all.contains(&BasicBlock::new(1)));
    assert!(all.contains(&BasicBlock::new(2)));
}

#[test]
fn test_place_from_local() {
    let place = Place::from_local(Local::new(0));
    assert!(place.is_local());
    assert_eq!(place.as_local(), Some(Local::new(0)));
}

#[test]
fn test_location() {
    let loc = Location::START;
    assert_eq!(loc.block, START_BLOCK);
    assert_eq!(loc.statement_index, 0);

    let next = loc.successor_within_block();
    assert_eq!(next.block, START_BLOCK);
    assert_eq!(next.statement_index, 1);
}

#[test]
fn test_binop_is_comparison() {
    assert!(BinOp::Eq.is_comparison());
    assert!(BinOp::Lt.is_comparison());
    assert!(BinOp::Le.is_comparison());
    assert!(BinOp::Ne.is_comparison());
    assert!(BinOp::Ge.is_comparison());
    assert!(BinOp::Gt.is_comparison());

    assert!(!BinOp::Add.is_comparison());
    assert!(!BinOp::Mul.is_comparison());
}

// Snapshot tests for MIR pretty printing
mod snapshot_tests {
    use super::*;

    /// Helper to create a simple add function: fn add(a: i64, b: i64) -> i64 { a + b }
    fn create_add_function<'zir>(
        arena: &'zir Arena,
        types: &InternSet<'zir, TyKind<'zir>>,
    ) -> Body<'zir> {
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| arena.dropless.alloc(kind));

        // Local declarations: _0: return, _1: arg a, _2: arg b
        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl {
            mutability: Mutability::Mut,
            ty: i64_ty,
        });
        local_decls.push(LocalDecl {
            mutability: Mutability::Not,
            ty: i64_ty,
        });
        local_decls.push(LocalDecl {
            mutability: Mutability::Not,
            ty: i64_ty,
        });

        let mut body = Body::new(local_decls, 2);

        // bb0: _0 = Add(_1, _2); return
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

    /// Helper to create a conditional function with if-else
    fn create_conditional_function<'zir>(
        arena: &'zir Arena,
        types: &InternSet<'zir, TyKind<'zir>>,
    ) -> Body<'zir> {
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| arena.dropless.alloc(kind));
        let bool_ty = types.intern(TyKind::Bool, |kind| arena.dropless.alloc(kind));

        // fn max(a: i64, b: i64) -> i64
        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl {
            mutability: Mutability::Mut,
            ty: i64_ty,
        }); // _0: return
        local_decls.push(LocalDecl {
            mutability: Mutability::Not,
            ty: i64_ty,
        }); // _1: arg a
        local_decls.push(LocalDecl {
            mutability: Mutability::Not,
            ty: i64_ty,
        }); // _2: arg b
        local_decls.push(LocalDecl {
            mutability: Mutability::Mut,
            ty: bool_ty,
        }); // _3: comparison result

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

        // bb1: _0 = copy _1; goto -> bb3
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
            kind: TerminatorKind::Goto {
                target: BasicBlock::new(3),
            },
        });
        body.basic_blocks.push(bb1);

        // bb2: _0 = copy _2; goto -> bb3
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
            kind: TerminatorKind::Goto {
                target: BasicBlock::new(3),
            },
        });
        body.basic_blocks.push(bb2);

        // bb3: return
        let mut bb3 = BasicBlockData::new();
        bb3.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb3);

        body
    }

    #[test]
    fn snapshot_simple_add_function() {
        let arena = Arena::new();
        let types = InternSet::new();
        let body = create_add_function(&arena, &types);
        insta::assert_snapshot!(body.pretty_with_name("add").to_string());
    }

    #[test]
    fn snapshot_conditional_max_function() {
        let arena = Arena::new();
        let types = InternSet::new();
        let body = create_conditional_function(&arena, &types);
        insta::assert_snapshot!(body.pretty_with_name("max").to_string());
    }

    #[test]
    fn snapshot_empty_body() {
        let local_decls = IndexVec::new();
        let body = Body::new(local_decls, 0);
        insta::assert_snapshot!(body.pretty_with_name("empty").to_string());
    }
}
