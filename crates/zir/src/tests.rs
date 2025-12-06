//! Tests for zir crate
//!
//! Tests are organized into modules by component.

use crate::arena::Arena;
use crate::idx::Idx;
use crate::intern::InternSet;
use crate::list::List;
use crate::mir::*;
use crate::ty::*;
use crate::IndexVec;

mod mir_construction {
    //! Tests for MIR construction and manipulation.

    use super::*;

    #[test]
    fn build_function_with_arithmetic() {
        // fn add(a: i64, b: i64) -> i64 { a + b }
        let arena = Arena::new();
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
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

        assert_eq!(body.basic_blocks.len(), 1);
        assert_eq!(body.local_decls.len(), 3);
        assert_eq!(body.arg_count, 2);

        // Verify successors
        let term = body.basic_blocks[START_BLOCK].terminator();
        assert!(term.kind.successors().is_empty());
    }

    #[test]
    fn build_function_with_branching() {
        // fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
        let arena = Arena::new();
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
        let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
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

        assert_eq!(body.basic_blocks.len(), 4);

        // Verify control flow graph
        let bb0_successors = body.basic_blocks[START_BLOCK].terminator().kind.successors();
        assert_eq!(bb0_successors.len(), 2);
        assert!(bb0_successors.contains(&BasicBlock::new(1)));
        assert!(bb0_successors.contains(&BasicBlock::new(2)));

        let bb1_successors = body.basic_blocks[BasicBlock::new(1)].terminator().kind.successors();
        assert_eq!(bb1_successors, vec![BasicBlock::new(3)]);
    }

    #[test]
    fn build_loop_with_counter() {
        // fn count_to_n(n: i64) -> i64 {
        //     let mut i = 0;
        //     while i < n { i = i + 1; }
        //     i
        // }
        let arena = Arena::new();
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
        let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

        let mut body = Body::new(local_decls, 1);

        // bb0: _2 = 0; goto bb1
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

        // bb1 (loop header): _3 = Lt(_2, _1); switchInt(_3) -> [0: bb3, otherwise: bb2]
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

        // bb2 (loop body): _2 = _2 + 1; goto bb1
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

        // bb3 (exit): _0 = copy _2; return
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

        assert_eq!(body.basic_blocks.len(), 4);

        // Verify the loop structure: bb1 -> bb2 -> bb1 (back edge)
        let bb2_successors = body.basic_blocks[BasicBlock::new(2)].terminator().kind.successors();
        assert_eq!(bb2_successors, vec![BasicBlock::new(1)]);
    }
}

mod type_system {
    //! Tests for the type system.

    use super::*;

    #[test]
    fn fixed_width_integers() {
        assert_eq!(IntWidth::Fixed(8).bytes(8), 1);
        assert_eq!(IntWidth::Fixed(16).bytes(8), 2);
        assert_eq!(IntWidth::Fixed(32).bytes(8), 4);
        assert_eq!(IntWidth::Fixed(64).bytes(8), 8);
        assert_eq!(IntWidth::Fixed(128).bytes(8), 16);
        assert_eq!(IntWidth::Fixed(256).bytes(8), 32);
    }

    #[test]
    fn pointer_sized_integers() {
        assert_eq!(IntWidth::Size.bytes(4), 4);
        assert_eq!(IntWidth::Size.bytes(8), 8);
    }

    #[test]
    fn type_interning_deduplication() {
        let arena = Arena::new();
        let types = InternSet::new();

        let ty1 = types.intern(TyKind::Int(IntWidth::I32), |k| arena.dropless.alloc(k));
        let ty2 = types.intern(TyKind::Int(IntWidth::I32), |k| arena.dropless.alloc(k));
        let ty3 = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        assert_eq!(ty1.as_ptr(), ty2.as_ptr());
        assert_ne!(ty1.as_ptr(), ty3.as_ptr());
    }

    #[test]
    fn tuple_and_unit_types() {
        let arena = Arena::new();
        let types = InternSet::new();

        let unit = types.intern(TyKind::Unit, |k| arena.dropless.alloc(k));
        let i32_ty = types.intern(TyKind::Int(IntWidth::I32), |k| arena.dropless.alloc(k));

        let tuple_list = List::from_arena(&arena, &[i32_ty, i32_ty]);
        let pair = types.intern(TyKind::Tuple(tuple_list), |k| arena.dropless.alloc(k));

        assert!(matches!(&*unit, TyKind::Unit));
        assert!(matches!(&*pair, TyKind::Tuple(elems) if elems.len() == 2));
    }
}

mod scalar_repr {
    //! Tests for scalar value representation.

    use super::*;

    #[test]
    fn small_scalars() {
        let s = ScalarRepr::from_u64(42);
        assert_eq!(s.to_u64(), Some(42));
        assert_eq!(s.to_u128(), Some(42));
    }

    #[test]
    fn large_scalars() {
        let big = ScalarRepr::from_u128(u128::MAX);
        assert_eq!(big.to_u128(), Some(u128::MAX));
        assert!(big.to_u64().is_none());
    }

    #[test]
    fn arbitrary_precision_scalars() {
        use num_bigint::BigUint;
        use num_traits::One;

        // Create a 256-bit value: 2^255
        let big_value: BigUint = BigUint::one() << 255usize;
        let scalar = ScalarRepr::from_biguint(big_value.clone(), 32); // 32 bytes = 256 bits

        assert!(scalar.to_u64().is_none());
        assert!(scalar.to_u128().is_none());
        assert_eq!(scalar.to_biguint(), big_value);
    }
}

mod control_flow {
    //! Tests for control flow constructs.

    use super::*;

    #[test]
    fn switch_targets_if_else() {
        let targets = SwitchTargets::if_else(0, BasicBlock::new(1), BasicBlock::new(2));

        assert_eq!(targets.otherwise(), BasicBlock::new(2));
        assert_eq!(targets.values.len(), 1);
        assert_eq!(targets.targets.len(), 2);

        let all = targets.all_targets();
        assert!(all.contains(&BasicBlock::new(1)));
        assert!(all.contains(&BasicBlock::new(2)));
    }

    #[test]
    fn switch_targets_multi_way() {
        let targets = SwitchTargets::new(
            [(1, BasicBlock::new(1)), (2, BasicBlock::new(2)), (3, BasicBlock::new(3))].into_iter(),
            BasicBlock::new(0),
        );

        assert_eq!(targets.otherwise(), BasicBlock::new(0));
        assert_eq!(targets.values.len(), 3);
        assert_eq!(targets.targets.len(), 4);

        let pairs: Vec<_> = targets.iter().collect();
        assert_eq!(pairs[0], (1, BasicBlock::new(1)));
        assert_eq!(pairs[1], (2, BasicBlock::new(2)));
        assert_eq!(pairs[2], (3, BasicBlock::new(3)));
    }

    #[test]
    fn location_navigation() {
        let loc = Location::START;
        assert_eq!(loc.block, START_BLOCK);
        assert_eq!(loc.statement_index, 0);

        let next = loc.successor_within_block();
        assert_eq!(next.statement_index, 1);
        assert_eq!(next.block, START_BLOCK);
    }
}

mod place_and_projection {
    //! Tests for places and projections.

    use super::*;

    #[test]
    fn simple_local_place() {
        let place = Place::from_local(Local::new(5));
        assert!(place.is_local());
        assert_eq!(place.as_local(), Some(Local::new(5)));
        assert!(place.projection.is_empty());
    }

    #[test]
    fn projected_place() {
        let arena = Arena::new();
        let proj = List::from_arena(&arena, &[PlaceElem::Deref]);
        let place = Place {
            local: Local::new(0),
            projection: proj,
        };

        assert!(!place.is_local());
        assert!(place.as_local().is_none());
        assert_eq!(place.projection.len(), 1);
    }
}

mod arena_allocation {
    //! Tests for arena allocation.

    use super::*;

    #[test]
    fn dropless_arena_slices() {
        let arena = Arena::new();
        let slice1: &[i32] = arena.dropless.alloc_slice(&[1, 2, 3]);
        let slice2: &[i32] = arena.dropless.alloc_slice(&[4, 5, 6, 7, 8]);

        assert_eq!(slice1, &[1, 2, 3]);
        assert_eq!(slice2, &[4, 5, 6, 7, 8]);
    }

    #[test]
    fn list_iteration() {
        let arena = Arena::new();
        let list = List::from_arena(&arena, &[10u32, 20, 30, 40]);

        let sum: u32 = list.iter().sum();
        assert_eq!(sum, 100);

        let doubled: Vec<u32> = list.iter().map(|x| x * 2).collect();
        assert_eq!(doubled, vec![20, 40, 60, 80]);
    }

    #[test]
    fn empty_list_singleton() {
        let empty1: &List<u32> = List::empty();
        let empty2: &List<u32> = List::empty();

        assert_eq!(empty1 as *const _, empty2 as *const _);
        assert!(empty1.is_empty());
    }
}

mod snapshot_tests {
    //! Snapshot tests for MIR pretty printing using insta.

    use super::*;

    fn create_add_function<'zir>(
        arena: &'zir Arena,
        types: &InternSet<'zir, TyKind<'zir>>,
    ) -> Body<'zir> {
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| arena.dropless.alloc(kind));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
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

    fn create_conditional_function<'zir>(
        arena: &'zir Arena,
        types: &InternSet<'zir, TyKind<'zir>>,
    ) -> Body<'zir> {
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| arena.dropless.alloc(kind));
        let bool_ty = types.intern(TyKind::Bool, |kind| arena.dropless.alloc(kind));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

        let mut body = Body::new(local_decls, 2);

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
