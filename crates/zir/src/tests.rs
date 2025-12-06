//! Tests for zir crate

use crate::arena::Arena;
use crate::idx::Idx;
use crate::list::List;
use crate::mir::*;
use crate::ty::*;

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
