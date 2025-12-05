//! Integration tests for ZIR library.

use zir::{
    Module, Body, BasicBlock, BasicBlockData, Local, LocalDecl,
    Statement, Terminator, TerminatorKind,
    Place, Operand, Rvalue, BinOp, Scalar, SourceInfo, FnSig,
};
use zir::module::Function;

/// Build a simple function that adds two numbers:
/// fn add(a: i32, b: i32) -> i32 {
///     let result = a + b;
///     return result;
/// }
#[test]
fn test_build_add_function() {
    let mut module = Module::new();

    // Get i32 type
    let i32_ty = module.i32_ty();

    // Create function signature
    let sig = FnSig::new(vec![i32_ty, i32_ty], i32_ty);

    // Create function body
    let mut body = Body::new();

    // Local declarations:
    // _0: i32 (return place)
    // _1: i32 (arg a)
    // _2: i32 (arg b)
    body.local_decls.push(LocalDecl::immut(i32_ty)); // _0 return
    body.local_decls.push(LocalDecl::immut(i32_ty)); // _1 arg a
    body.local_decls.push(LocalDecl::immut(i32_ty)); // _2 arg b
    body.arg_count = 2;

    // Entry block bb0:
    //   _0 = _1 + _2
    //   return
    let mut bb0 = BasicBlockData::new();

    // _0 = _1 + _2
    bb0.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::return_place(),
        Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(Local::new(1))),
            Operand::Copy(Place::local(Local::new(2))),
        ),
    ));

    // return
    bb0.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Return,
    ));

    body.basic_blocks.push(bb0);

    // Add function to module
    let func = Function::with_body("add".to_string(), sig, body);
    let func_id = module.add_function(func);

    // Verify
    let func = module.get_function(func_id);
    assert_eq!(func.name, "add");
    assert_eq!(func.sig.inputs.len(), 2);

    let body = func.body.as_ref().unwrap();
    assert_eq!(body.arg_count, 2);
    assert_eq!(body.basic_blocks.len(), 1);

    // Print the body for visual inspection
    println!("{:?}", body);
}

/// Build a function with conditional branching:
/// fn max(a: i32, b: i32) -> i32 {
///     if a > b { a } else { b }
/// }
#[test]
fn test_build_conditional_function() {
    let mut module = Module::new();
    let i32_ty = module.i32_ty();
    let bool_ty = module.bool_ty();

    let sig = FnSig::new(vec![i32_ty, i32_ty], i32_ty);

    let mut body = Body::new();

    // Locals:
    // _0: i32 (return)
    // _1: i32 (a)
    // _2: i32 (b)
    // _3: bool (comparison result)
    body.local_decls.push(LocalDecl::immut(i32_ty));  // _0
    body.local_decls.push(LocalDecl::immut(i32_ty));  // _1
    body.local_decls.push(LocalDecl::immut(i32_ty));  // _2
    body.local_decls.push(LocalDecl::immut(bool_ty)); // _3
    body.arg_count = 2;

    // bb0: entry
    //   _3 = _1 > _2
    //   switchInt(_3) -> [1: bb1, otherwise: bb2]
    let mut bb0 = BasicBlockData::new();
    bb0.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(3)),
        Rvalue::BinaryOp(
            BinOp::Gt,
            Operand::Copy(Place::local(Local::new(1))),
            Operand::Copy(Place::local(Local::new(2))),
        ),
    ));
    bb0.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::local(Local::new(3))),
            targets: zir::SwitchTargets::if_else(
                Scalar::from(1u8),
                BasicBlock::new(1),
                BasicBlock::new(2),
            ),
        },
    ));
    body.basic_blocks.push(bb0);

    // bb1: then branch
    //   _0 = _1
    //   goto -> bb3
    let mut bb1 = BasicBlockData::new();
    bb1.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::return_place(),
        Rvalue::Use(Operand::Copy(Place::local(Local::new(1)))),
    ));
    bb1.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Goto { target: BasicBlock::new(3) },
    ));
    body.basic_blocks.push(bb1);

    // bb2: else branch
    //   _0 = _2
    //   goto -> bb3
    let mut bb2 = BasicBlockData::new();
    bb2.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::return_place(),
        Rvalue::Use(Operand::Copy(Place::local(Local::new(2)))),
    ));
    bb2.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Goto { target: BasicBlock::new(3) },
    ));
    body.basic_blocks.push(bb2);

    // bb3: exit
    //   return
    let mut bb3 = BasicBlockData::new();
    bb3.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Return,
    ));
    body.basic_blocks.push(bb3);

    // Add function to module
    let func = Function::with_body("max".to_string(), sig, body);
    let func_id = module.add_function(func);

    // Verify
    let func = module.get_function(func_id);
    let body = func.body.as_ref().unwrap();
    assert_eq!(body.basic_blocks.len(), 4);

    // Check switchInt terminator
    let term = body.basic_blocks[BasicBlock::START].terminator();
    match &term.kind {
        TerminatorKind::SwitchInt { targets, .. } => {
            assert_eq!(targets.otherwise(), BasicBlock::new(2));
        }
        _ => panic!("Expected SwitchInt terminator"),
    }

    println!("{:?}", body);
}

/// Test arbitrary bit-width types (u256, i512).
#[test]
fn test_arbitrary_bit_width_types() {
    let mut module = Module::new();

    // Create u256 type
    let u256 = module.uint_ty(256);
    assert_eq!(format!("{:?}", module.get_type(u256)), "u256");

    // Create i512 type
    let i512 = module.int_ty(512);
    assert_eq!(format!("{:?}", module.get_type(i512)), "i512");

    // Verify type interning works
    let u256_again = module.uint_ty(256);
    assert_eq!(u256, u256_again);

    // Create a scalar constant for u256
    use num_bigint::BigUint;
    let big_value: BigUint = BigUint::from(1u128) << 200usize;
    let scalar = Scalar::from_biguint(big_value.clone(), 256);
    assert_eq!(scalar.bits(), 256);
    assert_eq!(scalar.to_biguint(), big_value);
}

/// Test module serialization (basic check).
#[test]
fn test_module_serialization() {
    let mut module = Module::new();
    let i32_ty = module.i32_ty();

    // Create a simple function
    let sig = FnSig::new(vec![i32_ty], i32_ty);
    let func = Function::new("identity".to_string(), sig);
    module.add_function(func);

    // Serialize to JSON
    let json = serde_json::to_string_pretty(&module).unwrap();

    // Verify it contains expected content
    assert!(json.contains("identity"));

    // Deserialize back
    let restored: Module = serde_json::from_str(&json).unwrap();
    assert_eq!(restored.function_count(), 1);

    let func = restored.find_function("identity").unwrap();
    assert_eq!(restored.get_function(func).name, "identity");
}
