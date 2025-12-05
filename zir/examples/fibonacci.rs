//! Example: Build a fibonacci function using ZIR.
//!
//! This demonstrates how to construct MIR programmatically
//! and serves as a test case for the ZIR library.
//!
//! The generated function computes: fib(n) = n if n < 2 else fib(n-1) + fib(n-2)
//! (Iterative implementation to avoid stack issues)

use zir::{
    Module, Body, BasicBlock, BasicBlockData, Local, LocalDecl,
    Statement, Terminator, TerminatorKind,
    Place, Operand, Rvalue, BinOp, Scalar, SourceInfo, FnSig,
    ConstValue,
};
use zir::module::Function;

fn main() {
    let mut module = Module::new();
    let i64_ty = module.i64_ty();

    // fn fib(n: i64) -> i64
    let sig = FnSig::new(vec![i64_ty], i64_ty);

    let mut body = Body::new();

    // Locals:
    // _0: i64 (return value)
    // _1: i64 (arg n)
    // _2: i64 (a = 0)
    // _3: i64 (b = 1)
    // _4: i64 (i = 0)
    // _5: i64 (temp for swap)
    // _6: bool (loop condition)
    body.local_decls.push(LocalDecl::mutable(i64_ty)); // _0
    body.local_decls.push(LocalDecl::immut(i64_ty));   // _1
    body.local_decls.push(LocalDecl::mutable(i64_ty)); // _2
    body.local_decls.push(LocalDecl::mutable(i64_ty)); // _3
    body.local_decls.push(LocalDecl::mutable(i64_ty)); // _4
    body.local_decls.push(LocalDecl::mutable(i64_ty)); // _5
    body.local_decls.push(LocalDecl::mutable(module.bool_ty())); // _6
    body.arg_count = 1;

    // bb0: entry - initialize
    //   _2 = 0
    //   _3 = 1
    //   _4 = 0
    //   goto -> bb1
    let mut bb0 = BasicBlockData::new();
    bb0.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(2)),
        Rvalue::Use(Operand::Const(ConstValue::Scalar(Scalar::from(0i64 as u64)), i64_ty)),
    ));
    bb0.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(3)),
        Rvalue::Use(Operand::Const(ConstValue::Scalar(Scalar::from(1u64)), i64_ty)),
    ));
    bb0.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(4)),
        Rvalue::Use(Operand::Const(ConstValue::Scalar(Scalar::from(0u64)), i64_ty)),
    ));
    bb0.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Goto { target: BasicBlock::new(1) },
    ));
    body.basic_blocks.push(bb0);

    // bb1: loop header
    //   _6 = _4 < _1
    //   switchInt(_6) -> [1: bb2, otherwise: bb3]
    let mut bb1 = BasicBlockData::new();
    bb1.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(6)),
        Rvalue::BinaryOp(
            BinOp::Lt,
            Operand::Copy(Place::local(Local::new(4))),
            Operand::Copy(Place::local(Local::new(1))),
        ),
    ));
    bb1.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::local(Local::new(6))),
            targets: zir::SwitchTargets::if_else(
                Scalar::from(1u8),
                BasicBlock::new(2),
                BasicBlock::new(3),
            ),
        },
    ));
    body.basic_blocks.push(bb1);

    // bb2: loop body
    //   _5 = _2 + _3
    //   _2 = _3
    //   _3 = _5
    //   _4 = _4 + 1
    //   goto -> bb1
    let mut bb2 = BasicBlockData::new();
    bb2.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(5)),
        Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(Local::new(2))),
            Operand::Copy(Place::local(Local::new(3))),
        ),
    ));
    bb2.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(2)),
        Rvalue::Use(Operand::Copy(Place::local(Local::new(3)))),
    ));
    bb2.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(3)),
        Rvalue::Use(Operand::Copy(Place::local(Local::new(5)))),
    ));
    bb2.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::local(Local::new(4)),
        Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(Local::new(4))),
            Operand::Const(ConstValue::Scalar(Scalar::from(1u64)), i64_ty),
        ),
    ));
    bb2.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Goto { target: BasicBlock::new(1) },
    ));
    body.basic_blocks.push(bb2);

    // bb3: exit
    //   _0 = _2
    //   return
    let mut bb3 = BasicBlockData::new();
    bb3.statements.push(Statement::assign(
        SourceInfo::DUMMY,
        Place::return_place(),
        Rvalue::Use(Operand::Copy(Place::local(Local::new(2)))),
    ));
    bb3.terminator = Some(Terminator::new(
        SourceInfo::DUMMY,
        TerminatorKind::Return,
    ));
    body.basic_blocks.push(bb3);

    // Add function to module
    let func = Function::with_body("fib".to_string(), sig, body);
    let func_id = module.add_function(func);

    // Print the generated MIR
    println!("Generated MIR for fibonacci function:");
    println!("======================================");
    let func = module.get_function(func_id);
    println!("{:?}", func.body.as_ref().unwrap());

    // Print JSON representation
    println!("\nJSON representation:");
    println!("====================");
    println!("{}", serde_json::to_string_pretty(&module).unwrap());

    println!("\nModule statistics:");
    println!("==================");
    println!("Types: {}", module.type_count());
    println!("Functions: {}", module.function_count());
    println!("Globals: {}", module.global_count());
}
