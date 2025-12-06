//! Example: JIT compilation and execution of MIR functions
//!
//! This example demonstrates how to:
//! - Create MIR function bodies using the ZIR type system
//! - Compile them to native code using the Cranelift JIT backend
//! - Execute the compiled functions and retrieve results
//!
//! This shows a complete "real program building" workflow from MIR to execution.

use cranelift::prelude::*;
use cranelift_module::Module;
use zir::Arena;
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir_codegen_cranelift::{CodegenContext, create_jit_module};

fn main() {
    println!("ZIR Cranelift JIT Execution Example");
    println!("====================================\n");

    // Example 1: Simple constant function
    example_const_function();

    // Example 2: Add function with arguments
    example_add_function();

    // Example 3: Max function with control flow
    example_max_function();

    // Example 4: Loop (count to N)
    example_loop_function();

    println!("\nAll examples completed successfully!");
}

/// Example: JIT compile and execute a function returning a constant value.
fn example_const_function() {
    println!("Example 1: Constant Function");
    println!("----------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

    // Create MIR: fn const_42() -> i64 { 42 }
    let body = create_const_mir(&arena, i64_ty, 42);

    // Create JIT module and codegen context
    let module = create_jit_module();
    let mut ctx = CodegenContext::new(module);

    // Create function signature: () -> i64
    let mut sig = ctx.module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));

    // Declare and define the function
    let func_id =
        ctx.declare_function("const_42", sig.clone()).expect("failed to declare function");
    ctx.define_function(func_id, &body, sig).expect("failed to define function");

    // Finalize the module and get the function pointer
    ctx.module.finalize_definitions().expect("failed to finalize");
    let code_ptr = ctx.module.get_finalized_function(func_id);

    // Cast to a callable function pointer and execute
    let func: fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let result = func();

    println!("  const_42() = {}", result);
    assert_eq!(result, 42);
    println!("  OK\n");
}

/// Example: JIT compile and execute an add function.
fn example_add_function() {
    println!("Example 2: Add Function");
    println!("-----------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

    // Create MIR: fn add(a: i64, b: i64) -> i64 { a + b }
    let body = create_add_mir(&arena, i64_ty);

    // Create JIT module and codegen context
    let module = create_jit_module();
    let mut ctx = CodegenContext::new(module);

    // Create function signature: (i64, i64) -> i64
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));

    // Declare and define the function
    let func_id = ctx.declare_function("add", sig.clone()).expect("failed to declare function");
    ctx.define_function(func_id, &body, sig).expect("failed to define function");

    // Finalize and get the function pointer
    ctx.module.finalize_definitions().expect("failed to finalize");
    let code_ptr = ctx.module.get_finalized_function(func_id);

    // Execute with different inputs
    let func: fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };

    let test_cases = [(10, 20, 30), (100, 200, 300), (-5, 10, 5), (0, 0, 0)];

    for (a, b, expected) in test_cases {
        let result = func(a, b);
        println!("  add({}, {}) = {}", a, b, result);
        assert_eq!(result, expected);
    }
    println!("  OK\n");
}

/// Example: JIT compile and execute a max function with control flow.
fn example_max_function() {
    println!("Example 3: Max Function (with branching)");
    println!("-----------------------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
    let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

    // Create MIR: fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
    let body = create_max_mir(&arena, i64_ty, bool_ty);

    // Create JIT module and codegen context
    let module = create_jit_module();
    let mut ctx = CodegenContext::new(module);

    // Create function signature: (i64, i64) -> i64
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));

    // Declare and define the function
    let func_id = ctx.declare_function("max", sig.clone()).expect("failed to declare function");
    ctx.define_function(func_id, &body, sig).expect("failed to define function");

    // Finalize and get the function pointer
    ctx.module.finalize_definitions().expect("failed to finalize");
    let code_ptr = ctx.module.get_finalized_function(func_id);

    // Execute with different inputs
    let func: fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };

    let test_cases = [(10, 20, 20), (30, 15, 30), (-5, -10, -5), (42, 42, 42)];

    for (a, b, expected) in test_cases {
        let result = func(a, b);
        println!("  max({}, {}) = {}", a, b, result);
        assert_eq!(result, expected);
    }
    println!("  OK\n");
}

/// Example: JIT compile and execute a loop function.
fn example_loop_function() {
    println!("Example 4: Loop Function (count to N)");
    println!("-------------------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
    let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

    // Create MIR: fn count_to_n(n: i64) -> i64 { let mut i = 0; while i < n { i += 1; } i }
    let body = create_loop_mir(&arena, i64_ty, bool_ty);

    // Create JIT module and codegen context
    let module = create_jit_module();
    let mut ctx = CodegenContext::new(module);

    // Create function signature: (i64) -> i64
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));

    // Declare and define the function
    let func_id =
        ctx.declare_function("count_to_n", sig.clone()).expect("failed to declare function");
    ctx.define_function(func_id, &body, sig).expect("failed to define function");

    // Finalize and get the function pointer
    ctx.module.finalize_definitions().expect("failed to finalize");
    let code_ptr = ctx.module.get_finalized_function(func_id);

    // Execute with different inputs
    let func: fn(i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };

    let test_cases = [(0, 0), (5, 5), (10, 10), (100, 100)];

    for (n, expected) in test_cases {
        let result = func(n);
        println!("  count_to_n({}) = {}", n, result);
        assert_eq!(result, expected);
    }
    println!("  OK\n");
}

// ============================================================================
// MIR Building Helpers
// ============================================================================

/// Create MIR for: fn const_value() -> i64 { <value> }
fn create_const_mir<'a>(_arena: &'a Arena, i64_ty: Ty<'a>, value: i64) -> Body<'a> {
    let mut local_decls = zir::IndexVec::new();
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

/// Create MIR for: fn add(a: i64, b: i64) -> i64 { a + b }
fn create_add_mir<'a>(_arena: &'a Arena, i64_ty: Ty<'a>) -> Body<'a> {
    let mut local_decls = zir::IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _0: return
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty }); // _1: arg a
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty }); // _2: arg b

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

/// Create MIR for: fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
fn create_max_mir<'a>(_arena: &'a Arena, i64_ty: Ty<'a>, bool_ty: Ty<'a>) -> Body<'a> {
    let mut local_decls = zir::IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _0: return
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty }); // _1: arg a
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty }); // _2: arg b
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty }); // _3: cmp result

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

    // bb1 (true): _0 = _1; goto -> bb3
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

    // bb2 (false): _0 = _2; goto -> bb3
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

    // bb3 (join): return
    let mut bb3 = BasicBlockData::new();
    bb3.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });
    body.basic_blocks.push(bb3);

    body
}

/// Create MIR for: fn count_to_n(n: i64) -> i64 { let mut i = 0; while i < n { i += 1; } i }
fn create_loop_mir<'a>(_arena: &'a Arena, i64_ty: Ty<'a>, bool_ty: Ty<'a>) -> Body<'a> {
    let mut local_decls = zir::IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _0: return
    local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty }); // _1: arg n
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _2: counter i
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty }); // _3: cmp result

    let mut body = Body::new(local_decls, 1);

    // bb0: _2 = 0; goto -> bb1
    let mut bb0 = BasicBlockData::new();
    bb0.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(2)),
            Rvalue::Use(Operand::Const(ConstValue::Scalar(ScalarRepr::from_u64(0)), i64_ty)),
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

    // bb2 (loop body): _2 = Add(_2, 1); goto -> bb1
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

    // bb3 (exit): _0 = _2; return
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
