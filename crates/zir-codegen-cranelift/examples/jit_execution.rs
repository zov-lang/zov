//! Example: JIT compilation and execution of ZIR MIR
//!
//! This example demonstrates how to:
//! 1. Create MIR for a function
//! 2. Compile it to native code using Cranelift
//! 3. Execute the compiled code via JIT
//!
//! This is a "real program building" example that shows end-to-end
//! code generation and execution.

use cranelift_module::Module;
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir::{Arena, IndexVec};
use zir_codegen_cranelift::{CodegenContext, create_jit_module};

fn main() {
    println!("ZIR JIT Execution Example");
    println!("==========================\n");

    // Example 1: Simple constant function
    example_const_function();

    // Example 2: Addition function
    example_add_function();

    // Example 3: Max function with branching
    example_max_function();

    // Example 4: Factorial (recursive-like loop)
    example_factorial();

    println!("\nAll examples completed successfully!");
}

/// Demonstrates compiling and executing a function that returns a constant.
fn example_const_function() {
    println!("Example 1: Constant function");
    println!("----------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

    // Build: fn const42() -> i64 { 42 }
    let body = build_const_function(&arena, i64_ty, 42);

    // Compile and execute
    let result = compile_and_run_i64(&body, &[]);
    println!("  const42() = {}", result);
    assert_eq!(result, 42);

    println!("  ✓ Passed\n");
}

/// Demonstrates compiling and executing an addition function.
fn example_add_function() {
    println!("Example 2: Addition function");
    println!("----------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

    // Build: fn add(a: i64, b: i64) -> i64 { a + b }
    let body = build_add_function(&arena, i64_ty);

    // Test with various inputs
    let test_cases = [(1, 2, 3), (10, 20, 30), (-5, 5, 0), (100, -50, 50)];

    for (a, b, expected) in test_cases {
        let result = compile_and_run_i64(&body, &[a, b]);
        println!("  add({}, {}) = {}", a, b, result);
        assert_eq!(result, expected);
    }

    println!("  ✓ Passed\n");
}

/// Demonstrates compiling and executing a max function with control flow.
fn example_max_function() {
    println!("Example 3: Max function (with branching)");
    println!("-----------------------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
    let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

    // Build: fn max(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
    let body = build_max_function(&arena, i64_ty, bool_ty);

    // Test with various inputs
    let test_cases = [(5, 3, 5), (3, 5, 5), (10, 10, 10), (-5, -3, -3), (-3, -5, -3)];

    for (a, b, expected) in test_cases {
        let result = compile_and_run_i64(&body, &[a, b]);
        println!("  max({}, {}) = {}", a, b, result);
        assert_eq!(result, expected);
    }

    println!("  ✓ Passed\n");
}

/// Demonstrates compiling and executing a factorial-like function.
fn example_factorial() {
    println!("Example 4: Factorial function (loop)");
    println!("------------------------------------");

    let arena = Arena::new();
    let types = InternSet::new();
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
    let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

    // Build: fn factorial(n: i64) -> i64 { let mut result = 1; while n > 1 { result *= n; n -= 1; } result }
    let body = build_factorial_function(&arena, i64_ty, bool_ty);

    // Test with various inputs
    let test_cases = [(0, 1), (1, 1), (2, 2), (3, 6), (4, 24), (5, 120), (6, 720)];

    for (n, expected) in test_cases {
        let result = compile_and_run_i64(&body, &[n]);
        println!("  factorial({}) = {}", n, result);
        assert_eq!(result, expected);
    }

    println!("  ✓ Passed\n");
}

// ============================================================================
// MIR Building Helpers
// ============================================================================

fn build_const_function<'a>(_arena: &'a Arena<'a>, i64_ty: Ty<'a>, value: i64) -> Body<'a> {
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

fn build_add_function<'a>(arena: &'a Arena<'a>, i64_ty: Ty<'a>) -> Body<'a> {
    let _ = arena;
    let mut local_decls = IndexVec::new();
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

fn build_max_function<'a>(arena: &'a Arena<'a>, i64_ty: Ty<'a>, bool_ty: Ty<'a>) -> Body<'a> {
    let _ = arena;
    let mut local_decls = IndexVec::new();
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

    // bb1: _0 = _1; goto bb3
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

    // bb2: _0 = _2; goto bb3
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

    // bb3: return
    let mut bb3 = BasicBlockData::new();
    bb3.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });
    body.basic_blocks.push(bb3);

    body
}

fn build_factorial_function<'a>(arena: &'a Arena<'a>, i64_ty: Ty<'a>, bool_ty: Ty<'a>) -> Body<'a> {
    let _ = arena;
    let mut local_decls = IndexVec::new();
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _0: return (result)
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty }); // _1: arg n (mutable for loop)
    local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty }); // _2: cmp result

    let mut body = Body::new(local_decls, 1);

    // bb0: _0 = 1; goto bb1
    let mut bb0 = BasicBlockData::new();
    bb0.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(0)),
            Rvalue::Use(Operand::Const(ConstValue::Scalar(ScalarRepr::from_u64(1)), i64_ty)),
        ),
    });
    bb0.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Goto { target: BasicBlock::new(1) },
    });
    body.basic_blocks.push(bb0);

    // bb1 (loop header): _2 = Gt(_1, 1); switchInt(_2) -> [0: bb3, otherwise: bb2]
    let mut bb1 = BasicBlockData::new();
    bb1.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(2)),
            Rvalue::BinaryOp(
                BinOp::Gt,
                Operand::Copy(Place::from_local(Local::new(1))),
                Operand::Const(ConstValue::Scalar(ScalarRepr::from_u64(1)), i64_ty),
            ),
        ),
    });
    bb1.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from_local(Local::new(2))),
            targets: SwitchTargets::if_else(0, BasicBlock::new(3), BasicBlock::new(2)),
        },
    });
    body.basic_blocks.push(bb1);

    // bb2 (loop body): _0 = Mul(_0, _1); _1 = Sub(_1, 1); goto bb1
    let mut bb2 = BasicBlockData::new();
    bb2.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(0)),
            Rvalue::BinaryOp(
                BinOp::Mul,
                Operand::Copy(Place::from_local(Local::new(0))),
                Operand::Copy(Place::from_local(Local::new(1))),
            ),
        ),
    });
    bb2.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            Place::from_local(Local::new(1)),
            Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::from_local(Local::new(1))),
                Operand::Const(ConstValue::Scalar(ScalarRepr::from_u64(1)), i64_ty),
            ),
        ),
    });
    bb2.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Goto { target: BasicBlock::new(1) },
    });
    body.basic_blocks.push(bb2);

    // bb3 (exit): return
    let mut bb3 = BasicBlockData::new();
    bb3.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });
    body.basic_blocks.push(bb3);

    body
}

// ============================================================================
// JIT Compilation and Execution
// ============================================================================

/// Compiles MIR to native code and executes it with the given i64 arguments.
fn compile_and_run_i64(body: &Body<'_>, args: &[i64]) -> i64 {
    use cranelift::prelude::*;

    // Create a new JIT module
    let mut module = create_jit_module();

    // Build signature
    let mut sig = module.make_signature();
    for _ in 0..body.arg_count {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    // Declare and define the function
    let func_id = module
        .declare_function("_jit_func", cranelift_module::Linkage::Export, &sig)
        .expect("Failed to declare function");

    let mut ctx = CodegenContext::new(module);
    ctx.define_function(func_id, body, sig).expect("Failed to define function");

    // Finalize the module
    ctx.module.finalize_definitions().expect("Failed to finalize definitions");

    // Get the function pointer
    let func_ptr = ctx.module.get_finalized_function(func_id);

    // Call the function based on argument count
    unsafe {
        match args.len() {
            0 => {
                let func: extern "C" fn() -> i64 = std::mem::transmute(func_ptr);
                func()
            }
            1 => {
                let func: extern "C" fn(i64) -> i64 = std::mem::transmute(func_ptr);
                func(args[0])
            }
            2 => {
                let func: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(func_ptr);
                func(args[0], args[1])
            }
            _ => panic!("Unsupported argument count: {}", args.len()),
        }
    }
}
