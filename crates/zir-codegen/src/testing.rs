//! Backend-agnostic testing utilities for code generation.
//!
//! This module provides utilities for testing [`CodegenBackend`] implementations
//! in a backend-independent way. Tests written using these utilities can be
//! run against any backend without modification.
//!
//! # Codegen-Agnostic Tests
//!
//! The testing framework allows defining tests once and running them against
//! any backend. Each backend can register itself with:
//! - A factory function to create backend instances
//! - A normalization function for cross-platform snapshot testing
//!
//! ## Example
//!
//! ```rust,ignore
//! // In backend-specific tests (e.g., cranelift_tests.rs):
//! use zir_codegen::testing::{BackendTestRunner, create_add_function, sig_i64_i64_to_i64};
//!
//! fn normalize_clif(ir: &str) -> String {
//!     // Replace platform-specific calling conventions
//!     ir.replace("system_v", "<call_conv>")
//! }
//!
//! fn create_cranelift() -> Box<dyn CodegenBackend> {
//!     Box::new(CraneliftBackend::new(CodegenConfig::default()))
//! }
//!
//! // Run all standard tests against this backend
//! BackendTestRunner::new("cranelift", create_cranelift, normalize_clif)
//!     .run_all_tests();
//! ```

use crate::{CodegenBackend, CodegenConfig, FunctionSignature, TypeDesc};
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;
use zir::{Arena, IndexVec};

/// Creates a simple function that returns a constant i64 value.
///
/// # MIR Structure
/// ```text
/// fn const_fn() -> i64 {
///     let _0: i64;
///     bb0: {
///         _0 = <value>;
///         return;
///     }
/// }
/// ```
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
///
/// # MIR Structure
/// ```text
/// fn add(_1: i64, _2: i64) -> i64 {
///     let _0: i64;
///     bb0: {
///         _0 = Add(_1, _2);
///         return;
///     }
/// }
/// ```
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
///
/// # MIR Structure
/// ```text
/// fn max(_1: i64, _2: i64) -> i64 {
///     let _0: i64;
///     let _3: bool;
///     bb0: {
///         _3 = Gt(_1, _2);
///         switchInt(_3) -> [0: bb2, otherwise: bb1];
///     }
///     bb1: {
///         _0 = _1;
///         goto -> bb3;
///     }
///     bb2: {
///         _0 = _2;
///         goto -> bb3;
///     }
///     bb3: {
///         return;
///     }
/// }
/// ```
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

/// Signature for a function returning i64.
pub fn sig_void_to_i64() -> FunctionSignature {
    FunctionSignature::new().with_return(TypeDesc::Int(64))
}

/// Signature for a function taking two i64 and returning i64.
pub fn sig_i64_i64_to_i64() -> FunctionSignature {
    FunctionSignature::new()
        .with_param(TypeDesc::Int(64))
        .with_param(TypeDesc::Int(64))
        .with_return(TypeDesc::Int(64))
}

/// Compiles a MIR body to IR using any backend implementing [`CodegenBackend`].
///
/// This function is backend-agnostic - it works with any backend that implements
/// the [`CodegenBackend`] trait.
pub fn compile_to_ir_text(
    backend: &mut dyn CodegenBackend,
    body: &Body<'_>,
    sig: FunctionSignature,
) -> String {
    backend.compile_to_ir(body, sig)
}

/// A test case for backend-agnostic codegen testing.
///
/// This struct encapsulates a test case that can be run against any
/// [`CodegenBackend`] implementation.
pub struct CodegenTestCase<'a> {
    /// Name of the test case.
    pub name: &'static str,
    /// The MIR body to compile.
    pub body: Body<'a>,
    /// The function signature.
    pub signature: FunctionSignature,
}

impl<'a> CodegenTestCase<'a> {
    /// Creates a new test case.
    pub fn new(name: &'static str, body: Body<'a>, signature: FunctionSignature) -> Self {
        Self { name, body, signature }
    }

    /// Runs this test case against a backend.
    ///
    /// Returns the generated IR text.
    pub fn run(&self, backend: &mut dyn CodegenBackend) -> String {
        compile_to_ir_text(backend, &self.body, self.signature.clone())
    }
}

/// Creates the standard set of test cases for codegen verification.
///
/// This returns a vector of test case builders that can be used with any
/// backend implementing [`CodegenBackend`].
///
/// The test cases cover:
/// - Constant value generation
/// - Negative constant handling
/// - Binary operations (add)
/// - Control flow (branching)
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

/// Runs all standard test cases against a backend factory.
///
/// This function creates a backend using the provided factory and runs
/// all standard test cases, returning a map of test names to their IR output.
pub fn run_standard_tests<F>(factory: F) -> Vec<(&'static str, String)>
where
    F: Fn(CodegenConfig) -> Box<dyn CodegenBackend>,
{
    let arena = Arena::new();
    let test_cases = standard_test_cases(&arena);
    let mut results = Vec::new();

    for test in &test_cases {
        let mut backend = factory(CodegenConfig::default());
        let ir = test.run(backend.as_mut());
        results.push((test.name, ir));
    }

    results
}

// ============================================================================
// Backend-Agnostic Test Infrastructure
// ============================================================================

/// Macro for defining a single codegen test that works with any backend.
///
/// This macro provides a concise way to define tests that:
/// 1. Create MIR bodies using the standard test utilities
/// 2. Compile them using any backend
/// 3. Optionally normalize the output for cross-platform snapshots
///
/// # Syntax Variants
///
/// ```rust,ignore
/// // Basic: test with no-arg MIR builder
/// codegen_test!(test_name, backend, mir_builder, (param_types) -> ret_type);
///
/// // With value: test with value-arg MIR builder
/// codegen_test!(test_name, backend, mir_builder, value, () -> ret_type);
///
/// // With normalizer: apply normalization before snapshot
/// codegen_test!(test_name, backend, mir_builder, (param_types) -> ret_type, normalizer);
/// ```
#[macro_export]
macro_rules! codegen_test {
    // Variant: MIR builder with no args, with normalizer
    ($name:ident, $backend:expr, $mir_fn:expr, ($($p:ty),*) -> $ret:ty, $normalize:expr) => {
        #[test]
        fn $name() {
            use zir::Arena;
            use $crate::{CodegenBackend, FunctionSignature, TypeDesc};

            let arena = Arena::new();
            let body = $mir_fn(&arena);
            let sig = FunctionSignature::new()
                $(.with_param(TypeDesc::Int((std::mem::size_of::<$p>() * 8) as u32)))*
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = $backend;
            let ir = backend.compile_to_ir(&body, sig);
            let normalized = $normalize(&ir);
            insta::assert_snapshot!(normalized);
        }
    };

    // Variant: MIR builder with no args, no normalizer
    ($name:ident, $backend:expr, $mir_fn:expr, ($($p:ty),*) -> $ret:ty) => {
        #[test]
        fn $name() {
            use zir::Arena;
            use $crate::{CodegenBackend, FunctionSignature, TypeDesc};

            let arena = Arena::new();
            let body = $mir_fn(&arena);
            let sig = FunctionSignature::new()
                $(.with_param(TypeDesc::Int((std::mem::size_of::<$p>() * 8) as u32)))*
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = $backend;
            let ir = backend.compile_to_ir(&body, sig);
            insta::assert_snapshot!(ir);
        }
    };

    // Variant: MIR builder with value arg, with normalizer
    ($name:ident, $backend:expr, $mir_fn:expr, $value:expr, () -> $ret:ty, $normalize:expr) => {
        #[test]
        fn $name() {
            use zir::Arena;
            use $crate::{CodegenBackend, FunctionSignature, TypeDesc};

            let arena = Arena::new();
            let body = $mir_fn(&arena, $value);
            let sig = FunctionSignature::new()
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = $backend;
            let ir = backend.compile_to_ir(&body, sig);
            let normalized = $normalize(&ir);
            insta::assert_snapshot!(normalized);
        }
    };

    // Variant: MIR builder with value arg, no normalizer
    ($name:ident, $backend:expr, $mir_fn:expr, $value:expr, () -> $ret:ty) => {
        #[test]
        fn $name() {
            use zir::Arena;
            use $crate::{CodegenBackend, FunctionSignature, TypeDesc};

            let arena = Arena::new();
            let body = $mir_fn(&arena, $value);
            let sig = FunctionSignature::new()
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = $backend;
            let ir = backend.compile_to_ir(&body, sig);
            insta::assert_snapshot!(ir);
        }
    };
}
