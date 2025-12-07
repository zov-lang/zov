//! Backend-agnostic testing utilities for code generation.
//!
//! This module provides utilities for testing [`CodegenBackend`] implementations
//! in a backend-independent way. Tests written using these utilities can be
//! run against any backend without modification.
//!
//! # Test Declaration
//!
//! The [`codegen_tests!`] macro provides a declarative way to define tests
//! that run across all available backends. Each test case is defined once
//! and automatically expanded to run against each backend.
//!
//! ```ignore
//! codegen_tests! {
//!     backends: [cranelift, llvm],
//!     tests: {
//!         test_const_42: create_const_function(42) => sig_void_to_i64(),
//!         test_add: create_add_function() => sig_i64_i64_to_i64(),
//!     }
//! }
//! ```
//!
//! # FileCheck-style Verification (Planned)
//!
//! Future versions will support FileCheck-style assertions:
//! ```ignore
//! // CHECK: iadd
//! // CHECK-NOT: imul
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

/// Trait for types that can provide a codegen backend for testing.
///
/// Implement this trait for each backend to enable unified testing.
/// The trait provides a factory method that creates backend instances.
///
/// # Example
///
/// ```ignore
/// struct CraneliftTestBackend;
///
/// impl TestBackendProvider for CraneliftTestBackend {
///     fn name() -> &'static str { "cranelift" }
///     fn create(config: CodegenConfig) -> Box<dyn CodegenBackend> {
///         Box::new(CraneliftBackend::new(config))
///     }
/// }
/// ```
pub trait TestBackendProvider {
    /// Returns the name of this backend (e.g., "cranelift", "llvm").
    fn name() -> &'static str;

    /// Creates a new backend instance with the given configuration.
    fn create(config: CodegenConfig) -> Box<dyn CodegenBackend>;

    /// Returns whether this backend is available on the current platform.
    ///
    /// Override this to conditionally skip tests on unsupported platforms.
    fn is_available() -> bool {
        true
    }
}

/// Runs a test case against a specific backend provider.
///
/// This is the core function used by the test macros to execute tests.
pub fn run_test_with_backend<B: TestBackendProvider>(test_case: &CodegenTestCase<'_>) -> String {
    if !B::is_available() {
        panic!("Backend '{}' is not available on this platform", B::name());
    }
    let mut backend = B::create(CodegenConfig::default());
    test_case.run(backend.as_mut())
}

/// Macro for declaring codegen tests that run across multiple backends.
///
/// This macro generates individual test functions for each combination of
/// test case and backend. The tests are named `{test_name}_{backend_name}`.
///
/// # Usage
///
/// ```ignore
/// use zir_codegen::declare_codegen_tests;
///
/// // First, define your backend providers
/// struct Cranelift;
/// impl TestBackendProvider for Cranelift {
///     fn name() -> &'static str { "cranelift" }
///     fn create(config: CodegenConfig) -> Box<dyn CodegenBackend> {
///         zir_codegen_cranelift::create_backend(config)
///     }
/// }
///
/// // Then declare the tests
/// declare_codegen_tests! {
///     #[backend(Cranelift)]
///     mod codegen_tests {
///         test_const_42 => |arena| {
///             (create_const_function(arena, 42), sig_void_to_i64())
///         };
///         test_add => |arena| {
///             (create_add_function(arena), sig_i64_i64_to_i64())
///         };
///     }
/// }
/// ```
#[macro_export]
macro_rules! declare_codegen_tests {
    (
        #[backend($backend:ty)]
        mod $mod_name:ident {
            $(
                $test_name:ident => |$arena:ident| $body:expr
            );* $(;)?
        }
    ) => {
        mod $mod_name {
            use super::*;
            use $crate::testing::*;
            use zir::Arena;

            $(
                #[test]
                fn $test_name() {
                    let $arena = Arena::new();
                    let (body, sig) = $body;
                    let test_case = CodegenTestCase::new(
                        stringify!($test_name),
                        body,
                        sig,
                    );
                    let ir = run_test_with_backend::<$backend>(&test_case);
                    assert!(!ir.is_empty(), "Generated IR should not be empty");
                }
            )*
        }
    };
}

/// Macro for declaring snapshot tests across backends.
///
/// Similar to [`declare_codegen_tests!`] but uses insta for snapshot testing.
/// Each test produces a snapshot file named `{test_name}_{backend_name}.snap`.
#[macro_export]
macro_rules! declare_codegen_snapshot_tests {
    (
        #[backend($backend:ty)]
        mod $mod_name:ident {
            $(
                $test_name:ident => |$arena:ident| $body:expr
            );* $(;)?
        }
    ) => {
        mod $mod_name {
            use super::*;
            use $crate::testing::*;
            use zir::Arena;

            $(
                #[test]
                fn $test_name() {
                    let $arena = Arena::new();
                    let (body, sig) = $body;
                    let test_case = CodegenTestCase::new(
                        stringify!($test_name),
                        body,
                        sig,
                    );
                    let ir = run_test_with_backend::<$backend>(&test_case);
                    insta::assert_snapshot!(ir);
                }
            )*
        }
    };
}

// ============================================================================
// FileCheck-style IR Verification (Experimental)
// ============================================================================

/// A simple pattern matcher for IR verification.
///
/// Provides basic CHECK directive support similar to LLVM's FileCheck tool.
/// This is useful for verifying that specific patterns appear in generated IR.
///
/// # Supported Directives
///
/// - `CHECK: pattern` - Verifies pattern appears in the output
/// - `CHECK-NOT: pattern` - Verifies pattern does NOT appear
/// - `CHECK-NEXT: pattern` - Verifies pattern appears on the next line
///
/// # Example
///
/// ```ignore
/// let ir = backend.compile_to_ir(&body, sig);
/// let checker = IrChecker::new(&ir);
/// checker
///     .check("iadd")
///     .check_not("imul")
///     .verify();
/// ```
pub struct IrChecker<'a> {
    ir: &'a str,
    lines: Vec<&'a str>,
    current_line: usize,
    errors: Vec<String>,
}

impl<'a> IrChecker<'a> {
    /// Creates a new IR checker for the given IR text.
    pub fn new(ir: &'a str) -> Self {
        let lines: Vec<&str> = ir.lines().collect();
        Self { ir, lines, current_line: 0, errors: Vec::new() }
    }

    /// Verifies that the pattern appears somewhere in the remaining IR.
    ///
    /// Advances the current position to after the matched line.
    pub fn check(mut self, pattern: &str) -> Self {
        let found = self.lines[self.current_line..].iter().position(|line| line.contains(pattern));

        match found {
            Some(offset) => {
                self.current_line += offset + 1;
            }
            None => {
                self.errors.push(format!(
                    "CHECK: pattern '{}' not found after line {}",
                    pattern, self.current_line
                ));
            }
        }
        self
    }

    /// Verifies that the pattern does NOT appear anywhere in the IR.
    pub fn check_not(mut self, pattern: &str) -> Self {
        if self.ir.contains(pattern) {
            self.errors
                .push(format!("CHECK-NOT: pattern '{}' was found but shouldn't be", pattern));
        }
        self
    }

    /// Verifies that the pattern appears on the very next line.
    pub fn check_next(mut self, pattern: &str) -> Self {
        if self.current_line >= self.lines.len() {
            self.errors.push(format!("CHECK-NEXT: no more lines, expected '{}'", pattern));
        } else if !self.lines[self.current_line].contains(pattern) {
            self.errors.push(format!(
                "CHECK-NEXT: line {} doesn't contain '{}', got: '{}'",
                self.current_line, pattern, self.lines[self.current_line]
            ));
        } else {
            self.current_line += 1;
        }
        self
    }

    /// Finalizes the check and panics if any errors occurred.
    pub fn verify(self) {
        if !self.errors.is_empty() {
            panic!(
                "IR verification failed:\n{}\n\nActual IR:\n{}",
                self.errors.join("\n"),
                self.ir
            );
        }
    }

    /// Returns whether all checks passed without panicking.
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// Returns the collected errors.
    pub fn errors(&self) -> &[String] {
        &self.errors
    }
}
