//! Backend-agnostic integration tests for zir-codegen.
//!
//! These tests demonstrate that the `CodegenBackend` trait and testing utilities
//! work correctly with any backend implementation. The tests use only the
//! abstract interface, not any backend-specific types.

use zir::Arena;
use zir_codegen::CodegenConfig;
use zir_codegen::testing::{
    CodegenTestCase, compile_to_ir_text, create_add_function, create_const_function,
    create_max_function, run_standard_tests, sig_i64_i64_to_i64, sig_void_to_i64,
    standard_test_cases,
};

// Import the backend factory - this is the ONLY backend-specific import
use zir_codegen_cranelift::create_backend;

/// Test that the backend factory works and returns a valid backend.
#[test]
fn test_backend_factory() {
    let backend = create_backend(CodegenConfig::default());
    assert!(!backend.name().is_empty(), "Backend should have a name");
}

/// Test that the backend implements the trait correctly.
#[test]
fn test_backend_trait_implementation() {
    let backend = create_backend(CodegenConfig::default());

    // The backend should have a name
    let name = backend.name();
    assert!(!name.is_empty(), "Backend name should not be empty");

    // The backend should return its config
    let config = backend.config();
    assert!(!config.optimize, "Default config should not optimize");
}

/// Test compiling a simple constant function through the abstract interface.
#[test]
fn test_compile_const_function() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 42);

    let mut backend = create_backend(CodegenConfig::default());
    let ir_text = compile_to_ir_text(backend.as_mut(), &body, sig_void_to_i64());

    assert!(!ir_text.is_empty(), "Generated IR should not be empty");
}

/// Test compiling a function with parameters.
#[test]
fn test_compile_function_with_params() {
    let arena = Arena::new();
    let body = create_add_function(&arena);

    let mut backend = create_backend(CodegenConfig::default());
    let ir_text = compile_to_ir_text(backend.as_mut(), &body, sig_i64_i64_to_i64());

    assert!(!ir_text.is_empty(), "Generated IR should not be empty");
}

/// Test compiling a function with control flow.
#[test]
fn test_compile_function_with_control_flow() {
    let arena = Arena::new();
    let body = create_max_function(&arena);

    let mut backend = create_backend(CodegenConfig::default());
    let ir_text = compile_to_ir_text(backend.as_mut(), &body, sig_i64_i64_to_i64());

    assert!(!ir_text.is_empty(), "Generated IR should not be empty");
}

/// Test using CodegenTestCase abstraction.
#[test]
fn test_codegen_test_case() {
    let arena = Arena::new();
    let test_case =
        CodegenTestCase::new("test_const", create_const_function(&arena, 100), sig_void_to_i64());

    let mut backend = create_backend(CodegenConfig::default());
    let ir = test_case.run(backend.as_mut());

    assert!(!ir.is_empty(), "Test case should produce non-empty IR");
}

/// Test the standard test cases utility.
#[test]
fn test_standard_test_cases() {
    let arena = Arena::new();
    let test_cases = standard_test_cases(&arena);

    // Should have all expected test cases
    assert_eq!(test_cases.len(), 4);

    // Each test case should have a name
    let names: Vec<_> = test_cases.iter().map(|tc| tc.name).collect();
    assert!(names.contains(&"const_42"));
    assert!(names.contains(&"const_negative"));
    assert!(names.contains(&"add_function"));
    assert!(names.contains(&"max_function"));
}

/// Test running all standard tests through the factory.
#[test]
fn test_run_standard_tests() {
    let results = run_standard_tests(create_backend);

    assert_eq!(results.len(), 4, "Should have 4 test results");

    for (name, ir) in &results {
        assert!(!ir.is_empty(), "Test '{}' should produce non-empty IR", name);
    }
}

/// Test that multiple backends can be created independently.
#[test]
fn test_multiple_backend_instances() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 1);

    // Create multiple backends - they should be independent
    let mut backend1 = create_backend(CodegenConfig::default());
    let mut backend2 = create_backend(CodegenConfig::default());

    let ir1 = compile_to_ir_text(backend1.as_mut(), &body, sig_void_to_i64());
    let ir2 = compile_to_ir_text(backend2.as_mut(), &body, sig_void_to_i64());

    // Both should produce the same output for the same input
    assert_eq!(ir1, ir2, "Same input should produce same output");
}

/// Test that backends with different configs can coexist.
#[test]
fn test_backend_config_independence() {
    let config1 = CodegenConfig { optimize: false, debug_info: false };
    let config2 = CodegenConfig { optimize: true, debug_info: true };

    let backend1 = create_backend(config1);
    let backend2 = create_backend(config2);

    assert!(!backend1.config().optimize);
    assert!(backend2.config().optimize);
    assert!(!backend1.config().debug_info);
    assert!(backend2.config().debug_info);
}

// ============================================================================
// IrChecker Tests
// ============================================================================

use zir_codegen::testing::IrChecker;

/// Test IrChecker basic CHECK directive.
#[test]
fn test_ir_checker_check() {
    let ir = "function add(i64, i64) -> i64 {\nblock0:\n  v0 = iadd v1, v2\n  return v0\n}";
    let checker = IrChecker::new(ir);
    checker.check("iadd").check("return").verify();
}

/// Test IrChecker CHECK-NOT directive.
#[test]
fn test_ir_checker_check_not() {
    let ir = "function add(i64, i64) -> i64 {\nblock0:\n  v0 = iadd v1, v2\n  return v0\n}";
    let checker = IrChecker::new(ir);
    checker.check_not("imul").check_not("isub").verify();
}

/// Test IrChecker CHECK-NEXT directive.
#[test]
fn test_ir_checker_check_next() {
    let ir = "line1: first\nline2: second\nline3: third";
    let checker = IrChecker::new(ir);
    checker.check("first").check_next("second").check_next("third").verify();
}

/// Test IrChecker with actual generated IR.
#[test]
fn test_ir_checker_with_cranelift_ir() {
    let arena = Arena::new();
    let body = create_add_function(&arena);

    let mut backend = create_backend(CodegenConfig::default());
    let ir = compile_to_ir_text(backend.as_mut(), &body, sig_i64_i64_to_i64());

    // Verify the IR contains expected Cranelift patterns
    IrChecker::new(&ir)
        .check("function")
        .check("i64")
        .check("iadd")
        .check("return")
        .check_not("imul")
        .verify();
}

/// Test IrChecker error reporting.
#[test]
fn test_ir_checker_errors() {
    let ir = "function foo() {}";
    let checker = IrChecker::new(ir).check("nonexistent");
    assert!(!checker.is_ok());
    assert!(!checker.errors().is_empty());
}

// ============================================================================
// TestBackendProvider Tests
// ============================================================================

use zir_codegen::CodegenBackend;
use zir_codegen::testing::TestBackendProvider;

/// Define Cranelift as a test backend provider.
struct CraneliftProvider;

impl TestBackendProvider for CraneliftProvider {
    fn name() -> &'static str {
        "cranelift"
    }

    fn create(config: CodegenConfig) -> Box<dyn CodegenBackend> {
        create_backend(config)
    }
}

/// Test TestBackendProvider trait with Cranelift.
#[test]
fn test_backend_provider_trait() {
    assert_eq!(CraneliftProvider::name(), "cranelift");
    assert!(CraneliftProvider::is_available());

    let backend = CraneliftProvider::create(CodegenConfig::default());
    assert_eq!(backend.name(), "cranelift");
}

/// Test running tests via the TestBackendProvider trait.
#[test]
fn test_run_with_backend_provider() {
    use zir_codegen::testing::run_test_with_backend;

    let arena = Arena::new();
    let test_case =
        CodegenTestCase::new("provider_test", create_const_function(&arena, 99), sig_void_to_i64());

    let ir = run_test_with_backend::<CraneliftProvider>(&test_case);
    assert!(!ir.is_empty());
    assert!(ir.contains("function"));
}
