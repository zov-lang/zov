//! CLIF codegen tests for zir-codegen-cranelift
//!
//! These tests verify that MIR is correctly compiled to Cranelift IR (CLIF).
//! They use the backend-agnostic testing utilities from `zir_codegen::testing`
//! to create MIR bodies and compile them using the `CodegenBackend` trait.

use zir::{Arena, mir};
use zir_codegen::testing::{
    compile_to_ir_text, create_add_function, create_const_function, create_max_function,
    run_standard_tests, sig_i64_i64_to_i64, sig_void_to_i64,
};
use zir_codegen::{CodegenConfig, FunctionSignature};
use zir_codegen_cranelift::create_backend;

/// Helper to compile MIR to CLIF using the backend factory.
fn compile_to_clif(body: &mir::Body<'_>, sig: FunctionSignature) -> String {
    let mut backend = create_backend(CodegenConfig::default());
    compile_to_ir_text(backend.as_mut(), body, sig)
}

#[test]
fn test_backend_name() {
    let backend = create_backend(CodegenConfig::default());
    assert_eq!(backend.name(), "cranelift");
}

#[test]
fn test_clif_const_42() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 42);
    let clif = compile_to_clif(&body, sig_void_to_i64());
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_const_negative() {
    let arena = Arena::new();
    let body = create_const_function(&arena, -123);
    let clif = compile_to_clif(&body, sig_void_to_i64());
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_add_function() {
    let arena = Arena::new();
    let body = create_add_function(&arena);
    let clif = compile_to_clif(&body, sig_i64_i64_to_i64());
    insta::assert_snapshot!(clif);
}

#[test]
fn test_clif_max_function() {
    let arena = Arena::new();
    let body = create_max_function(&arena);
    let clif = compile_to_clif(&body, sig_i64_i64_to_i64());
    insta::assert_snapshot!(clif);
}

#[test]
fn test_standard_tests_all_pass() {
    // Run all standard tests using the backend factory
    let results = run_standard_tests(create_backend);

    // Verify we got all expected tests
    assert_eq!(results.len(), 4);

    // Verify each test produced non-empty IR
    for (name, ir) in &results {
        assert!(!ir.is_empty(), "Test '{}' produced empty IR", name);
        // All Cranelift functions should have a signature
        assert!(ir.contains("function"), "Test '{}' should contain 'function'", name);
    }
}
