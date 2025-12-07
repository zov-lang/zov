//! Backend-agnostic integration tests for zir-codegen.

use zir::Arena;
use zir_codegen::CodegenBackend;
use zir_codegen::testing::{
    CodegenTestCase, compile_to_ir_text, create_add_function, create_const_function,
    create_max_function, run_standard_tests, sig_i64_i64_to_i64, sig_void_to_i64,
    standard_test_cases,
};
use zir_codegen_cranelift::CraneliftBackend;

#[test]
fn test_backend_name() {
    let backend = CraneliftBackend::new();
    assert!(!backend.name().is_empty());
}

#[test]
fn test_compile_const_function() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 42);

    let mut backend = CraneliftBackend::new();
    let ir_text =
        compile_to_ir_text(&mut backend, &body, sig_void_to_i64()).expect("compilation failed");

    assert!(!ir_text.is_empty());
}

#[test]
fn test_compile_function_with_params() {
    let arena = Arena::new();
    let body = create_add_function(&arena);

    let mut backend = CraneliftBackend::new();
    let ir_text =
        compile_to_ir_text(&mut backend, &body, sig_i64_i64_to_i64()).expect("compilation failed");

    assert!(!ir_text.is_empty());
}

#[test]
fn test_compile_function_with_control_flow() {
    let arena = Arena::new();
    let body = create_max_function(&arena);

    let mut backend = CraneliftBackend::new();
    let ir_text =
        compile_to_ir_text(&mut backend, &body, sig_i64_i64_to_i64()).expect("compilation failed");

    assert!(!ir_text.is_empty());
}

#[test]
fn test_codegen_test_case() {
    let arena = Arena::new();
    let test_case =
        CodegenTestCase::new("test_const", create_const_function(&arena, 100), sig_void_to_i64());

    let mut backend = CraneliftBackend::new();
    let ir = test_case.run(&mut backend).expect("test case failed");

    assert!(!ir.is_empty());
}

#[test]
fn test_standard_test_cases() {
    let arena = Arena::new();
    let test_cases = standard_test_cases(&arena);

    assert_eq!(test_cases.len(), 4);

    let names: Vec<_> = test_cases.iter().map(|tc| tc.name).collect();
    assert!(names.contains(&"const_42"));
    assert!(names.contains(&"const_negative"));
    assert!(names.contains(&"add_function"));
    assert!(names.contains(&"max_function"));
}

#[test]
fn test_run_standard_tests() {
    let results =
        run_standard_tests(|| Box::new(CraneliftBackend::new())).expect("standard tests failed");

    assert_eq!(results.len(), 4);

    for (name, ir) in &results {
        assert!(!ir.is_empty(), "Test '{}' produced empty IR", name);
    }
}

#[test]
fn test_multiple_backend_instances() {
    let arena = Arena::new();
    let body = create_const_function(&arena, 1);

    let mut backend1 = CraneliftBackend::new();
    let mut backend2 = CraneliftBackend::new();

    let ir1 =
        compile_to_ir_text(&mut backend1, &body, sig_void_to_i64()).expect("compilation failed");
    let ir2 =
        compile_to_ir_text(&mut backend2, &body, sig_void_to_i64()).expect("compilation failed");

    assert_eq!(ir1, ir2);
}
