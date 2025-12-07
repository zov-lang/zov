//! CLIF codegen tests.

use zir::{Arena, mir};
use zir_codegen::testing::{
    compile_to_ir_text, create_add_function, create_const_function, create_max_function,
    run_standard_tests, sig_i64_i64_to_i64, sig_void_to_i64,
};
use zir_codegen::{CodegenConfig, FunctionSignature};
use zir_codegen_cranelift::create_backend;

const CALLING_CONVENTIONS: &[&str] =
    &["system_v", "apple_aarch64", "windows_fastcall", "fast", "cold", "tail"];

fn normalize_calling_convention(clif: &str) -> String {
    let mut result = clif.to_string();
    for conv in CALLING_CONVENTIONS {
        let pattern = format!(" {} {{", conv);
        result = result.replace(&pattern, " <calling_conv> {");
    }
    result
}

fn compile_to_clif(body: &mir::Body<'_>, sig: FunctionSignature) -> String {
    let mut backend = create_backend(CodegenConfig::default());
    let clif = compile_to_ir_text(backend.as_mut(), body, sig).expect("compile failed");
    normalize_calling_convention(&clif)
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
    let results = run_standard_tests(create_backend).expect("tests should pass");
    assert_eq!(results.len(), 4);
    for (name, ir) in &results {
        assert!(!ir.is_empty(), "{} produced empty IR", name);
        assert!(ir.contains("function"), "{} should contain 'function'", name);
    }
}
