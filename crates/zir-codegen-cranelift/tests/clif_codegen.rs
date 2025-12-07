//! CLIF codegen tests for zir-codegen-cranelift

use zir::Arena;
use zir_codegen::testing::{
    create_add_function, create_const_function, create_max_function, run_standard_tests,
};
use zir_codegen::{CodegenBackend, CodegenConfig, FunctionSignature, TypeDesc};
use zir_codegen_cranelift::{CraneliftBackend, create_backend};

/// Normalizes calling conventions in CLIF output for cross-platform snapshot testing.
fn normalize_clif(clif: &str) -> String {
    let calling_conventions =
        ["system_v", "apple_aarch64", "windows_fastcall", "fast", "cold", "tail", "probestack"];

    let mut result = clif.to_string();
    for conv in calling_conventions {
        result = result.replace(conv, "<call_conv>");
    }
    result
}

/// Macro for declarative codegen tests with inline signature specification.
macro_rules! clif_test {
    // Variant: mir builder with no arguments
    ($name:ident, $mir_fn:expr, () -> $ret:ty) => {
        #[test]
        fn $name() {
            let arena = Arena::new();
            let body = $mir_fn(&arena);
            let sig = FunctionSignature::new()
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = CraneliftBackend::new(CodegenConfig::default());
            let clif = backend.compile_to_ir(&body, sig);
            insta::assert_snapshot!(normalize_clif(&clif));
        }
    };
    // Variant: mir builder with value argument
    ($name:ident, $mir_fn:expr, $value:expr, () -> $ret:ty) => {
        #[test]
        fn $name() {
            let arena = Arena::new();
            let body = $mir_fn(&arena, $value);
            let sig = FunctionSignature::new()
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = CraneliftBackend::new(CodegenConfig::default());
            let clif = backend.compile_to_ir(&body, sig);
            insta::assert_snapshot!(normalize_clif(&clif));
        }
    };
    // Variant: mir builder with two params and return
    ($name:ident, $mir_fn:expr, ($p1:ty, $p2:ty) -> $ret:ty) => {
        #[test]
        fn $name() {
            let arena = Arena::new();
            let body = $mir_fn(&arena);
            let sig = FunctionSignature::new()
                .with_param(TypeDesc::Int((std::mem::size_of::<$p1>() * 8) as u32))
                .with_param(TypeDesc::Int((std::mem::size_of::<$p2>() * 8) as u32))
                .with_return(TypeDesc::Int((std::mem::size_of::<$ret>() * 8) as u32));
            let mut backend = CraneliftBackend::new(CodegenConfig::default());
            let clif = backend.compile_to_ir(&body, sig);
            insta::assert_snapshot!(normalize_clif(&clif));
        }
    };
}

clif_test!(test_clif_const_42, create_const_function, 42, () -> i64);
clif_test!(test_clif_const_negative, create_const_function, -123, () -> i64);
clif_test!(test_clif_add_function, create_add_function, (i64, i64) -> i64);
clif_test!(test_clif_max_function, create_max_function, (i64, i64) -> i64);

#[test]
fn test_backend_name() {
    let backend = CraneliftBackend::new(CodegenConfig::default());
    assert_eq!(backend.name(), "cranelift");
}

#[test]
fn test_backend_config() {
    let config = CodegenConfig { optimize: true, debug_info: true };
    let backend = CraneliftBackend::new(config);
    assert!(backend.config().optimize);
    assert!(backend.config().debug_info);
}

#[test]
fn test_standard_tests_via_factory() {
    let results = run_standard_tests(create_backend);
    assert_eq!(results.len(), 4);
    for (name, ir) in &results {
        assert!(!ir.is_empty(), "Test '{}' produced empty IR", name);
        assert!(ir.contains("function"), "Test '{}' should contain 'function'", name);
    }
}
