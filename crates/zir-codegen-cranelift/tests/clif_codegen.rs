//! Cranelift codegen tests using backend-agnostic test infrastructure.
//!
//! These tests demonstrate how to use the `codegen_test!` macro to define
//! tests that work with any backend. Each backend provides:
//! - A way to create backend instances
//! - A normalization function for cross-platform snapshots

use zir_codegen::testing::{create_add_function, create_const_function, create_max_function};
use zir_codegen::{CodegenBackend, CodegenConfig, codegen_test};
use zir_codegen_cranelift::CraneliftBackend;

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

/// Creates a fresh Cranelift backend for testing.
fn clif_backend() -> CraneliftBackend {
    CraneliftBackend::new(CodegenConfig::default())
}

// Backend-agnostic tests using the codegen_test! macro.
// These tests are defined once and can be replicated for any backend.

codegen_test!(clif_const_42, clif_backend(), create_const_function, 42, () -> i64, normalize_clif);
codegen_test!(clif_const_negative, clif_backend(), create_const_function, -123, () -> i64, normalize_clif);
codegen_test!(clif_add_function, clif_backend(), create_add_function, (i64, i64) -> i64, normalize_clif);
codegen_test!(clif_max_function, clif_backend(), create_max_function, (i64, i64) -> i64, normalize_clif);

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
