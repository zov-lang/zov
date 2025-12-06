//! CLIF codegen tests for zir-codegen-cranelift
//!
//! These tests verify that MIR is correctly compiled to Cranelift IR (CLIF).
//! The tests use direct `CraneliftBackend` instantiation and a declarative
//! macro for cleaner test definitions.

use zir::Arena;
use zir_codegen::testing::{
    create_add_function, create_const_function, create_max_function, run_standard_tests,
    sig_i64_i64_to_i64, sig_void_to_i64,
};
use zir_codegen::{CodegenBackend, CodegenConfig};
use zir_codegen_cranelift::{CraneliftBackend, create_backend};

// ============================================================================
// Helper Functions
// ============================================================================

/// Normalizes calling conventions in CLIF output for cross-platform snapshot testing.
///
/// Different platforms use different calling conventions (e.g., `system_v` on Linux,
/// `apple_aarch64` on macOS ARM). This function replaces platform-specific calling
/// conventions with a generic `<call_conv>` placeholder to ensure snapshots are
/// consistent across all platforms.
fn normalize_clif(clif: &str) -> String {
    // List of calling conventions to normalize
    let calling_conventions =
        ["system_v", "apple_aarch64", "windows_fastcall", "fast", "cold", "tail", "probestack"];

    let mut result = clif.to_string();
    for conv in calling_conventions {
        result = result.replace(conv, "<call_conv>");
    }
    result
}

// ============================================================================
// Declarative Test Macro
// ============================================================================

/// Macro for declarative codegen test definitions.
///
/// This macro simplifies writing codegen tests by reducing boilerplate.
/// Tests are defined with a name, MIR builder function, and signature.
///
/// The generated CLIF is normalized to remove platform-specific calling
/// conventions, ensuring consistent snapshots across all platforms.
///
/// # Example
///
/// ```ignore
/// clif_test! {
///     name: test_add,
///     mir: create_add_function,
///     sig: sig_i64_i64_to_i64,
/// }
/// ```
macro_rules! clif_test {
    (
        name: $name:ident,
        mir: $mir_fn:expr,
        sig: $sig_fn:expr $(,)?
    ) => {
        #[test]
        fn $name() {
            let arena = Arena::new();
            let body = $mir_fn(&arena);
            let mut backend = CraneliftBackend::new(CodegenConfig::default());
            let clif = backend.compile_to_ir(&body, $sig_fn());
            let clif = normalize_clif(&clif);
            insta::assert_snapshot!(clif);
        }
    };
    // Variant for const functions with a value parameter
    (
        name: $name:ident,
        mir: $mir_fn:expr,
        value: $value:expr,
        sig: $sig_fn:expr $(,)?
    ) => {
        #[test]
        fn $name() {
            let arena = Arena::new();
            let body = $mir_fn(&arena, $value);
            let mut backend = CraneliftBackend::new(CodegenConfig::default());
            let clif = backend.compile_to_ir(&body, $sig_fn());
            let clif = normalize_clif(&clif);
            insta::assert_snapshot!(clif);
        }
    };
}

// ============================================================================
// CLIF IR Snapshot Tests
// ============================================================================

clif_test! {
    name: test_clif_const_42,
    mir: create_const_function,
    value: 42,
    sig: sig_void_to_i64,
}

clif_test! {
    name: test_clif_const_negative,
    mir: create_const_function,
    value: -123,
    sig: sig_void_to_i64,
}

clif_test! {
    name: test_clif_add_function,
    mir: create_add_function,
    sig: sig_i64_i64_to_i64,
}

clif_test! {
    name: test_clif_max_function,
    mir: create_max_function,
    sig: sig_i64_i64_to_i64,
}

// ============================================================================
// Backend Unit Tests (using direct instantiation)
// ============================================================================

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

// ============================================================================
// Backend Factory Tests (for backend-agnostic compatibility)
// ============================================================================

/// Test that the factory pattern works for backend-agnostic code.
/// The factory is kept for cases where code needs to work with any backend.
#[test]
fn test_standard_tests_via_factory() {
    // Run all standard tests using the backend factory
    // This demonstrates the factory's purpose: backend-agnostic test execution
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
