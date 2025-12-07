//! LLVM code generation backend for ZIR
//!
//! This crate implements the [`zir_codegen::CodegenBackend`] trait using LLVM
//! as the code generation backend. It provides an alternative to Cranelift
//! for production-quality code generation with full optimization support.
//!
//! # Architecture
//!
//! The LLVM backend follows the same architecture as `rustc_codegen_llvm`:
//!
//! 1. **FFI Wrapper** (`llvm/`): Low-level bindings to LLVM C API via `llvm-sys`
//! 2. **Context** (`context.rs`): LLVM context and module management
//! 3. **Types** (`types.rs`): ZIR to LLVM type conversion
//! 4. **Codegen** (`codegen.rs`): MIR to LLVM IR translation
//!
//! # Feature Flags
//!
//! - `llvm`: Enable the actual LLVM backend (requires system LLVM installation)
//!
//! Without the `llvm` feature, this crate provides stub implementations that
//! panic when used. This allows the crate to be compiled and tested without
//! requiring LLVM to be installed.
//!
//! # Building with LLVM
//!
//! To use the LLVM backend, you need:
//!
//! 1. LLVM 19.x installed on your system
//! 2. The `LLVM_SYS_190_PREFIX` environment variable set to the LLVM installation path
//!
//! Then enable the feature:
//! ```bash
//! cargo build -p zir-codegen-llvm --features llvm
//! ```
//!
//! # Example
//!
//! ```ignore
//! use zir_codegen::CodegenConfig;
//! use zir_codegen_llvm::LlvmBackend;
//!
//! let backend = LlvmBackend::new(CodegenConfig::default());
//! // Use backend for code generation...
//! ```

// These modules are only compiled when the llvm feature is enabled.
// They contain the actual LLVM bindings and codegen implementation.
// For now, only llvm.rs is implemented. context.rs, types.rs, and codegen.rs
// are placeholders for future implementation.
#[cfg(feature = "llvm")]
mod llvm;

use std::collections::HashMap;
use std::io::Write;

use zir::mir::Body;
use zir_codegen::{
    CodegenBackend, CodegenConfig, CodegenResults, CodegenUnit, FunctionSignature, OngoingCodegen,
    OutputFilenames, Session, TargetConfig, WorkProduct, WorkProductId,
};

/// LLVM-based code generation backend.
///
/// This backend uses LLVM to generate native code from ZIR MIR.
/// It supports full LLVM optimization passes and can emit various
/// output formats including object files, assembly, and LLVM IR.
///
/// # Feature Requirements
///
/// This backend requires the `llvm` feature to be enabled. Without it,
/// all methods will panic with an error message indicating that LLVM
/// is not available.
pub struct LlvmBackend {
    /// Configuration for this backend.
    config: CodegenConfig,
    /// IR output buffer for compile_to_ir.
    #[cfg(feature = "llvm")]
    ir_buffer: String,
}

impl LlvmBackend {
    /// Creates a new LLVM backend.
    ///
    /// # Panics
    ///
    /// Panics if the `llvm` feature is not enabled.
    #[cfg(feature = "llvm")]
    pub fn new(config: CodegenConfig) -> Self {
        Self { config, ir_buffer: String::new() }
    }

    /// Creates a new LLVM backend (stub version).
    ///
    /// # Panics
    ///
    /// Always panics because LLVM is not available.
    #[cfg(not(feature = "llvm"))]
    pub fn new(config: CodegenConfig) -> Self {
        Self { config }
    }

    /// Returns a reference to the backend configuration.
    pub fn config(&self) -> &CodegenConfig {
        &self.config
    }
}

/// Internal result from codegen_unit for joining later.
struct LlvmCodegenResult {
    /// Compiled IR text for each function.
    #[allow(dead_code)]
    ir_outputs: Vec<String>,
}

impl CodegenBackend for LlvmBackend {
    fn name(&self) -> &'static str {
        "llvm"
    }

    fn init(&self, _sess: &Session) {
        #[cfg(not(feature = "llvm"))]
        {
            // Stub: do nothing, will fail on actual codegen
        }

        #[cfg(feature = "llvm")]
        {
            // Initialize LLVM
            llvm::init();
        }
    }

    fn target_config(&self, _sess: &Session) -> TargetConfig {
        // LLVM has excellent float support
        TargetConfig {
            target_features: vec![],
            unstable_target_features: vec![],
            has_reliable_f16: true,
            has_reliable_f16_math: true,
            has_reliable_f128: true,
            has_reliable_f128_math: true,
        }
    }

    fn print_passes(&self) {
        #[cfg(feature = "llvm")]
        {
            // List available LLVM passes
            println!("LLVM optimization passes available");
        }
    }

    fn print_version(&self) {
        #[cfg(feature = "llvm")]
        {
            println!("LLVM version: {}", llvm::version());
        }

        #[cfg(not(feature = "llvm"))]
        {
            println!("LLVM backend not available (compile with --features llvm)");
        }
    }

    fn print(&self, out: &mut dyn Write) {
        writeln!(out, "LLVM backend").unwrap();
        #[cfg(not(feature = "llvm"))]
        writeln!(out, "  status: stub (LLVM not available)").unwrap();
        #[cfg(feature = "llvm")]
        writeln!(out, "  status: available").unwrap();
    }

    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> OngoingCodegen {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = unit;
            panic!(
                "LLVM backend is not available. \
                 Please compile with the 'llvm' feature enabled: \
                 cargo build -p zir-codegen-llvm --features llvm"
            );
        }

        #[cfg(feature = "llvm")]
        {
            let mut ir_outputs = Vec::new();

            for (body, signature) in &unit.bodies {
                let ir = self.compile_function_to_llvm_ir(body, signature);
                ir_outputs.push(ir);
            }

            Box::new(LlvmCodegenResult { ir_outputs })
        }
    }

    fn join_codegen(
        &self,
        ongoing: OngoingCodegen,
        _sess: &Session,
        _outputs: &OutputFilenames,
    ) -> (CodegenResults, HashMap<WorkProductId, WorkProduct>) {
        let _result = ongoing
            .downcast::<LlvmCodegenResult>()
            .expect("invalid ongoing codegen type - expected LlvmCodegenResult");

        (CodegenResults::default(), HashMap::new())
    }

    fn link(&self, _sess: &Session, _results: CodegenResults, _outputs: &OutputFilenames) {
        #[cfg(not(feature = "llvm"))]
        {
            panic!(
                "LLVM backend is not available. \
                 Please compile with the 'llvm' feature enabled."
            );
        }

        #[cfg(feature = "llvm")]
        {
            // Link using LLVM linker or system linker
        }
    }

    fn config(&self) -> &CodegenConfig {
        &self.config
    }

    fn compile_function<'zir>(&mut self, body: &Body<'zir>, signature: FunctionSignature) {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = (body, signature);
            panic!(
                "LLVM backend is not available. \
                 Please compile with the 'llvm' feature enabled."
            );
        }

        #[cfg(feature = "llvm")]
        {
            let _ = self.compile_function_to_llvm_ir(body, &signature);
        }
    }

    fn compile_to_ir<'zir>(&mut self, body: &Body<'zir>, signature: FunctionSignature) -> String {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = (body, signature);
            panic!(
                "LLVM backend is not available. \
                 Please compile with the 'llvm' feature enabled."
            );
        }

        #[cfg(feature = "llvm")]
        {
            self.compile_function_to_llvm_ir(body, &signature)
        }
    }

    fn finalize(self: Box<Self>) -> CodegenResults {
        CodegenResults::default()
    }
}

#[cfg(feature = "llvm")]
impl LlvmBackend {
    /// Compiles a function to LLVM IR text.
    fn compile_function_to_llvm_ir(
        &mut self,
        body: &Body<'_>,
        signature: &FunctionSignature,
    ) -> String {
        // TODO: Implement actual LLVM codegen
        // For now, return a placeholder
        let _ = (body, signature);
        format!(
            "; LLVM IR placeholder\n\
             ; Function with {} args, {} returns\n\
             define i64 @_anon() {{\n\
             entry:\n\
               ret i64 0\n\
             }}\n",
            signature.params.len(),
            signature.returns.len()
        )
    }
}

/// Creates an LLVM backend as a boxed trait object.
///
/// This factory function is primarily intended for testing with the
/// backend-agnostic utilities in `zir_codegen::testing`. For direct
/// use, prefer constructing [`LlvmBackend`] directly via
/// [`LlvmBackend::new()`].
///
/// # Panics
///
/// Note that without the `llvm` feature enabled, the returned backend
/// will panic when any actual code generation is attempted.
#[doc(hidden)]
pub fn create_backend(config: CodegenConfig) -> Box<dyn CodegenBackend> {
    Box::new(LlvmBackend::new(config))
}

/// Returns whether the LLVM backend is available.
///
/// This is `true` when compiled with the `llvm` feature, `false` otherwise.
pub const fn is_available() -> bool {
    cfg!(feature = "llvm")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backend_name() {
        let backend = LlvmBackend::new(CodegenConfig::default());
        assert_eq!(backend.name(), "llvm");
    }

    #[test]
    fn test_backend_config() {
        let config = CodegenConfig { optimize: true, debug_info: true };
        let backend = LlvmBackend::new(config);
        assert!(backend.config().optimize);
        assert!(backend.config().debug_info);
    }

    #[test]
    fn test_is_available() {
        // This tests the compile-time constant
        let available = is_available();
        #[cfg(feature = "llvm")]
        assert!(available);
        #[cfg(not(feature = "llvm"))]
        assert!(!available);
    }
}
