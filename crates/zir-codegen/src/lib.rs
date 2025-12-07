//! Backend-agnostic code generation traits for ZIR
//!
//! This crate provides the abstraction layer for code generation backends.
//! It defines traits that allow different backends (Cranelift, LLVM, etc.)
//! to implement code generation in a unified way.
//!
//! The design is inspired by rustc's `rustc_codegen_ssa` crate, which provides
//! backend-agnostic functions that depend on traits implemented by each backend.
//!
//! # Testing Infrastructure
//!
//! The [`testing`] module provides utilities for testing backends in a
//! uniform way. Use the [`declare_codegen_tests!`] and [`declare_codegen_snapshot_tests!`]
//! macros to declare tests that run across all backends.
//!
//! The [`testing::IrChecker`] type provides FileCheck-style verification
//! for generated IR, useful for asserting specific patterns appear in output.

pub mod testing;

use std::any::Any;
use std::borrow::Cow;
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;

use zir::mir::Body;

// ============================================================================
// Target Specification
// ============================================================================

/// Target specification for code generation.
///
/// Inspired by rustc's target specification, this describes the platform
/// we're compiling for.
#[derive(Clone, Debug)]
pub struct Target {
    /// Pointer width in bits (32 or 64).
    pub pointer_width: u32,
    /// Target triple (e.g., "x86_64-unknown-linux-gnu").
    pub triple: Cow<'static, str>,
    /// Architecture name (e.g., "x86_64", "aarch64").
    pub arch: Cow<'static, str>,
    /// Target-specific options.
    pub options: TargetOptions,
}

impl Target {
    /// Creates a target from a triple string.
    pub fn from_triple(triple: &str) -> Self {
        use std::str::FromStr;
        let parsed = target_lexicon::Triple::from_str(triple).unwrap_or(target_lexicon::HOST);
        let pointer_width = match parsed.pointer_width() {
            Ok(pw) => pw.bits() as u32,
            Err(_) => 64,
        };
        Self {
            pointer_width,
            triple: Cow::Owned(triple.to_string()),
            arch: Cow::Owned(parsed.architecture.to_string()),
            options: TargetOptions::default(),
        }
    }
}

/// Target-specific options.
#[derive(Clone, Debug, Default)]
pub struct TargetOptions {
    /// CPU name for optimization (e.g., "skylake", "apple-m1").
    pub cpu: Option<Cow<'static, str>>,
    /// Available target features (e.g., "sse4.2", "avx2").
    pub features: Vec<Cow<'static, str>>,
    /// Relocation model.
    pub relocation_model: RelocModel,
    /// Whether the target is like Windows.
    pub is_like_windows: bool,
    /// Whether the target is like macOS.
    pub is_like_macos: bool,
}

/// Relocation model for code generation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RelocModel {
    /// Static relocation model.
    Static,
    /// Position-independent code.
    #[default]
    Pic,
    /// Position-independent executable.
    Pie,
    /// Dynamic, non-PIC.
    DynamicNoPic,
}

/// Session context for compilation.
///
/// This provides access to compiler options, diagnostics, and other
/// session-level state needed during code generation.
///
/// Inspired by rustc's Session, this contains target information and
/// compiler options.
#[derive(Clone, Debug)]
pub struct Session {
    /// The target we're compiling for.
    pub target: Target,
}

impl Session {
    /// Creates a session with a specific target.
    pub fn new(target: Target) -> Self {
        Self { target }
    }

    /// Creates a session from a target triple string.
    pub fn from_triple(triple: &str) -> Self {
        Self { target: Target::from_triple(triple) }
    }
}

/// Configuration for code generation.
#[derive(Clone, Debug, Default)]
pub struct CodegenConfig {
    /// Whether to enable optimizations.
    pub optimize: bool,
    /// Whether to emit debug info.
    pub debug_info: bool,
}

/// Target-specific configuration returned by backends.
///
/// This structure holds information about the target platform that
/// backends may need to configure themselves properly.
///
/// Following rustc's pattern, float support defaults to `true` so backends
/// need to explicitly acknowledge when they don't support these types.
#[derive(Clone, Debug)]
pub struct TargetConfig {
    /// Available target features (e.g., "sse4.2", "avx2").
    pub target_features: Vec<Cow<'static, str>>,
    /// Unstable target features that may be enabled.
    pub unstable_target_features: Vec<Cow<'static, str>>,
    /// Whether the target supports reliable f16 operations.
    pub has_reliable_f16: bool,
    /// Whether the target supports reliable f16 math operations.
    pub has_reliable_f16_math: bool,
    /// Whether the target supports reliable f128 operations.
    pub has_reliable_f128: bool,
    /// Whether the target supports reliable f128 math operations.
    pub has_reliable_f128_math: bool,
}

/// Output file configuration.
///
/// Specifies where to write the various outputs of compilation.
#[derive(Clone, Debug, Default)]
pub struct OutputFilenames {
    /// Directory for output files.
    pub out_dir: PathBuf,
    /// Base name for output files.
    pub crate_name: String,
    /// Extra outputs to generate.
    pub outputs: Vec<OutputType>,
}

impl OutputFilenames {
    /// Creates a new output configuration.
    pub fn new(out_dir: PathBuf, crate_name: &str) -> Self {
        Self { out_dir, crate_name: crate_name.to_string(), outputs: vec![OutputType::Object] }
    }

    /// Returns the path for the given output type.
    pub fn path_for(&self, output_type: OutputType) -> PathBuf {
        let ext = output_type.extension();
        self.out_dir.join(format!("{}.{}", self.crate_name, ext))
    }
}

/// Types of output that can be generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutputType {
    /// Object file (.o)
    Object,
    /// Assembly file (.s)
    Assembly,
    /// LLVM IR or equivalent (.ll)
    LlvmIr,
    /// Bitcode or equivalent (.bc)
    Bitcode,
    /// Executable (no extension on Unix)
    Exe,
    /// Static library (.a)
    StaticLib,
    /// Dynamic library (.so/.dylib/.dll)
    DynamicLib,
}

impl OutputType {
    /// Returns the file extension for this output type.
    pub fn extension(self) -> &'static str {
        match self {
            OutputType::Object => "o",
            OutputType::Assembly => "s",
            OutputType::LlvmIr => "ll",
            OutputType::Bitcode => "bc",
            OutputType::Exe => "",
            OutputType::StaticLib => "a",
            OutputType::DynamicLib => "so",
        }
    }
}

/// Compiled module output.
///
/// This struct represents the result of compiling a single codegen unit,
/// containing the object code and any metadata.
#[derive(Debug)]
pub struct CompiledModule {
    /// Name of the compiled module.
    pub name: String,
    /// Path to the object file, if emitted.
    pub object_path: Option<PathBuf>,
    /// Raw object code, if kept in memory.
    pub object_code: Option<Vec<u8>>,
    /// Path to the assembly file, if emitted.
    pub assembly_path: Option<PathBuf>,
    /// Path to the IR file, if emitted.
    pub ir_path: Option<PathBuf>,
}

impl CompiledModule {
    /// Creates a new compiled module.
    pub fn new(name: String) -> Self {
        Self { name, object_path: None, object_code: None, assembly_path: None, ir_path: None }
    }
}

/// Code generation results from a backend.
#[derive(Debug, Default)]
pub struct CodegenResults {
    /// Compiled modules.
    pub modules: Vec<CompiledModule>,
    /// Linker arguments needed for final linking.
    pub linker_args: Vec<String>,
}

/// Ongoing codegen state that can be passed between phases.
///
/// This allows backends to perform codegen in parallel and then
/// join the results.
pub type OngoingCodegen = Box<dyn Any + Send>;

/// Work product identifier for incremental compilation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WorkProductId(pub String);

/// Cached work product for incremental compilation.
#[derive(Clone, Debug)]
pub struct WorkProduct {
    /// Path to the cached artifact.
    pub path: PathBuf,
    /// Hash of the work product for invalidation.
    pub hash: u64,
}

/// A codegen unit - a collection of items to be compiled together.
#[derive(Debug)]
pub struct CodegenUnit<'a> {
    /// Name of this codegen unit.
    pub name: String,
    /// MIR bodies to compile.
    pub bodies: Vec<(&'a Body<'a>, FunctionSignature)>,
}

impl<'a> CodegenUnit<'a> {
    /// Creates a new codegen unit.
    pub fn new(name: &str) -> Self {
        Self { name: name.to_string(), bodies: Vec::new() }
    }

    /// Adds a function body to this codegen unit.
    pub fn add_function(&mut self, body: &'a Body<'a>, signature: FunctionSignature) {
        self.bodies.push((body, signature));
    }
}

/// Function signature for code generation.
///
/// This is a backend-agnostic representation of a function signature.
#[derive(Clone, Debug, Default)]
pub struct FunctionSignature {
    /// Parameter types.
    pub params: Vec<TypeDesc>,
    /// Return types.
    pub returns: Vec<TypeDesc>,
}

/// Type descriptor for function signatures.
#[derive(Clone, Debug)]
pub enum TypeDesc {
    /// Boolean type.
    Bool,
    /// Signed integer with bit width.
    Int(u32),
    /// Unsigned integer with bit width.
    Uint(u32),
    /// Pointer-sized signed integer.
    Isize,
    /// Pointer-sized unsigned integer.
    Usize,
    /// Pointer type.
    Ptr,
}

impl TypeDesc {
    /// Returns the size of this type in bits for a given pointer width.
    pub fn bit_width(&self, pointer_width: u32) -> u32 {
        match self {
            TypeDesc::Bool => 1,
            TypeDesc::Int(bits) | TypeDesc::Uint(bits) => *bits,
            TypeDesc::Isize | TypeDesc::Usize | TypeDesc::Ptr => pointer_width,
        }
    }
}

impl FunctionSignature {
    /// Creates a new empty signature.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a parameter type.
    pub fn with_param(mut self, ty: TypeDesc) -> Self {
        self.params.push(ty);
        self
    }

    /// Adds a return type.
    pub fn with_return(mut self, ty: TypeDesc) -> Self {
        self.returns.push(ty);
        self
    }
}

/// The main trait for code generation backends.
///
/// This trait abstracts over different code generation backends
/// (Cranelift, LLVM, etc.) and provides a unified interface for
/// compiling MIR to machine code.
///
/// The design follows rustc's `CodegenBackend` trait pattern with
/// lifecycle methods that mirror the compilation pipeline:
///
/// 1. `init()` - Initialize the backend with session info
/// 2. `target_config()` - Query target-specific configuration
/// 3. `codegen_unit()` - Compile a unit of code
/// 4. `join_codegen()` - Collect parallel codegen results
/// 5. `link()` - Link the final output
pub trait CodegenBackend: Any {
    /// Returns the name of this backend (e.g., "cranelift", "llvm").
    fn name(&self) -> &'static str;

    /// Initializes the backend with session configuration.
    ///
    /// This is called once before any codegen operations. Backends
    /// can use this to set up internal state based on compiler options.
    fn init(&self, _sess: &Session) {}

    /// Returns target-specific configuration.
    ///
    /// This allows backends to report what features they support for
    /// the current target, enabling frontend decisions about code generation.
    ///
    /// Note: The default returns `has_reliable_f16/f128 = true` so that
    /// backends must explicitly acknowledge when they don't support these
    /// types, rather than silently skipping tests.
    fn target_config(&self, _sess: &Session) -> TargetConfig {
        TargetConfig {
            target_features: vec![],
            unstable_target_features: vec![],
            has_reliable_f16: true,
            has_reliable_f16_math: true,
            has_reliable_f128: true,
            has_reliable_f128_math: true,
        }
    }

    /// Prints information about available passes.
    fn print_passes(&self) {}

    /// Prints the backend version.
    fn print_version(&self) {}

    /// Writes backend-specific information to the given writer.
    fn print(&self, _out: &mut dyn Write) {}

    /// Compiles a single codegen unit.
    ///
    /// This method takes a collection of MIR bodies and compiles them
    /// into backend-specific IR. The result is an opaque `OngoingCodegen`
    /// that can later be passed to `join_codegen()`.
    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> OngoingCodegen;

    /// Joins ongoing codegen and produces final results.
    ///
    /// This method is called after all codegen units have been compiled.
    /// It combines the results and produces the final `CodegenResults`
    /// along with any work products for incremental compilation.
    fn join_codegen(
        &self,
        ongoing: OngoingCodegen,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> (CodegenResults, HashMap<WorkProductId, WorkProduct>);

    /// Links the compiled modules into the final output.
    ///
    /// This is the final step in code generation. It takes the compiled
    /// modules from `join_codegen()` and produces the final executable,
    /// library, or object file.
    fn link(&self, sess: &Session, results: CodegenResults, outputs: &OutputFilenames);

    /// Returns the configuration for this backend.
    fn config(&self) -> &CodegenConfig;

    // === Convenience methods for simpler use cases ===

    /// Compiles a single MIR function body.
    ///
    /// This is a convenience method for simple use cases where you just
    /// want to compile a single function without the full codegen_unit pipeline.
    fn compile_function<'zir>(&mut self, body: &Body<'zir>, signature: FunctionSignature);

    /// Compiles a MIR function and returns the IR representation as text.
    ///
    /// This method is useful for testing the code generation output
    /// without actually executing the generated code. The returned
    /// IR can be compared against expected snapshots.
    fn compile_to_ir<'zir>(&mut self, body: &Body<'zir>, signature: FunctionSignature) -> String;

    /// Finalizes the compilation and returns the results.
    ///
    /// This is a convenience method that combines `join_codegen()` with
    /// default session and output settings.
    fn finalize(self: Box<Self>) -> CodegenResults;
}

/// Factory function type for creating backends.
///
/// This type is primarily used for testing infrastructure.
/// For production code, prefer constructing backends directly.
#[doc(hidden)]
pub type BackendFactory = fn(CodegenConfig) -> Box<dyn CodegenBackend>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen_config_default() {
        let config = CodegenConfig::default();
        assert!(!config.optimize);
        assert!(!config.debug_info);
    }

    #[test]
    fn test_function_signature_builder() {
        let sig = FunctionSignature::new()
            .with_param(TypeDesc::Int(64))
            .with_param(TypeDesc::Int(64))
            .with_return(TypeDesc::Int(64));

        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
    }

    #[test]
    fn test_target_from_triple() {
        let target = Target::from_triple("x86_64-unknown-linux-gnu");
        assert_eq!(target.pointer_width, 64);
        assert_eq!(target.triple.as_ref(), "x86_64-unknown-linux-gnu");
        assert_eq!(target.arch.as_ref(), "x86_64");
    }

    #[test]
    fn test_session_from_triple() {
        let session = Session::from_triple("aarch64-unknown-linux-gnu");
        assert_eq!(session.target.triple.as_ref(), "aarch64-unknown-linux-gnu");
    }

    #[test]
    fn test_output_filenames() {
        use std::path::Path;

        let outputs = OutputFilenames::new(PathBuf::from("/tmp"), "myprogram");
        assert_eq!(outputs.path_for(OutputType::Object), Path::new("/tmp/myprogram.o"));
        assert_eq!(outputs.path_for(OutputType::Assembly), Path::new("/tmp/myprogram.s"));
    }

    #[test]
    fn test_type_desc_bit_width() {
        assert_eq!(TypeDesc::Bool.bit_width(64), 1);
        assert_eq!(TypeDesc::Int(32).bit_width(64), 32);
        assert_eq!(TypeDesc::Uint(64).bit_width(64), 64);
        assert_eq!(TypeDesc::Ptr.bit_width(64), 64);
        assert_eq!(TypeDesc::Ptr.bit_width(32), 32);
    }

    #[test]
    fn test_codegen_unit() {
        let unit = CodegenUnit::new("test_unit");
        assert_eq!(unit.name, "test_unit");
        assert!(unit.bodies.is_empty());
    }

    #[test]
    fn test_compiled_module() {
        let module = CompiledModule::new("test_module".to_string());
        assert_eq!(module.name, "test_module");
        assert!(module.object_path.is_none());
        assert!(module.object_code.is_none());
    }

    #[test]
    fn test_work_product_id() {
        let id1 = WorkProductId("module1".to_string());
        let id2 = WorkProductId("module1".to_string());
        let id3 = WorkProductId("module2".to_string());
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_reloc_model_default() {
        let model = RelocModel::default();
        assert_eq!(model, RelocModel::Pic);
    }
}
