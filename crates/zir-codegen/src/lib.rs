//! Backend-agnostic code generation traits for ZIR
//!
//! This crate provides the abstraction layer for code generation backends.
//! It defines traits that allow different backends (Cranelift, LLVM, etc.)
//! to implement code generation in a unified way.
//!
//! # Design
//!
//! The design is inspired by rustc's `rustc_codegen_ssa` crate, which provides
//! backend-agnostic functions that depend on traits implemented by each backend.
//!
//! # Key Traits
//!
//! - [`CodegenBackend`]: The main trait for code generation backends
//!
//! # Testing
//!
//! The [`testing`] module provides utilities for writing backend-agnostic
//! tests that can verify any implementation of [`CodegenBackend`].
//!
//! # Example
//!
//! ```ignore
//! use zir_codegen::{CodegenBackend, CodegenConfig, CodegenResult};
//!
//! let mut backend = SomeCraneliftBackend::new(CodegenConfig::default())?;
//! backend.init(&session);
//! let result = backend.codegen_unit(unit)?;
//! let (results, _) = backend.join_codegen(ongoing, &session, &outputs)?;
//! backend.link(&session, results, &outputs)?;
//! ```

pub mod testing;

use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::path::PathBuf;

use zir::mir::Body;

/// Session context for compilation.
///
/// This provides access to compiler options, diagnostics, and other
/// session-level state needed during code generation.
#[derive(Clone, Debug, Default)]
pub struct Session {
    /// Target triple (e.g., "x86_64-unknown-linux-gnu").
    pub target_triple: String,
    /// Optimization level (0-3).
    pub opt_level: u8,
    /// Whether debug info is enabled.
    pub debug_info: bool,
    /// Additional backend-specific options.
    pub backend_options: HashMap<String, String>,
}

impl Session {
    /// Creates a new session with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a session for the host target.
    pub fn for_host() -> Self {
        Self { target_triple: target_lexicon::HOST.to_string(), ..Default::default() }
    }

    /// Sets the optimization level.
    pub fn with_opt_level(mut self, level: u8) -> Self {
        self.opt_level = level;
        self
    }

    /// Enables debug info.
    pub fn with_debug_info(mut self, enabled: bool) -> Self {
        self.debug_info = enabled;
        self
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

/// Target-specific configuration.
///
/// This structure holds information about the target platform that
/// backends may need to configure themselves properly.
#[derive(Clone, Debug, Default)]
pub struct TargetConfig {
    /// Available target features (e.g., "sse4.2", "avx2").
    pub target_features: Vec<String>,
    /// Unstable target features that may be enabled.
    pub unstable_target_features: Vec<String>,
    /// Whether the target supports reliable f16 operations.
    pub has_reliable_f16: bool,
    /// Whether the target supports reliable f128 operations.
    pub has_reliable_f128: bool,
    /// Pointer width in bits.
    pub pointer_width: u32,
}

impl TargetConfig {
    /// Creates a default target config for the current host.
    pub fn for_host() -> Self {
        Self {
            pointer_width: std::mem::size_of::<*const ()>() as u32 * 8,
            has_reliable_f16: false,
            has_reliable_f128: false,
            ..Default::default()
        }
    }
}

/// Errors that can occur during code generation.
#[derive(Debug)]
pub enum CodegenError {
    /// Backend-specific module error.
    Module(String),
    /// Unsupported type.
    UnsupportedType(String),
    /// Invalid MIR.
    InvalidMir(String),
    /// Backend not available.
    BackendUnavailable(String),
    /// Linking error.
    Link(String),
    /// I/O error.
    Io(String),
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodegenError::Module(msg) => write!(f, "module error: {}", msg),
            CodegenError::UnsupportedType(ty) => write!(f, "unsupported type: {}", ty),
            CodegenError::InvalidMir(msg) => write!(f, "invalid MIR: {}", msg),
            CodegenError::BackendUnavailable(msg) => write!(f, "backend unavailable: {}", msg),
            CodegenError::Link(msg) => write!(f, "link error: {}", msg),
            CodegenError::Io(msg) => write!(f, "I/O error: {}", msg),
        }
    }
}

impl std::error::Error for CodegenError {}

impl From<std::io::Error> for CodegenError {
    fn from(err: std::io::Error) -> Self {
        CodegenError::Io(err.to_string())
    }
}

/// Result type for codegen operations.
pub type CodegenResult<T> = Result<T, CodegenError>;

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

/// IR output format for testing and debugging.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrOutput {
    /// Textual IR representation (e.g., CLIF for Cranelift).
    Text(String),
    /// Binary IR representation.
    Binary(Vec<u8>),
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
    /// Returns the size of this type in bits.
    ///
    /// For pointer-sized types, returns the host pointer width.
    pub fn bit_width(&self) -> u32 {
        match self {
            TypeDesc::Bool => 1,
            TypeDesc::Int(bits) | TypeDesc::Uint(bits) => *bits,
            TypeDesc::Isize | TypeDesc::Usize | TypeDesc::Ptr => {
                std::mem::size_of::<*const ()>() as u32 * 8
            }
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
/// # Design
///
/// The design follows rustc's `CodegenBackend` trait pattern with
/// lifecycle methods that mirror the compilation pipeline:
///
/// 1. `init()` - Initialize the backend with session info
/// 2. `target_config()` - Query target-specific configuration
/// 3. `codegen_unit()` - Compile a unit of code
/// 4. `join_codegen()` - Collect parallel codegen results
/// 5. `link()` - Link the final output
///
/// # Backend Responsibilities
///
/// Backends implementing this trait should:
/// 1. Initialize their internal state in `init()`
/// 2. Provide target configuration in `target_config()`
/// 3. Compile MIR to native IR in `codegen_unit()`
/// 4. Combine parallel results in `join_codegen()`
/// 5. Produce final output in `link()`
///
/// # Example Implementation
///
/// ```ignore
/// struct MyCraneliftBackend { /* ... */ }
///
/// impl CodegenBackend for MyCraneliftBackend {
///     fn name(&self) -> &'static str {
///         "cranelift"
///     }
///
///     fn init(&self, sess: &Session) {
///         // Initialize backend with session configuration
///     }
///
///     fn codegen_unit<'a>(
///         &mut self,
///         unit: CodegenUnit<'a>,
///     ) -> CodegenResult<OngoingCodegen> {
///         // Compile the unit
///         Ok(Box::new(results))
///     }
///
///     fn join_codegen(
///         &self,
///         ongoing: OngoingCodegen,
///         sess: &Session,
///         outputs: &OutputFilenames,
///     ) -> CodegenResult<(CodegenResults, HashMap<WorkProductId, WorkProduct>)> {
///         // Combine results
///         Ok((results, work_products))
///     }
///
///     fn link(
///         &self,
///         sess: &Session,
///         results: CodegenResults,
///         outputs: &OutputFilenames,
///     ) -> CodegenResult<()> {
///         // Link the final output
///         Ok(())
///     }
/// }
/// ```
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
    fn target_config(&self, _sess: &Session) -> TargetConfig {
        TargetConfig::for_host()
    }

    /// Prints information about available passes.
    ///
    /// Used for debugging and informational output.
    fn print_passes(&self) {}

    /// Prints the backend version.
    ///
    /// Used for debugging and informational output.
    fn print_version(&self) {}

    /// Writes backend-specific information to the given writer.
    ///
    /// This can be used for printing backend-specific debug info.
    fn print(&self, _out: &mut dyn Write) -> CodegenResult<()> {
        Ok(())
    }

    /// Compiles a single codegen unit.
    ///
    /// This method takes a collection of MIR bodies and compiles them
    /// into backend-specific IR. The result is an opaque `OngoingCodegen`
    /// that can later be passed to `join_codegen()`.
    ///
    /// For simple use cases, this can directly return the compiled results.
    /// For parallel compilation, this returns a handle that will be joined later.
    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> CodegenResult<OngoingCodegen>;

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
    ) -> CodegenResult<(CodegenResults, HashMap<WorkProductId, WorkProduct>)>;

    /// Links the compiled modules into the final output.
    ///
    /// This is the final step in code generation. It takes the compiled
    /// modules from `join_codegen()` and produces the final executable,
    /// library, or object file.
    fn link(
        &self,
        sess: &Session,
        results: CodegenResults,
        outputs: &OutputFilenames,
    ) -> CodegenResult<()>;

    /// Returns the configuration for this backend.
    fn config(&self) -> &CodegenConfig;

    // === Convenience methods for simpler use cases ===

    /// Compiles a single MIR function body.
    ///
    /// This is a convenience method for simple use cases where you just
    /// want to compile a single function without the full codegen_unit pipeline.
    fn compile_function<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<()>;

    /// Compiles a MIR function and returns the IR representation.
    ///
    /// This method is useful for testing the code generation output
    /// without actually executing the generated code. The returned
    /// IR can be compared against expected snapshots.
    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<IrOutput>;

    /// Finalizes the compilation and returns the results.
    ///
    /// This is a convenience method that combines `join_codegen()` with
    /// default session and output settings.
    fn finalize(self: Box<Self>) -> CodegenResult<CodegenResults>;
}

/// Factory function type for creating backends.
pub type BackendFactory = fn(CodegenConfig) -> CodegenResult<Box<dyn CodegenBackend>>;

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
    fn test_codegen_error_display() {
        let err = CodegenError::Module("test error".into());
        assert_eq!(err.to_string(), "module error: test error");

        let err = CodegenError::UnsupportedType("i256".into());
        assert_eq!(err.to_string(), "unsupported type: i256");

        let err = CodegenError::InvalidMir("bad block".into());
        assert_eq!(err.to_string(), "invalid MIR: bad block");

        let err = CodegenError::BackendUnavailable("LLVM".into());
        assert_eq!(err.to_string(), "backend unavailable: LLVM");

        let err = CodegenError::Link("linker failed".into());
        assert_eq!(err.to_string(), "link error: linker failed");

        let err = CodegenError::Io("file not found".into());
        assert_eq!(err.to_string(), "I/O error: file not found");
    }

    #[test]
    fn test_ir_output_equality() {
        let text1 = IrOutput::Text("function f() {}".into());
        let text2 = IrOutput::Text("function f() {}".into());
        let text3 = IrOutput::Text("function g() {}".into());

        assert_eq!(text1, text2);
        assert_ne!(text1, text3);
    }

    #[test]
    fn test_session_builder() {
        let session = Session::for_host().with_opt_level(2).with_debug_info(true);

        assert_eq!(session.opt_level, 2);
        assert!(session.debug_info);
        assert!(!session.target_triple.is_empty());
    }

    #[test]
    fn test_target_config_for_host() {
        let config = TargetConfig::for_host();
        assert!(config.pointer_width == 32 || config.pointer_width == 64);
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
        assert_eq!(TypeDesc::Bool.bit_width(), 1);
        assert_eq!(TypeDesc::Int(32).bit_width(), 32);
        assert_eq!(TypeDesc::Uint(64).bit_width(), 64);
        // Pointer-sized types should be 32 or 64 on most platforms
        let ptr_width = TypeDesc::Ptr.bit_width();
        assert!(ptr_width == 32 || ptr_width == 64);
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
}
