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
//! # Error Handling
//!
//! This crate provides a user-friendly [`Error`] type for codegen errors.
//! Errors are designed to produce clear, actionable reports useful for
//! debugging ICE (Internal Compiler Errors) and during development.
//!
//! # Testing
//!
//! The [`testing`] module provides utilities for writing backend-agnostic
//! tests that can verify any implementation of [`CodegenBackend`].
//!
//! # Example
//!
//! ```ignore
//! use zir_codegen::{CodegenBackend, CodegenConfig, Session, Target, CodegenResult};
//!
//! let mut backend = SomeCraneliftBackend::new(CodegenConfig::default())?;
//! let session = Session::host();
//! backend.init(&session);
//! let result = backend.codegen_unit(unit)?;
//! let (results, _) = backend.join_codegen(ongoing, &session, &outputs)?;
//! backend.link(&session, results, &outputs)?;
//! ```

pub mod testing;

use std::any::Any;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::path::PathBuf;

use zir::mir::Body;

// ============================================================================
// Error Handling
// ============================================================================

/// Result type alias for codegen operations.
///
/// The error is boxed to keep the result type small (clippy::result_large_err).
pub type CodegenResult<T> = Result<T, Box<Error>>;

/// Code generation error with detailed context for debugging.
///
/// This error type is designed to produce clear, actionable reports
/// that are useful for:
/// - Debugging Internal Compiler Errors (ICE)
/// - Development and testing of codegen backends
/// - User-facing error messages when compilation fails
///
/// # Example
///
/// ```ignore
/// use zir_codegen::{Error, ErrorKind};
///
/// let error = Error::new(ErrorKind::UnsupportedType)
///     .with_message("i256 is not supported by the Cranelift backend")
///     .with_context("function", "my_function")
///     .with_help("consider using i128 or smaller integer types");
/// ```
#[derive(Debug, Clone)]
pub struct Error {
    /// The kind of error.
    pub kind: ErrorKind,
    /// Human-readable error message.
    pub message: Cow<'static, str>,
    /// Additional context about where the error occurred.
    pub context: Vec<(Cow<'static, str>, Cow<'static, str>)>,
    /// Optional help text suggesting how to fix the error.
    pub help: Option<Cow<'static, str>>,
    /// Optional note with additional information.
    pub note: Option<Cow<'static, str>>,
    /// The backend that produced the error (if known).
    pub backend: Option<Cow<'static, str>>,
}

impl Error {
    /// Creates a new error with the given kind.
    pub fn new(kind: ErrorKind) -> Self {
        Self {
            kind,
            message: kind.default_message(),
            context: Vec::new(),
            help: None,
            note: None,
            backend: None,
        }
    }

    /// Creates a new error with a custom message.
    pub fn with_message<S: Into<Cow<'static, str>>>(mut self, message: S) -> Self {
        self.message = message.into();
        self
    }

    /// Adds context about where the error occurred.
    pub fn with_context<K, V>(mut self, key: K, value: V) -> Self
    where
        K: Into<Cow<'static, str>>,
        V: Into<Cow<'static, str>>,
    {
        self.context.push((key.into(), value.into()));
        self
    }

    /// Adds help text suggesting how to fix the error.
    pub fn with_help<S: Into<Cow<'static, str>>>(mut self, help: S) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Adds a note with additional information.
    pub fn with_note<S: Into<Cow<'static, str>>>(mut self, note: S) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Sets the backend that produced the error.
    pub fn with_backend<S: Into<Cow<'static, str>>>(mut self, backend: S) -> Self {
        self.backend = Some(backend.into());
        self
    }

    /// Creates an error for an unsupported feature.
    pub fn unsupported<S: Into<Cow<'static, str>>>(feature: S) -> Self {
        Self::new(ErrorKind::UnsupportedFeature).with_message(feature)
    }

    /// Creates an error for an unsupported type.
    pub fn unsupported_type<S: Into<Cow<'static, str>>>(ty: S) -> Self {
        Self::new(ErrorKind::UnsupportedType).with_context("type", ty)
    }

    /// Creates an error for an unsupported operation.
    pub fn unsupported_op<S: Into<Cow<'static, str>>>(op: S) -> Self {
        Self::new(ErrorKind::UnsupportedOperation).with_context("operation", op)
    }

    /// Creates an internal compiler error (ICE).
    pub fn ice<S: Into<Cow<'static, str>>>(message: S) -> Self {
        Self::new(ErrorKind::InternalError).with_message(message)
    }

    /// Creates a backend initialization error.
    pub fn init_failed<S: Into<Cow<'static, str>>>(message: S) -> Self {
        Self::new(ErrorKind::InitializationFailed).with_message(message)
    }

    /// Creates a linking error.
    pub fn link_failed<S: Into<Cow<'static, str>>>(message: S) -> Self {
        Self::new(ErrorKind::LinkingFailed).with_message(message)
    }

    /// Formats the error for pretty printing.
    ///
    /// Returns a multi-line string with all error details formatted
    /// for easy reading in terminal output or logs.
    pub fn pretty_print(&self) -> String {
        let mut output = String::new();

        // Error header
        output.push_str(&format!("error[{}]: {}\n", self.kind.code(), self.message));

        // Backend info
        if let Some(ref backend) = self.backend {
            output.push_str(&format!("  --> backend: {}\n", backend));
        }

        // Context
        if !self.context.is_empty() {
            output.push_str("  |\n");
            for (key, value) in &self.context {
                output.push_str(&format!("  | {}: {}\n", key, value));
            }
        }

        // Note
        if let Some(ref note) = self.note {
            output.push_str(&format!("  = note: {}\n", note));
        }

        // Help
        if let Some(ref help) = self.help {
            output.push_str(&format!("  = help: {}\n", help));
        }

        output
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}

/// The kind of codegen error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    /// An unsupported feature was requested.
    UnsupportedFeature,
    /// An unsupported type was encountered.
    UnsupportedType,
    /// An unsupported operation was encountered.
    UnsupportedOperation,
    /// Backend initialization failed.
    InitializationFailed,
    /// Function declaration failed.
    DeclarationFailed,
    /// Function definition failed.
    DefinitionFailed,
    /// Module finalization failed.
    FinalizationFailed,
    /// Linking failed.
    LinkingFailed,
    /// Invalid MIR was provided.
    InvalidMir,
    /// Internal compiler error (ICE).
    InternalError,
    /// I/O error during code generation.
    IoError,
}

impl ErrorKind {
    /// Returns the error code for this kind.
    pub fn code(self) -> &'static str {
        match self {
            ErrorKind::UnsupportedFeature => "E0001",
            ErrorKind::UnsupportedType => "E0002",
            ErrorKind::UnsupportedOperation => "E0003",
            ErrorKind::InitializationFailed => "E0010",
            ErrorKind::DeclarationFailed => "E0011",
            ErrorKind::DefinitionFailed => "E0012",
            ErrorKind::FinalizationFailed => "E0013",
            ErrorKind::LinkingFailed => "E0014",
            ErrorKind::InvalidMir => "E0020",
            ErrorKind::InternalError => "E9999",
            ErrorKind::IoError => "E0030",
        }
    }

    /// Returns the default message for this error kind.
    pub fn default_message(self) -> Cow<'static, str> {
        match self {
            ErrorKind::UnsupportedFeature => "unsupported feature".into(),
            ErrorKind::UnsupportedType => "unsupported type".into(),
            ErrorKind::UnsupportedOperation => "unsupported operation".into(),
            ErrorKind::InitializationFailed => "backend initialization failed".into(),
            ErrorKind::DeclarationFailed => "function declaration failed".into(),
            ErrorKind::DefinitionFailed => "function definition failed".into(),
            ErrorKind::FinalizationFailed => "module finalization failed".into(),
            ErrorKind::LinkingFailed => "linking failed".into(),
            ErrorKind::InvalidMir => "invalid MIR".into(),
            ErrorKind::InternalError => "internal compiler error".into(),
            ErrorKind::IoError => "I/O error during code generation".into(),
        }
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.default_message())
    }
}

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
    /// Creates a target for the current host.
    pub fn host() -> Self {
        let triple = target_lexicon::HOST;
        Self {
            pointer_width: std::mem::size_of::<*const ()>() as u32 * 8,
            triple: Cow::Owned(triple.to_string()),
            arch: Cow::Owned(triple.architecture.to_string()),
            options: TargetOptions::default(),
        }
    }

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

impl Default for Target {
    fn default() -> Self {
        Self::host()
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
    /// The host we're compiling on.
    pub host: Target,
}

impl Session {
    /// Creates a session for the host target.
    pub fn host() -> Self {
        let target = Target::host();
        Self { target: target.clone(), host: target }
    }

    /// Creates a session with a specific target.
    pub fn with_target(target: Target) -> Self {
        Self { target, host: Target::host() }
    }

    /// Creates a session from a target triple string.
    pub fn from_triple(triple: &str) -> Self {
        Self { target: Target::from_triple(triple), host: Target::host() }
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::host()
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
#[derive(Clone, Debug, Default)]
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

impl TargetConfig {
    /// Creates a default target config.
    ///
    /// Uses `true` as default for float support so backends need to
    /// explicitly acknowledge when they don't support the float types.
    pub fn new() -> Self {
        Self {
            target_features: Vec::new(),
            unstable_target_features: Vec::new(),
            has_reliable_f16: true,
            has_reliable_f16_math: true,
            has_reliable_f128: true,
            has_reliable_f128_math: true,
        }
    }
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
/// # Error Handling
///
/// Methods return [`CodegenResult<T>`] which wraps results with a
/// user-friendly [`Error`] type. This allows callers to handle errors
/// gracefully and provides detailed context for debugging ICE and
/// development issues.
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
///     fn init(&self, sess: &Session) -> CodegenResult<()> {
///         // Initialize backend with session configuration
///         Ok(())
///     }
///
///     fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> CodegenResult<OngoingCodegen> {
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
///     fn link(&self, sess: &Session, results: CodegenResults, outputs: &OutputFilenames)
///         -> CodegenResult<()> {
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
    ///
    /// # Errors
    ///
    /// Returns an error if initialization fails.
    fn init(&self, _sess: &Session) -> CodegenResult<()> {
        Ok(())
    }

    /// Returns target-specific configuration.
    ///
    /// This allows backends to report what features they support for
    /// the current target, enabling frontend decisions about code generation.
    ///
    /// Note: The default returns `has_reliable_f16/f128 = true` so that
    /// backends must explicitly acknowledge when they don't support these
    /// types, rather than silently skipping tests.
    fn target_config(&self, _sess: &Session) -> TargetConfig {
        TargetConfig::new()
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
    fn print(&self, _out: &mut dyn Write) {}

    /// Compiles a single codegen unit.
    ///
    /// This method takes a collection of MIR bodies and compiles them
    /// into backend-specific IR. The result is an opaque `OngoingCodegen`
    /// that can later be passed to `join_codegen()`.
    ///
    /// For simple use cases, this can directly return the compiled results.
    /// For parallel compilation, this returns a handle that will be joined later.
    ///
    /// # Errors
    ///
    /// Returns an error if code generation fails.
    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> CodegenResult<OngoingCodegen>;

    /// Joins ongoing codegen and produces final results.
    ///
    /// This method is called after all codegen units have been compiled.
    /// It combines the results and produces the final `CodegenResults`
    /// along with any work products for incremental compilation.
    ///
    /// # Errors
    ///
    /// Returns an error if the ongoing codegen type is invalid or joining fails.
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
    ///
    /// # Errors
    ///
    /// Returns an error if linking fails.
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
    ///
    /// # Errors
    ///
    /// Returns an error if compilation fails.
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
    ///
    /// # Errors
    ///
    /// Returns an error if compilation fails.
    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> CodegenResult<IrOutput>;

    /// Finalizes the compilation and returns the results.
    ///
    /// This is a convenience method that combines `join_codegen()` with
    /// default session and output settings.
    ///
    /// # Errors
    ///
    /// Returns an error if finalization fails.
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
    fn test_ir_output_equality() {
        let text1 = IrOutput::Text("function f() {}".into());
        let text2 = IrOutput::Text("function f() {}".into());
        let text3 = IrOutput::Text("function g() {}".into());

        assert_eq!(text1, text2);
        assert_ne!(text1, text3);
    }

    #[test]
    fn test_target_host() {
        let target = Target::host();
        assert!(target.pointer_width == 32 || target.pointer_width == 64);
        assert!(!target.triple.is_empty());
        assert!(!target.arch.is_empty());
    }

    #[test]
    fn test_target_from_triple() {
        let target = Target::from_triple("x86_64-unknown-linux-gnu");
        assert_eq!(target.pointer_width, 64);
        assert_eq!(target.triple.as_ref(), "x86_64-unknown-linux-gnu");
        assert_eq!(target.arch.as_ref(), "x86_64");
    }

    #[test]
    fn test_session_host() {
        let session = Session::host();
        assert!(session.target.pointer_width == 32 || session.target.pointer_width == 64);
        assert!(!session.target.triple.is_empty());
        assert!(!session.host.triple.is_empty());
    }

    #[test]
    fn test_session_from_triple() {
        let session = Session::from_triple("aarch64-unknown-linux-gnu");
        assert_eq!(session.target.triple.as_ref(), "aarch64-unknown-linux-gnu");
        // Host should still be the actual host
        assert!(!session.host.triple.is_empty());
    }

    #[test]
    fn test_target_config_new() {
        let config = TargetConfig::new();
        // Defaults to true for float support
        assert!(config.has_reliable_f16);
        assert!(config.has_reliable_f128);
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

    #[test]
    fn test_reloc_model_default() {
        let model = RelocModel::default();
        assert_eq!(model, RelocModel::Pic);
    }

    #[test]
    fn test_error_creation() {
        let error = Error::new(ErrorKind::UnsupportedType);
        assert_eq!(error.kind, ErrorKind::UnsupportedType);
        assert_eq!(error.message.as_ref(), "unsupported type");
    }

    #[test]
    fn test_error_builder() {
        let error = Error::new(ErrorKind::UnsupportedFeature)
            .with_message("f16 not supported")
            .with_context("function", "compute_sum")
            .with_backend("cranelift")
            .with_help("use f32 instead")
            .with_note("f16 support is experimental");

        assert_eq!(error.message.as_ref(), "f16 not supported");
        assert_eq!(error.context.len(), 1);
        assert_eq!(error.context[0].0.as_ref(), "function");
        assert_eq!(error.context[0].1.as_ref(), "compute_sum");
        assert_eq!(error.backend.as_ref().unwrap().as_ref(), "cranelift");
        assert_eq!(error.help.as_ref().unwrap().as_ref(), "use f32 instead");
        assert_eq!(error.note.as_ref().unwrap().as_ref(), "f16 support is experimental");
    }

    #[test]
    fn test_error_convenience_constructors() {
        let e1 = Error::unsupported("AVX-512");
        assert_eq!(e1.kind, ErrorKind::UnsupportedFeature);
        assert_eq!(e1.message.as_ref(), "AVX-512");

        let e2 = Error::unsupported_type("i256");
        assert_eq!(e2.kind, ErrorKind::UnsupportedType);
        assert_eq!(e2.context[0].1.as_ref(), "i256");

        let e3 = Error::ice("internal assertion failed");
        assert_eq!(e3.kind, ErrorKind::InternalError);
    }

    #[test]
    fn test_error_kind_codes() {
        assert_eq!(ErrorKind::UnsupportedFeature.code(), "E0001");
        assert_eq!(ErrorKind::InternalError.code(), "E9999");
    }

    #[test]
    fn test_error_pretty_print() {
        let error = Error::new(ErrorKind::UnsupportedType)
            .with_message("i256 is not supported")
            .with_backend("cranelift")
            .with_context("function", "test_fn")
            .with_note("only i8-i128 are supported")
            .with_help("use i128 instead");

        let pretty = error.pretty_print();
        assert!(pretty.contains("error[E0002]"));
        assert!(pretty.contains("i256 is not supported"));
        assert!(pretty.contains("backend: cranelift"));
        assert!(pretty.contains("function: test_fn"));
        assert!(pretty.contains("note:"));
        assert!(pretty.contains("help:"));
    }

    #[test]
    fn test_error_display() {
        let error = Error::new(ErrorKind::UnsupportedType).with_message("test error");
        assert_eq!(format!("{}", error), "test error");
    }

    #[test]
    fn test_codegen_result_type() {
        fn returns_ok() -> CodegenResult<i32> {
            Ok(42)
        }
        fn returns_err() -> CodegenResult<i32> {
            Err(Box::new(Error::ice("test")))
        }

        assert_eq!(returns_ok().unwrap(), 42);
        assert!(returns_err().is_err());
    }
}
