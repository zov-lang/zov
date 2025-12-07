//! Backend-agnostic code generation traits for ZIR.

pub mod testing;

use std::any::Any;
use std::borrow::Cow;
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;

use thiserror::Error;
use zir::mir::{Body, Span};
use zir::ty::{IntWidth, TyKind};

/// Codegen errors.
#[derive(Debug, Error)]
pub enum Error {
    #[error("layout error for `{ty}`: {message}")]
    Layout { ty: TyData, message: &'static str },

    #[error("type not supported: `{0}`")]
    TypeNotSupported(TyData),

    #[error("internal: {0}")]
    Internal(&'static str),

    #[error("at {span:?}: {message}")]
    Compile { span: Span, message: &'static str },

    #[error("unsupported: {0}")]
    Unsupported(&'static str),

    #[error("module: {0}")]
    Module(String),
}

/// Type data for error reporting - captures essential type information.
#[derive(Debug, Clone)]
pub enum TyData {
    Bool,
    Int(IntWidth),
    Uint(IntWidth),
    Ptr,
    Ref,
    Tuple(usize),
    FnDef,
    Never,
    Unit,
}

impl TyData {
    pub fn from_kind(kind: &TyKind<'_>) -> Self {
        match kind {
            TyKind::Bool => TyData::Bool,
            TyKind::Int(w) => TyData::Int(*w),
            TyKind::Uint(w) => TyData::Uint(*w),
            TyKind::Ptr(..) => TyData::Ptr,
            TyKind::Ref(..) => TyData::Ref,
            TyKind::Tuple(elems) => TyData::Tuple(elems.len()),
            TyKind::FnDef(_) => TyData::FnDef,
            TyKind::Never => TyData::Never,
            TyKind::Unit => TyData::Unit,
        }
    }
}

impl std::fmt::Display for TyData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyData::Bool => write!(f, "bool"),
            TyData::Int(w) => write!(f, "i{}", w.bits()),
            TyData::Uint(w) => write!(f, "u{}", w.bits()),
            TyData::Ptr => write!(f, "*_"),
            TyData::Ref => write!(f, "&_"),
            TyData::Tuple(n) => write!(f, "({} elems)", n),
            TyData::FnDef => write!(f, "fn"),
            TyData::Never => write!(f, "!"),
            TyData::Unit => write!(f, "()"),
        }
    }
}

impl Error {
    pub fn layout(ty: TyData, message: &'static str) -> Self {
        Error::Layout { ty, message }
    }

    pub fn type_not_supported(ty: TyData) -> Self {
        Error::TypeNotSupported(ty)
    }

    pub fn compile(span: Span, message: &'static str) -> Self {
        Error::Compile { span, message }
    }

    pub fn module(message: impl Into<String>) -> Self {
        Error::Module(message.into())
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
pub struct Target {
    pub pointer_width: u32,
    pub triple: Cow<'static, str>,
    pub arch: Cow<'static, str>,
    pub options: TargetOptions,
}

impl Target {
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

#[derive(Clone, Debug, Default)]
pub struct TargetOptions {
    pub cpu: Option<Cow<'static, str>>,
    pub features: Vec<Cow<'static, str>>,
    pub relocation_model: RelocModel,
    pub is_like_windows: bool,
    pub is_like_macos: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RelocModel {
    Static,
    #[default]
    Pic,
    Pie,
    DynamicNoPic,
}

#[derive(Clone, Debug)]
pub struct Session {
    pub target: Target,
}

impl Session {
    pub fn new(target: Target) -> Self {
        Self { target }
    }

    pub fn from_triple(triple: &str) -> Self {
        Self { target: Target::from_triple(triple) }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CodegenConfig {
    pub optimize: bool,
    pub debug_info: bool,
}

#[derive(Clone, Debug)]
pub struct TargetConfig {
    pub target_features: Vec<Cow<'static, str>>,
    pub unstable_target_features: Vec<Cow<'static, str>>,
    pub has_reliable_f16: bool,
    pub has_reliable_f16_math: bool,
    pub has_reliable_f128: bool,
    pub has_reliable_f128_math: bool,
}

#[derive(Clone, Debug, Default)]
pub struct OutputFilenames {
    pub out_dir: PathBuf,
    pub crate_name: String,
    pub outputs: Vec<OutputType>,
}

impl OutputFilenames {
    pub fn new(out_dir: PathBuf, crate_name: &str) -> Self {
        Self { out_dir, crate_name: crate_name.to_string(), outputs: vec![OutputType::Object] }
    }

    pub fn path_for(&self, output_type: OutputType) -> PathBuf {
        let ext = output_type.extension();
        self.out_dir.join(format!("{}.{}", self.crate_name, ext))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutputType {
    Object,
    Assembly,
    LlvmIr,
    Bitcode,
    Exe,
    StaticLib,
    DynamicLib,
}

impl OutputType {
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

#[derive(Debug)]
pub struct CompiledModule {
    pub name: String,
    pub object_path: Option<PathBuf>,
    pub object_code: Option<Vec<u8>>,
    pub assembly_path: Option<PathBuf>,
    pub ir_path: Option<PathBuf>,
    pub ir_text: Option<String>,
}

impl CompiledModule {
    pub fn new(name: String) -> Self {
        Self {
            name,
            object_path: None,
            object_code: None,
            assembly_path: None,
            ir_path: None,
            ir_text: None,
        }
    }

    pub fn with_ir_text(name: String, ir_text: String) -> Self {
        Self {
            name,
            object_path: None,
            object_code: None,
            assembly_path: None,
            ir_path: None,
            ir_text: Some(ir_text),
        }
    }
}

#[derive(Debug, Default)]
pub struct CodegenResults {
    pub modules: Vec<CompiledModule>,
    pub linker_args: Vec<String>,
}

pub type OngoingCodegen = Box<dyn Any + Send>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WorkProductId(pub String);

#[derive(Clone, Debug)]
pub struct WorkProduct {
    pub path: PathBuf,
    pub hash: u64,
}

#[derive(Debug)]
pub struct CodegenUnit<'a> {
    pub name: String,
    pub bodies: Vec<(&'a Body<'a>, FunctionSignature)>,
}

impl<'a> CodegenUnit<'a> {
    pub fn new(name: &str) -> Self {
        Self { name: name.to_string(), bodies: Vec::new() }
    }

    pub fn add_function(&mut self, body: &'a Body<'a>, signature: FunctionSignature) {
        self.bodies.push((body, signature));
    }
}

#[derive(Clone, Debug, Default)]
pub struct FunctionSignature {
    pub params: Vec<TypeDesc>,
    pub returns: Vec<TypeDesc>,
}

#[derive(Clone, Debug)]
pub enum TypeDesc {
    Bool,
    Int(u32),
    Uint(u32),
    Isize,
    Usize,
    Ptr,
}

impl TypeDesc {
    pub fn bit_width(&self, pointer_width: u32) -> u32 {
        match self {
            TypeDesc::Bool => 1,
            TypeDesc::Int(bits) | TypeDesc::Uint(bits) => *bits,
            TypeDesc::Isize | TypeDesc::Usize | TypeDesc::Ptr => pointer_width,
        }
    }
}

impl FunctionSignature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_param(mut self, ty: TypeDesc) -> Self {
        self.params.push(ty);
        self
    }

    pub fn with_return(mut self, ty: TypeDesc) -> Self {
        self.returns.push(ty);
        self
    }
}

/// Code generation backend trait.
pub trait CodegenBackend: Any {
    fn name(&self) -> &'static str;
    fn init(&self, _sess: &Session) {}

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

    fn print_passes(&self) {}
    fn print_version(&self) {}
    fn print(&self, _out: &mut dyn Write) {}

    fn codegen_unit<'a>(&mut self, unit: CodegenUnit<'a>) -> Result<OngoingCodegen>;

    fn join_codegen(
        &self,
        ongoing: OngoingCodegen,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> (CodegenResults, HashMap<WorkProductId, WorkProduct>);

    fn link(&self, sess: &Session, results: CodegenResults, outputs: &OutputFilenames);
    fn config(&self) -> &CodegenConfig;

    fn compile_function<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> Result<()>;
    fn compile_to_ir<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: FunctionSignature,
    ) -> Result<String>;
    fn finalize(self: Box<Self>) -> CodegenResults;
}

/// Factory function type for creating backends.
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
