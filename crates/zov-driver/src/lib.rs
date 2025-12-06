//! ZoV Compiler Driver
//!
//! This crate provides the glue code that connects MIR to Codegen backends.
//! It implements the full compilation pipeline:
//!
//! Source -> Parsing -> Type Checking -> MIR -> Codegen -> Machine Code
//!
//! Currently supports:
//! - Cranelift JIT backend for testing
//! - AOT compilation to object files

use cranelift::prelude::*;
use cranelift_codegen::ir::types;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use zir::mir::Body;
use zir::{CompilerDatabase, SourceFile};
use zir_codegen_cranelift::{CodegenConfig, CodegenContext, CodegenResult, create_jit_module};

/// The compiler driver that coordinates compilation.
pub struct Driver {
    /// The Salsa database for incremental compilation.
    pub db: CompilerDatabase,
    /// Configuration for code generation.
    pub config: CodegenConfig,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new()
    }
}

impl Driver {
    /// Creates a new compiler driver.
    pub fn new() -> Self {
        Self { db: CompilerDatabase::new(), config: CodegenConfig::default() }
    }

    /// Creates a driver with custom codegen configuration.
    pub fn with_config(config: CodegenConfig) -> Self {
        Self { db: CompilerDatabase::new(), config }
    }

    /// Adds a source file to the compilation.
    pub fn add_source(&self, path: &str, text: &str) -> SourceFile {
        SourceFile::new(&self.db, text.to_string(), path.to_string())
    }

    /// Compiles and JIT-executes a function that takes no arguments and returns an i64.
    ///
    /// This is primarily for testing the compilation pipeline.
    pub fn jit_compile_and_run(&self, body: &Body<'_>, name: &str) -> CodegenResult<i64> {
        let module = create_jit_module()?;
        let mut ctx = CodegenContext::new(module);

        // Build signature for () -> i64
        let mut sig = ctx.module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        // Declare and define the function
        let func_id = ctx.declare_function(name, sig.clone())?;
        ctx.define_function(func_id, body, sig)?;

        // Finalize and get function pointer
        ctx.module.finalize_definitions().map_err(|e| {
            zir_codegen_cranelift::CodegenError::Module(format!("finalize error: {}", e))
        })?;

        let code_ptr = ctx.module.get_finalized_function(func_id);

        // Safety: We trust our codegen to produce valid code matching the signature
        let func: fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        Ok(func())
    }

    /// Compiles a function to native code using the JIT module.
    ///
    /// Returns the JIT module with the compiled function.
    pub fn jit_compile(
        &self,
        body: &Body<'_>,
        name: &str,
        sig: Signature,
    ) -> CodegenResult<CompiledFunction> {
        let module = create_jit_module()?;
        let mut ctx = CodegenContext::new(module);

        let func_id = ctx.declare_function(name, sig.clone())?;
        ctx.define_function(func_id, body, sig)?;

        ctx.module.finalize_definitions().map_err(|e| {
            zir_codegen_cranelift::CodegenError::Module(format!("finalize error: {}", e))
        })?;

        let code_ptr = ctx.module.get_finalized_function(func_id);

        Ok(CompiledFunction { module: ctx.module, code_ptr, name: name.to_string() })
    }
}

/// A compiled function with its JIT module.
///
/// The module must be kept alive as long as the function pointer is used.
pub struct CompiledFunction {
    /// The JIT module containing the compiled code.
    #[allow(dead_code)]
    module: JITModule,
    /// Pointer to the compiled function.
    pub code_ptr: *const u8,
    /// Function name.
    pub name: String,
}

impl CompiledFunction {
    /// Returns the function pointer for a function with signature `() -> i64`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the function was compiled with a compatible signature.
    pub unsafe fn as_fn_void_to_i64(&self) -> fn() -> i64 {
        // Safety: caller guarantees compatible signature
        unsafe { std::mem::transmute(self.code_ptr) }
    }

    /// Returns the function pointer for a function with signature `(i64) -> i64`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the function was compiled with a compatible signature.
    pub unsafe fn as_fn_i64_to_i64(&self) -> fn(i64) -> i64 {
        // Safety: caller guarantees compatible signature
        unsafe { std::mem::transmute(self.code_ptr) }
    }

    /// Returns the function pointer for a function with signature `(i64, i64) -> i64`.
    ///
    /// # Safety
    ///
    /// The caller must ensure the function was compiled with a compatible signature.
    pub unsafe fn as_fn_i64_i64_to_i64(&self) -> fn(i64, i64) -> i64 {
        // Safety: caller guarantees compatible signature
        unsafe { std::mem::transmute(self.code_ptr) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zir::idx::Idx;
    use zir::intern::InternSet;
    use zir::mir::*;
    use zir::ty::*;
    use zir::{Arena, IndexVec};

    /// Helper to create a simple function that returns a constant.
    fn create_const_function<'a>(arena: &'a Arena<'a>, value: i64) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });

        let mut body = Body::new(local_decls, 0);

        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Const(
                    ConstValue::Scalar(ScalarRepr::from_u64(value as u64)),
                    i64_ty,
                )),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb0);

        body
    }

    /// Helper to create an add function: fn add(a: i64, b: i64) -> i64 { a + b }
    fn create_add_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        // _0: return place
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        // _1: first argument (a)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _2: second argument (b)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });

        let mut body = Body::new(local_decls, 2);

        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::from_local(Local::new(1))),
                    Operand::Copy(Place::from_local(Local::new(2))),
                ),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb0);

        body
    }

    /// Helper to create a max function with branching.
    fn create_max_function<'a>(arena: &'a Arena<'a>) -> Body<'a> {
        let types = InternSet::new();
        let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |k| arena.dropless.alloc(k));
        let bool_ty = types.intern(TyKind::Bool, |k| arena.dropless.alloc(k));

        let mut local_decls = IndexVec::new();
        // _0: return place
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: i64_ty });
        // _1: first argument (a)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _2: second argument (b)
        local_decls.push(LocalDecl { mutability: Mutability::Not, ty: i64_ty });
        // _3: comparison result
        local_decls.push(LocalDecl { mutability: Mutability::Mut, ty: bool_ty });

        let mut body = Body::new(local_decls, 2);

        // bb0: _3 = Gt(_1, _2); switchInt(_3) -> [0: bb2, otherwise: bb1]
        let mut bb0 = BasicBlockData::new();
        bb0.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(3)),
                Rvalue::BinaryOp(
                    BinOp::Gt,
                    Operand::Copy(Place::from_local(Local::new(1))),
                    Operand::Copy(Place::from_local(Local::new(2))),
                ),
            ),
        });
        bb0.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(Local::new(3))),
                targets: SwitchTargets::if_else(0, BasicBlock::new(2), BasicBlock::new(1)),
            },
        });
        body.basic_blocks.push(bb0);

        // bb1 (true branch): _0 = copy _1; goto -> bb3
        let mut bb1 = BasicBlockData::new();
        bb1.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Copy(Place::from_local(Local::new(1)))),
            ),
        });
        bb1.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Goto { target: BasicBlock::new(3) },
        });
        body.basic_blocks.push(bb1);

        // bb2 (false branch): _0 = copy _2; goto -> bb3
        let mut bb2 = BasicBlockData::new();
        bb2.statements.push(Statement {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: StatementKind::Assign(
                Place::from_local(Local::new(0)),
                Rvalue::Use(Operand::Copy(Place::from_local(Local::new(2)))),
            ),
        });
        bb2.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Goto { target: BasicBlock::new(3) },
        });
        body.basic_blocks.push(bb2);

        // bb3 (join point): return
        let mut bb3 = BasicBlockData::new();
        bb3.terminator = Some(Terminator {
            source_info: SourceInfo { span: Span::DUMMY },
            kind: TerminatorKind::Return,
        });
        body.basic_blocks.push(bb3);

        body
    }

    #[test]
    fn test_driver_creation() {
        let driver = Driver::new();
        assert!(!driver.config.debug_info);
        assert!(driver.config.optimize);
    }

    #[test]
    fn test_add_source() {
        let driver = Driver::new();
        let file = driver.add_source("test.zov", "fn main() {}");
        assert_eq!(file.text(&driver.db), "fn main() {}");
        assert_eq!(file.path(&driver.db), "test.zov");
    }

    #[test]
    fn test_jit_const_42() {
        let driver = Driver::new();
        let arena = Arena::new();
        let body = create_const_function(&arena, 42);

        let result = driver.jit_compile_and_run(&body, "const_42").unwrap();
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_const_negative() {
        let driver = Driver::new();
        let arena = Arena::new();
        // Use a negative number represented as unsigned
        let body = create_const_function(&arena, -123);

        let result = driver.jit_compile_and_run(&body, "const_neg").unwrap();
        assert_eq!(result, -123);
    }

    #[test]
    fn test_jit_add_function() {
        let driver = Driver::new();
        let arena = Arena::new();
        let body = create_add_function(&arena);

        // Create signature: (i64, i64) -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let compiled = driver.jit_compile(&body, "add", sig).unwrap();

        // Call the function
        // Safety: we know the signature matches
        let add_fn = unsafe { compiled.as_fn_i64_i64_to_i64() };
        assert_eq!(add_fn(3, 5), 8);
        assert_eq!(add_fn(10, 20), 30);
        assert_eq!(add_fn(-5, 10), 5);
    }

    #[test]
    fn test_jit_max_function() {
        let driver = Driver::new();
        let arena = Arena::new();
        let body = create_max_function(&arena);

        // Create signature: (i64, i64) -> i64
        let module = create_jit_module().unwrap();
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let compiled = driver.jit_compile(&body, "max", sig).unwrap();

        // Call the function
        // Safety: we know the signature matches
        let max_fn = unsafe { compiled.as_fn_i64_i64_to_i64() };
        assert_eq!(max_fn(3, 5), 5);
        assert_eq!(max_fn(10, 5), 10);
        assert_eq!(max_fn(-5, -10), -5);
        assert_eq!(max_fn(42, 42), 42);
    }
}
