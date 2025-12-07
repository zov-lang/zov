//! Codegen context for Cranelift.

#![allow(clippy::result_large_err)]

use cranelift::prelude::*;
use cranelift_codegen::Context;
use cranelift_codegen::ir::types;
use cranelift_frontend::{FunctionBuilder, Switch};
use cranelift_module::{FuncId, Linkage, Module};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use zir::idx::Idx;
use zir::mir::{
    BasicBlock, BinOp, Body, ConstValue, DefId, Local, Operand, Place, Rvalue, START_BLOCK,
    SourceInfo, StatementKind, TerminatorKind, UnOp,
};
use zir::ty::{Ty, TyKind};
use zir_codegen::{Error, Result, TyData};

use crate::analyze::{SsaKind, analyze_ssa};
use crate::clif_type;
use crate::place::CPlace;
use crate::value::{CValue, Pointer};

pub struct CodegenContext<M: Module> {
    pub module: M,
    pub ctx: Context,
    pub ptr_type: types::Type,
    pub functions: FxHashMap<DefId, FuncId>,
}

impl<M: Module> CodegenContext<M> {
    pub fn new(module: M) -> Self {
        let ptr_type = module.isa().pointer_type();
        Self { module, ctx: Context::new(), ptr_type, functions: FxHashMap::default() }
    }

    pub fn declare_function(&mut self, name: &str, signature: Signature) -> Result<FuncId> {
        self.module
            .declare_function(name, Linkage::Export, &signature)
            .map_err(|e| Error::module(e.to_string()))
    }

    pub fn define_function<'zir>(
        &mut self,
        func_id: FuncId,
        body: &Body<'zir>,
        signature: Signature,
    ) -> Result<()> {
        self.ctx.func.signature = signature;

        let mut builder_ctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut builder_ctx);

        let mut fx = FunctionCodegen::new(self.ptr_type, body, builder);
        fx.codegen()?;
        fx.builder.finalize();

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| Error::module(e.to_string()))?;

        self.ctx.clear();
        Ok(())
    }

    pub fn compile_to_clif<'zir>(
        &mut self,
        body: &Body<'zir>,
        signature: Signature,
    ) -> Result<String> {
        self.ctx.func.signature = signature;

        let mut builder_ctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut builder_ctx);

        let mut fx = FunctionCodegen::new(self.ptr_type, body, builder);
        fx.codegen()?;
        fx.builder.finalize();

        let clif_output = self.ctx.func.display().to_string();
        self.ctx.clear();
        Ok(clif_output)
    }
}

pub struct FunctionCodegen<'a, 'zir> {
    pub builder: FunctionBuilder<'a>,
    ptr_type: types::Type,
    body: &'a Body<'zir>,
    block_map: IndexVec<BasicBlock, Block>,
    locals: IndexVec<Local, CPlace<'zir>>,
    ssa_kinds: IndexVec<Local, SsaKind>,
    current_source_info: SourceInfo,
}

impl<'a, 'zir> FunctionCodegen<'a, 'zir> {
    pub fn new(ptr_type: types::Type, body: &'a Body<'zir>, builder: FunctionBuilder<'a>) -> Self {
        let ssa_kinds = analyze_ssa(body);
        Self {
            builder,
            ptr_type,
            body,
            block_map: IndexVec::new(),
            locals: IndexVec::new(),
            ssa_kinds,
            current_source_info: SourceInfo::default(),
        }
    }

    fn error(&self, message: &'static str) -> Error {
        Error::compile(self.current_source_info.span, message)
    }

    fn type_error(&self, ty: Ty<'zir>) -> Error {
        Error::type_not_supported(TyData::from_kind(&ty))
    }

    pub fn codegen(&mut self) -> Result<()> {
        // Create blocks
        for _ in self.body.basic_blocks.iter() {
            let block = self.builder.create_block();
            self.block_map.push(block);
        }

        // Set up entry block with parameters
        let entry_block = self.block_map[START_BLOCK];
        self.builder.switch_to_block(entry_block);

        // Add block parameters for function arguments
        let arg_count = self.body.arg_count;
        for i in 0..arg_count {
            let local_idx = i + 1; // Arguments start at local 1
            if let Some(clif_ty) =
                clif_type(self.body.local_decls[Local::new(local_idx)].ty, self.ptr_type)
            {
                self.builder.append_block_param(entry_block, clif_ty);
            }
        }

        // Set up locals
        self.setup_locals();

        // Store function arguments into their places
        for i in 0..arg_count {
            let local_idx = i + 1;
            let local = Local::new(local_idx);
            if let Some(_clif_ty) = clif_type(self.body.local_decls[local].ty, self.ptr_type) {
                let param_val = self.builder.block_params(entry_block)[i];
                let place = self.locals[local];
                place.store(
                    &mut self.builder,
                    CValue::by_val(param_val, place.ty()),
                    self.ptr_type,
                );
            }
        }

        // Codegen blocks
        for (bb, bb_data) in self.body.basic_blocks.iter_enumerated() {
            let block = self.block_map[bb];

            // Only switch if not the entry block (already switched)
            if bb != START_BLOCK {
                self.builder.switch_to_block(block);
            }

            for stmt in &bb_data.statements {
                self.current_source_info = stmt.source_info;
                self.codegen_statement(stmt)?;
            }

            if let Some(ref terminator) = bb_data.terminator {
                self.current_source_info = terminator.source_info;
                self.codegen_terminator(terminator)?;
            }
        }

        // Seal all blocks at the end
        self.builder.seal_all_blocks();
        Ok(())
    }

    fn setup_locals(&mut self) {
        for (local, decl) in self.body.local_decls.iter_enumerated() {
            let place = if self.ssa_kinds[local] == SsaKind::MaybeSsa {
                if let Some(clif_ty) = clif_type(decl.ty, self.ptr_type) {
                    let var = self.builder.declare_var(clif_ty);
                    CPlace::var(var, decl.ty)
                } else {
                    // ZST or unsupported type, create dummy
                    let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        0,
                        0,
                    ));
                    CPlace::addr(Pointer::stack_slot(slot), decl.ty)
                }
            } else {
                // Need stack slot for address-taken locals
                let size = Self::type_size(decl.ty);
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
                CPlace::addr(Pointer::stack_slot(slot), decl.ty)
            };
            self.locals.push(place);
        }
    }

    fn type_size(ty: Ty<'zir>) -> u32 {
        match &*ty {
            TyKind::Bool => 1,
            TyKind::Int(width) | TyKind::Uint(width) => width.bytes(8),
            TyKind::Ptr(..) | TyKind::Ref(..) => 8,
            TyKind::Unit | TyKind::Never => 0,
            TyKind::Tuple(elems) => elems.iter().map(|t| Self::type_size(*t)).sum(),
            TyKind::FnDef(_) => 0,
        }
    }

    fn codegen_statement(&mut self, stmt: &zir::mir::Statement<'zir>) -> Result<()> {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let value = self.codegen_rvalue(rvalue)?;
                let dest = self.codegen_place(place)?;
                dest.store(&mut self.builder, value, self.ptr_type);
            }
            StatementKind::Nop => {}
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
        }
        Ok(())
    }

    fn codegen_rvalue(&mut self, rvalue: &Rvalue<'zir>) -> Result<CValue<'zir>> {
        match rvalue {
            Rvalue::Use(operand) => self.codegen_operand(operand),
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let lhs_val = self.codegen_operand(lhs)?;
                let rhs_val = self.codegen_operand(rhs)?;

                let lhs_loaded = lhs_val
                    .load(&mut self.builder, self.ptr_type)
                    .ok_or_else(|| self.error("binop on ZST"))?;
                let rhs_loaded = rhs_val
                    .load(&mut self.builder, self.ptr_type)
                    .ok_or_else(|| self.error("binop on ZST"))?;

                let result = self.codegen_binop(*op, lhs_loaded, rhs_loaded);
                Ok(CValue::by_val(result, lhs_val.ty()))
            }
            Rvalue::UnaryOp(op, operand) => {
                let val = self.codegen_operand(operand)?;
                let loaded = val
                    .load(&mut self.builder, self.ptr_type)
                    .ok_or_else(|| self.error("unop on ZST"))?;

                let result = match op {
                    UnOp::Not => self.builder.ins().bnot(loaded),
                    UnOp::Neg => self.builder.ins().ineg(loaded),
                };
                Ok(CValue::by_val(result, val.ty()))
            }
            _ => Err(Error::Unsupported("unsupported rvalue")),
        }
    }

    fn codegen_binop(&mut self, op: BinOp, lhs: Value, rhs: Value) -> Value {
        match op {
            BinOp::Add => self.builder.ins().iadd(lhs, rhs),
            BinOp::Sub => self.builder.ins().isub(lhs, rhs),
            BinOp::Mul => self.builder.ins().imul(lhs, rhs),
            BinOp::Div => self.builder.ins().sdiv(lhs, rhs),
            BinOp::Rem => self.builder.ins().srem(lhs, rhs),
            BinOp::BitXor => self.builder.ins().bxor(lhs, rhs),
            BinOp::BitAnd => self.builder.ins().band(lhs, rhs),
            BinOp::BitOr => self.builder.ins().bor(lhs, rhs),
            BinOp::Shl => self.builder.ins().ishl(lhs, rhs),
            BinOp::Shr => self.builder.ins().sshr(lhs, rhs),
            BinOp::Eq => self.builder.ins().icmp(IntCC::Equal, lhs, rhs),
            BinOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs),
            BinOp::Lt => self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
            BinOp::Le => self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
            BinOp::Gt => self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
            BinOp::Ge => self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs),
        }
    }

    fn codegen_operand(&mut self, operand: &Operand<'zir>) -> Result<CValue<'zir>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let cplace = self.codegen_place(place)?;
                Ok(cplace.load(&mut self.builder, self.ptr_type))
            }
            Operand::Const(const_val, ty) => self.codegen_const(const_val, *ty),
        }
    }

    fn codegen_const(&mut self, const_val: &ConstValue, ty: Ty<'zir>) -> Result<CValue<'zir>> {
        match const_val {
            ConstValue::Scalar(scalar) => {
                let clif_ty = clif_type(ty, self.ptr_type).ok_or_else(|| self.type_error(ty))?;

                let value = match scalar.to_u64() {
                    Some(v) => self.builder.ins().iconst(clif_ty, v as i64),
                    None => {
                        if let Some(v) = scalar.to_u128() {
                            if clif_ty == types::I128 {
                                let lo = self.builder.ins().iconst(types::I64, v as i64);
                                let hi = self.builder.ins().iconst(types::I64, (v >> 64) as i64);
                                self.builder.ins().iconcat(lo, hi)
                            } else {
                                return Err(Error::layout(
                                    TyData::from_kind(&ty),
                                    "scalar too large",
                                ));
                            }
                        } else {
                            return Err(Error::Unsupported("arbitrary precision not supported"));
                        }
                    }
                };

                Ok(CValue::by_val(value, ty))
            }
            ConstValue::Zst => Ok(CValue::zst(ty)),
        }
    }

    fn codegen_place(&mut self, place: &Place<'zir>) -> Result<CPlace<'zir>> {
        let mut cplace = self.locals[place.local];

        for elem in place.projection.iter() {
            match elem {
                zir::mir::PlaceElem::Deref => {
                    let value = cplace.load(&mut self.builder, self.ptr_type);
                    if let Some(val) = value.load(&mut self.builder, self.ptr_type) {
                        cplace = CPlace::addr(Pointer::addr(val), cplace.ty());
                    }
                }
                zir::mir::PlaceElem::Field(idx) => {
                    cplace = cplace.field(*idx, cplace.ty(), &mut self.builder);
                }
                _ => {
                    return Err(Error::Unsupported("unsupported projection"));
                }
            }
        }

        Ok(cplace)
    }

    fn codegen_terminator(&mut self, terminator: &zir::mir::Terminator<'zir>) -> Result<()> {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let block = self.block_map[*target];
                self.builder.ins().jump(block, &[]);
            }
            TerminatorKind::Return => {
                let ret_place = self.locals[Local::RETURN_PLACE];
                let ret_value = ret_place.load(&mut self.builder, self.ptr_type);
                if let Some(val) = ret_value.load(&mut self.builder, self.ptr_type) {
                    self.builder.ins().return_(&[val]);
                } else {
                    self.builder.ins().return_(&[]);
                }
            }
            TerminatorKind::Unreachable => {
                self.builder.ins().trap(TrapCode::user(0).unwrap());
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let val = self.codegen_operand(discr)?;
                let loaded = val
                    .load(&mut self.builder, self.ptr_type)
                    .ok_or_else(|| self.error("switch on ZST"))?;

                let otherwise = self.block_map[targets.otherwise()];

                if targets.values.len() == 1 {
                    let then_block = self.block_map[targets.targets[0]];
                    let cmp =
                        self.builder.ins().icmp_imm(IntCC::Equal, loaded, targets.values[0] as i64);
                    self.builder.ins().brif(cmp, then_block, &[], otherwise, &[]);
                } else {
                    let mut switch = Switch::new();
                    for (val, target) in targets.iter() {
                        let block = self.block_map[target];
                        switch.set_entry(val, block);
                    }
                    switch.emit(&mut self.builder, loaded, otherwise);
                }
            }
            TerminatorKind::Call { fn_span, .. } => {
                return Err(Error::compile(*fn_span, "calls not implemented"));
            }
        }
        Ok(())
    }
}
