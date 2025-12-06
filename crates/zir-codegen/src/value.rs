//! Value representation for Cranelift codegen

use cranelift::prelude::*;
use cranelift_codegen::ir::StackSlot;
use zir::ty::{Ty, TyKind};

/// A value in Cranelift IR.
#[derive(Debug, Clone, Copy)]
pub struct CValue<'zir> {
    inner: CValueInner,
    ty: Ty<'zir>,
}

#[derive(Debug, Clone, Copy)]
enum CValueInner {
    /// Value stored in a Cranelift SSA value.
    ByVal(Value),
    /// Value stored at a memory address.
    ByRef(Pointer),
    /// Zero-sized type (no actual value).
    Zst,
}

impl<'zir> CValue<'zir> {
    /// Creates a value from a Cranelift SSA value.
    pub fn by_val(value: Value, ty: Ty<'zir>) -> Self {
        Self {
            inner: CValueInner::ByVal(value),
            ty,
        }
    }

    /// Creates a value from a memory pointer.
    pub fn by_ref(ptr: Pointer, ty: Ty<'zir>) -> Self {
        Self {
            inner: CValueInner::ByRef(ptr),
            ty,
        }
    }

    /// Creates a zero-sized type value.
    pub fn zst(ty: Ty<'zir>) -> Self {
        Self {
            inner: CValueInner::Zst,
            ty,
        }
    }

    /// Returns the type of this value.
    pub fn ty(&self) -> Ty<'zir> {
        self.ty
    }

    /// Returns true if this is a zero-sized type.
    pub fn is_zst(&self) -> bool {
        match &*self.ty {
            TyKind::Unit => true,
            TyKind::Tuple(elems) => elems.is_empty(),
            _ => false,
        }
    }

    /// Loads the value if stored by reference.
    pub fn load(
        self,
        builder: &mut FunctionBuilder<'_>,
        ptr_type: types::Type,
    ) -> Option<Value> {
        if self.is_zst() {
            return None;
        }

        match self.inner {
            CValueInner::ByVal(val) => Some(val),
            CValueInner::ByRef(ptr) => {
                let clif_ty = super::clif_type(self.ty, ptr_type)?;
                let addr = ptr.get_addr(builder);
                Some(builder.ins().load(clif_ty, MemFlags::new(), addr, 0))
            }
            CValueInner::Zst => None,
        }
    }

    /// Returns the SSA value if stored by value.
    pub fn as_val(&self) -> Option<Value> {
        match self.inner {
            CValueInner::ByVal(val) => Some(val),
            CValueInner::ByRef(_) | CValueInner::Zst => None,
        }
    }
}

/// A memory pointer.
#[derive(Debug, Clone, Copy)]
pub struct Pointer {
    kind: PointerKind,
    offset: i32,
}

#[derive(Debug, Clone, Copy)]
enum PointerKind {
    /// Pointer to a stack slot.
    StackSlot(StackSlot),
    /// Pointer stored in a value.
    Addr(Value),
}

impl Pointer {
    /// Creates a pointer to a stack slot.
    pub fn stack_slot(slot: StackSlot) -> Self {
        Self {
            kind: PointerKind::StackSlot(slot),
            offset: 0,
        }
    }

    /// Creates a pointer from an address value.
    pub fn addr(value: Value) -> Self {
        Self {
            kind: PointerKind::Addr(value),
            offset: 0,
        }
    }

    /// Returns the pointer with an added offset.
    pub fn offset(self, offset: i32) -> Self {
        Self {
            kind: self.kind,
            offset: self.offset + offset,
        }
    }

    /// Gets the address as a Cranelift value.
    pub fn get_addr(self, builder: &mut FunctionBuilder<'_>) -> Value {
        match self.kind {
            PointerKind::StackSlot(slot) => {
                builder.ins().stack_addr(types::I64, slot, self.offset)
            }
            PointerKind::Addr(addr) => {
                if self.offset == 0 {
                    addr
                } else {
                    let offset = builder.ins().iconst(types::I64, self.offset as i64);
                    builder.ins().iadd(addr, offset)
                }
            }
        }
    }

    /// Stores a value at this pointer.
    pub fn store(self, builder: &mut FunctionBuilder<'_>, value: Value) {
        let addr = self.get_addr(builder);
        builder.ins().store(MemFlags::new(), value, addr, 0);
    }
}
