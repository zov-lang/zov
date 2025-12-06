//! Place handling for Cranelift codegen

use cranelift::prelude::*;
use zir::ty::Ty;

use crate::value::{CValue, Pointer};

/// A place in Cranelift IR (an lvalue).
#[derive(Debug, Clone, Copy)]
pub struct CPlace<'zir> {
    inner: CPlaceInner,
    ty: Ty<'zir>,
}

#[derive(Debug, Clone, Copy)]
enum CPlaceInner {
    /// Place stored in a variable.
    Var(Variable),
    /// Place stored at a memory address.
    Addr(Pointer),
}

impl<'zir> CPlace<'zir> {
    /// Creates a place from a Cranelift variable.
    pub fn var(var: Variable, ty: Ty<'zir>) -> Self {
        Self { inner: CPlaceInner::Var(var), ty }
    }

    /// Creates a place from a memory address.
    pub fn addr(ptr: Pointer, ty: Ty<'zir>) -> Self {
        Self { inner: CPlaceInner::Addr(ptr), ty }
    }

    /// Returns the type of this place.
    pub fn ty(&self) -> Ty<'zir> {
        self.ty
    }

    /// Loads the value from this place.
    pub fn load(self, builder: &mut FunctionBuilder<'_>, _ptr_type: types::Type) -> CValue<'zir> {
        match self.inner {
            CPlaceInner::Var(var) => {
                let val = builder.use_var(var);
                CValue::by_val(val, self.ty)
            }
            CPlaceInner::Addr(ptr) => CValue::by_ref(ptr, self.ty),
        }
    }

    /// Stores a value to this place.
    pub fn store(
        self,
        builder: &mut FunctionBuilder<'_>,
        value: CValue<'zir>,
        ptr_type: types::Type,
    ) {
        if let Some(val) = value.load(builder, ptr_type) {
            match self.inner {
                CPlaceInner::Var(var) => {
                    builder.def_var(var, val);
                }
                CPlaceInner::Addr(ptr) => {
                    ptr.store(builder, val);
                }
            }
        }
    }

    /// Returns the address of this place.
    #[allow(dead_code)]
    pub fn as_ptr(self, _builder: &mut FunctionBuilder<'_>) -> Option<Pointer> {
        match self.inner {
            CPlaceInner::Var(_) => None, // Variables don't have addresses
            CPlaceInner::Addr(ptr) => Some(ptr),
        }
    }

    /// Projects into a field of this place.
    pub fn field(self, index: u32, field_ty: Ty<'zir>, _builder: &mut FunctionBuilder<'_>) -> Self {
        match self.inner {
            CPlaceInner::Var(_) => {
                panic!("cannot take field of SSA variable");
            }
            CPlaceInner::Addr(ptr) => {
                // Calculate field offset (simplified - assumes packed layout)
                let offset = (index * 8) as i32; // Assume 8-byte alignment
                CPlace::addr(ptr.offset(offset), field_ty)
            }
        }
    }
}
