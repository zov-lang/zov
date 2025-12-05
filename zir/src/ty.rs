//! Type system with arbitrary bit-width integers.

use std::fmt;
use serde::{Serialize, Deserialize};
use crate::idx::{TyId, FuncId};

/// Specification for integer bit width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IntWidth {
    /// Fixed bit width (1-65535 bits).
    Fixed(u16),
    /// Pointer-sized integer.
    Ptr,
}

impl IntWidth {
    pub const I8: Self = Self::Fixed(8);
    pub const I16: Self = Self::Fixed(16);
    pub const I32: Self = Self::Fixed(32);
    pub const I64: Self = Self::Fixed(64);
    pub const I128: Self = Self::Fixed(128);
    pub const ISIZE: Self = Self::Ptr;

    /// Get the bit width for a given pointer size.
    pub fn bits(&self, ptr_bits: u16) -> u16 {
        match self {
            IntWidth::Fixed(bits) => *bits,
            IntWidth::Ptr => ptr_bits,
        }
    }
}

impl fmt::Debug for IntWidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntWidth::Fixed(bits) => write!(f, "{}", bits),
            IntWidth::Ptr => write!(f, "ptr"),
        }
    }
}

/// Mutability of a reference or pointer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum Mutability {
    /// Immutable.
    Not,
    /// Mutable.
    Mut,
}

impl Mutability {
    pub fn is_mut(&self) -> bool {
        matches!(self, Mutability::Mut)
    }

    pub fn prefix_str(&self) -> &'static str {
        match self {
            Mutability::Not => "",
            Mutability::Mut => "mut ",
        }
    }
}

/// The kind of a type.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TyKind {
    /// Boolean type.
    Bool,
    /// Signed integer with arbitrary bit width.
    Int(IntWidth),
    /// Unsigned integer with arbitrary bit width.
    Uint(IntWidth),
    /// Unit type (empty tuple).
    Unit,
    /// Tuple of types.
    Tuple(Vec<TyId>),
    /// Reference to a type.
    Ref(Mutability, TyId),
    /// Raw pointer to a type.
    Ptr(Mutability, TyId),
    /// Function type (by definition id).
    FnDef(FuncId),
    /// Never type (diverging).
    Never,
}

impl TyKind {
    /// Create an unsigned integer type with fixed bit width.
    pub fn uint(bits: u16) -> Self {
        TyKind::Uint(IntWidth::Fixed(bits))
    }

    /// Create a signed integer type with fixed bit width.
    pub fn int(bits: u16) -> Self {
        TyKind::Int(IntWidth::Fixed(bits))
    }
}

impl fmt::Debug for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Int(width) => write!(f, "i{:?}", width),
            TyKind::Uint(width) => write!(f, "u{:?}", width),
            TyKind::Unit => write!(f, "()"),
            TyKind::Tuple(tys) => {
                write!(f, "(")?;
                for (i, ty) in tys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", ty)?;
                }
                write!(f, ")")
            }
            TyKind::Ref(mutbl, ty) => write!(f, "&{}{:?}", mutbl.prefix_str(), ty),
            TyKind::Ptr(mutbl, ty) => {
                let qual = if mutbl.is_mut() { "mut" } else { "const" };
                write!(f, "*{} {:?}", qual, ty)
            }
            TyKind::FnDef(id) => write!(f, "fn({:?})", id),
            TyKind::Never => write!(f, "!"),
        }
    }
}

/// A type with its ID (for arena reference).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Ty {
    id: TyId,
}

impl Ty {
    /// Create a type from its ID.
    pub fn new(id: TyId) -> Self {
        Self { id }
    }

    /// Get the type ID.
    pub fn id(&self) -> TyId {
        self.id
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.id)
    }
}

impl From<TyId> for Ty {
    fn from(id: TyId) -> Self {
        Self::new(id)
    }
}

impl From<Ty> for TyId {
    fn from(ty: Ty) -> Self {
        ty.id
    }
}

/// Function signature.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct FnSig {
    /// Input parameter types.
    pub inputs: Vec<TyId>,
    /// Output (return) type.
    pub output: TyId,
}

impl FnSig {
    pub fn new(inputs: Vec<TyId>, output: TyId) -> Self {
        Self { inputs, output }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_width() {
        assert_eq!(IntWidth::I8.bits(64), 8);
        assert_eq!(IntWidth::I32.bits(64), 32);
        assert_eq!(IntWidth::ISIZE.bits(64), 64);
        assert_eq!(IntWidth::ISIZE.bits(32), 32);
    }

    #[test]
    fn test_type_debug() {
        assert_eq!(format!("{:?}", TyKind::Bool), "bool");
        assert_eq!(format!("{:?}", TyKind::uint(256)), "u256");
        assert_eq!(format!("{:?}", TyKind::int(32)), "i32");
        assert_eq!(format!("{:?}", TyKind::Unit), "()");
        assert_eq!(format!("{:?}", TyKind::Never), "!");
    }
}
