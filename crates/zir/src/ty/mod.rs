//! Type system for ZIR with arbitrary precision integers

mod scalar;

use std::fmt;
use std::hash::Hash;

pub use scalar::ScalarRepr;

use crate::intern::Interned;
use crate::list::List;
use crate::mir::DefId;

/// An interned type reference.
pub type Ty<'zir> = Interned<'zir, TyKind<'zir>>;

/// The kinds of types in ZIR.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind<'zir> {
    /// Boolean type
    Bool,

    /// Signed integer with arbitrary bit width
    Int(IntWidth),

    /// Unsigned integer with arbitrary bit width
    Uint(IntWidth),

    /// Tuple type
    Tuple(&'zir List<Ty<'zir>>),

    /// Reference type
    Ref(Mutability, Ty<'zir>),

    /// Raw pointer type
    Ptr(Mutability, Ty<'zir>),

    /// Function definition
    FnDef(DefId),

    /// Never type (for diverging functions)
    Never,

    /// Unit type
    Unit,
}

impl<'zir> fmt::Debug for TyKind<'zir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Int(w) => write!(f, "i{}", w.bits()),
            TyKind::Uint(w) => write!(f, "u{}", w.bits()),
            TyKind::Tuple(elems) => {
                let mut tup = f.debug_tuple("");
                for elem in elems.iter() {
                    tup.field(elem);
                }
                tup.finish()
            }
            TyKind::Ref(m, ty) => write!(f, "&{}{:?}", m.prefix_str(), ty),
            TyKind::Ptr(m, ty) => write!(f, "*{}{:?}", m.ptr_str(), ty),
            TyKind::FnDef(def) => write!(f, "fn({:?})", def),
            TyKind::Never => write!(f, "!"),
            TyKind::Unit => write!(f, "()"),
        }
    }
}

impl<'zir> fmt::Display for TyKind<'zir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// Integer width for arbitrary precision integers.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntWidth {
    /// Platform-dependent pointer-sized integer
    Size,
    /// Fixed bit width (1 to 2^32 bits)
    Fixed(u32),
}

impl IntWidth {
    pub const I8: Self = IntWidth::Fixed(8);
    pub const I16: Self = IntWidth::Fixed(16);
    pub const I32: Self = IntWidth::Fixed(32);
    pub const I64: Self = IntWidth::Fixed(64);
    pub const I128: Self = IntWidth::Fixed(128);
    pub const I256: Self = IntWidth::Fixed(256);

    /// Returns the bit width, or None for pointer-sized.
    pub fn fixed_bits(self) -> Option<u32> {
        match self {
            IntWidth::Size => None,
            IntWidth::Fixed(bits) => Some(bits),
        }
    }

    /// Returns the bit width as a string.
    pub fn bits(self) -> String {
        match self {
            IntWidth::Size => "size".to_string(),
            IntWidth::Fixed(bits) => bits.to_string(),
        }
    }

    /// Returns the byte size, rounding up.
    pub fn bytes(self, ptr_size: u32) -> u32 {
        let bits = match self {
            IntWidth::Size => ptr_size * 8,
            IntWidth::Fixed(bits) => bits,
        };
        (bits + 7) / 8
    }

    /// Creates a new fixed-width integer type.
    pub fn fixed(bits: u32) -> Self {
        assert!(bits > 0, "bit width must be positive");
        IntWidth::Fixed(bits)
    }
}

impl fmt::Debug for IntWidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntWidth::Size => write!(f, "size"),
            IntWidth::Fixed(bits) => write!(f, "{}", bits),
        }
    }
}

/// Mutability of references and pointers.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Mutability {
    /// Immutable (const)
    Not,
    /// Mutable
    Mut,
}

impl Mutability {
    /// Returns the prefix string for references.
    pub fn prefix_str(self) -> &'static str {
        match self {
            Mutability::Not => "",
            Mutability::Mut => "mut ",
        }
    }

    /// Returns the string for pointer types.
    pub fn ptr_str(self) -> &'static str {
        match self {
            Mutability::Not => "const ",
            Mutability::Mut => "mut ",
        }
    }

    /// Returns true if mutable.
    pub fn is_mut(self) -> bool {
        matches!(self, Mutability::Mut)
    }

    /// Returns true if immutable.
    pub fn is_not(self) -> bool {
        matches!(self, Mutability::Not)
    }
}

/// ABI for function calls.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Abi {
    /// ZoV calling convention
    Zov,
    /// C calling convention
    C,
}

/// Function signature.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnSig<'zir> {
    /// Input types followed by output type as the last element
    pub inputs_and_output: &'zir List<Ty<'zir>>,
    /// Calling convention
    pub abi: Abi,
}

impl<'zir> FnSig<'zir> {
    /// Returns the input parameter types.
    pub fn inputs(&self) -> &[Ty<'zir>] {
        let len = self.inputs_and_output.len();
        if len == 0 { &[] } else { &self.inputs_and_output[..len - 1] }
    }

    /// Returns the output type.
    pub fn output(&self) -> Ty<'zir> {
        self.inputs_and_output.last().copied().expect("signature must have output type")
    }
}

impl<'zir> fmt::Debug for FnSig<'zir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn(")?;
        for (i, ty) in self.inputs().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", ty)?;
        }
        write!(f, ") -> {:?}", self.output())
    }
}
