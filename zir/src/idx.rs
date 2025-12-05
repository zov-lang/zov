//! Index types for arena-based data structures.

use std::fmt;
use serde::{Serialize, Deserialize, Serializer, Deserializer};

macro_rules! define_index {
    (
        $(#[$attr:meta])*
        $vis:vis struct $name:ident;
    ) => {
        $(#[$attr])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        $vis struct $name(u32);

        impl $name {
            pub const fn new(index: usize) -> Self {
                Self(index as u32)
            }

            pub const fn from_raw(raw: u32) -> Self {
                Self(raw)
            }

            pub const fn from_raw_unchecked(raw: u32) -> Self {
                Self(raw)
            }

            pub const fn index(self) -> usize {
                self.0 as usize
            }

            pub const fn raw(self) -> u32 {
                self.0
            }
        }

        impl From<usize> for $name {
            fn from(index: usize) -> Self {
                Self::new(index)
            }
        }

        impl From<$name> for usize {
            fn from(idx: $name) -> Self {
                idx.index()
            }
        }

        impl index_vec::Idx for $name {
            fn from_usize(idx: usize) -> Self {
                Self::new(idx)
            }

            fn index(self) -> usize {
                self.index()
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Ok(Self(u32::deserialize(deserializer)?))
            }
        }
    };
}

define_index! {
    /// Index into the basic blocks of a function body.
    pub struct BasicBlock;
}

impl BasicBlock {
    /// The entry block of a function.
    pub const START: Self = Self::from_raw_unchecked(0);
}

impl fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

define_index! {
    /// Index into the local variables of a function body.
    pub struct Local;
}

impl Local {
    /// The return place (local 0).
    pub const RETURN_PLACE: Self = Self::from_raw_unchecked(0);
}

impl fmt::Debug for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

define_index! {
    /// Index into the type arena.
    pub struct TyId;
}

impl fmt::Debug for TyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ty{}", self.0)
    }
}

define_index! {
    /// Index into the function arena.
    pub struct FuncId;
}

impl fmt::Debug for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn{}", self.0)
    }
}

define_index! {
    /// Index into the global arena.
    pub struct GlobalId;
}

impl fmt::Debug for GlobalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "global{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_block_debug() {
        assert_eq!(format!("{:?}", BasicBlock::START), "bb0");
        assert_eq!(format!("{:?}", BasicBlock::new(5)), "bb5");
    }

    #[test]
    fn test_local_debug() {
        assert_eq!(format!("{:?}", Local::RETURN_PLACE), "_0");
        assert_eq!(format!("{:?}", Local::new(3)), "_3");
    }

    #[test]
    fn test_serde_roundtrip() {
        let original = TyId::new(42);
        let json = serde_json::to_string(&original).unwrap();
        let restored: TyId = serde_json::from_str(&json).unwrap();
        assert_eq!(original, restored);
    }
}
