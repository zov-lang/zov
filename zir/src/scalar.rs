//! Arbitrary precision scalar representation.
//!
//! Supports integers of any bit width (u<N> types).

use std::fmt;
use num_bigint::BigUint;
use num_traits::{Zero, One, ToPrimitive};
use serde::{Serialize, Deserialize};

/// Arbitrary precision unsigned scalar value.
///
/// Supports any bit width from 1 to 65535 bits.
/// Values are stored in a normalized form where the bit width
/// is always respected (values are truncated to fit).
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Scalar {
    /// The value data. Invariant: always fits within `bits` bits.
    data: ScalarData,
    /// Bit width of this scalar (1-65535).
    bits: u16,
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum ScalarData {
    /// Small values that fit in u128.
    Small(u128),
    /// Large values requiring arbitrary precision.
    Big(BigUint),
}

impl Scalar {
    /// Create a scalar with zero value and given bit width.
    pub fn zero(bits: u16) -> Self {
        assert!(bits > 0, "bit width must be at least 1");
        Self {
            data: ScalarData::Small(0),
            bits,
        }
    }

    /// Create a scalar from a u128 value with given bit width.
    /// The value is truncated to fit the bit width.
    pub fn from_u128(value: u128, bits: u16) -> Self {
        assert!(bits > 0, "bit width must be at least 1");
        let truncated = Self::truncate_u128(value, bits);
        Self {
            data: ScalarData::Small(truncated),
            bits,
        }
    }

    /// Create a scalar from a BigUint with given bit width.
    /// The value is truncated to fit the bit width.
    pub fn from_biguint(value: BigUint, bits: u16) -> Self {
        assert!(bits > 0, "bit width must be at least 1");
        let truncated = Self::truncate_biguint(value, bits);
        if bits <= 128 {
            Self {
                data: ScalarData::Small(truncated.to_u128().unwrap_or(0)),
                bits,
            }
        } else {
            Self {
                data: ScalarData::Big(truncated),
                bits,
            }
        }
    }

    /// Create a scalar from bytes (little-endian) with given bit width.
    pub fn from_bytes_le(bytes: &[u8], bits: u16) -> Self {
        let value = BigUint::from_bytes_le(bytes);
        Self::from_biguint(value, bits)
    }

    /// The bit width of this scalar.
    pub fn bits(&self) -> u16 {
        self.bits
    }

    /// The byte size needed to store this scalar.
    pub fn byte_size(&self) -> usize {
        (self.bits as usize + 7) / 8
    }

    /// Check if this scalar is zero.
    pub fn is_zero(&self) -> bool {
        match &self.data {
            ScalarData::Small(v) => *v == 0,
            ScalarData::Big(v) => v.is_zero(),
        }
    }

    /// Get the value as u128 if it fits.
    pub fn to_u128(&self) -> Option<u128> {
        match &self.data {
            ScalarData::Small(v) => Some(*v),
            ScalarData::Big(v) => v.to_u128(),
        }
    }

    /// Get the value as BigUint.
    pub fn to_biguint(&self) -> BigUint {
        match &self.data {
            ScalarData::Small(v) => BigUint::from(*v),
            ScalarData::Big(v) => v.clone(),
        }
    }

    /// Get the value as little-endian bytes.
    pub fn to_bytes_le(&self) -> Vec<u8> {
        let mut bytes = match &self.data {
            ScalarData::Small(v) => {
                let mut bytes = v.to_le_bytes().to_vec();
                bytes.truncate(self.byte_size());
                bytes
            }
            ScalarData::Big(v) => v.to_bytes_le(),
        };
        bytes.resize(self.byte_size(), 0);
        bytes
    }

    /// Truncate a u128 value to fit within the given bit width.
    fn truncate_u128(value: u128, bits: u16) -> u128 {
        if bits >= 128 {
            value
        } else {
            value & ((1u128 << bits) - 1)
        }
    }

    /// Truncate a BigUint value to fit within the given bit width.
    fn truncate_biguint(value: BigUint, bits: u16) -> BigUint {
        if value.bits() as u16 <= bits {
            value
        } else {
            let mask = (BigUint::one() << bits as usize) - BigUint::one();
            value & mask
        }
    }

    /// Boolean true value (1-bit scalar with value 1).
    pub const fn bool_true() -> Self {
        Self {
            data: ScalarData::Small(1),
            bits: 1,
        }
    }

    /// Boolean false value (1-bit scalar with value 0).
    pub const fn bool_false() -> Self {
        Self {
            data: ScalarData::Small(0),
            bits: 1,
        }
    }

    /// Create from a boolean.
    pub const fn from_bool(value: bool) -> Self {
        if value {
            Self::bool_true()
        } else {
            Self::bool_false()
        }
    }

    /// Try to convert to boolean.
    pub fn to_bool(&self) -> Option<bool> {
        if self.bits != 1 {
            return None;
        }
        match &self.data {
            ScalarData::Small(0) => Some(false),
            ScalarData::Small(1) => Some(true),
            _ => None,
        }
    }
}

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.data {
            ScalarData::Small(v) => write!(f, "{}u{}", v, self.bits),
            ScalarData::Big(v) => write!(f, "{}u{}", v, self.bits),
        }
    }
}

impl fmt::Display for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.data {
            ScalarData::Small(v) => write!(f, "{}", v),
            ScalarData::Big(v) => write!(f, "{}", v),
        }
    }
}

macro_rules! impl_from_primitive {
    ($($ty:ty => $bits:expr),* $(,)?) => {
        $(
            impl From<$ty> for Scalar {
                fn from(value: $ty) -> Self {
                    Self::from_u128(value as u128, $bits)
                }
            }
        )*
    };
}

impl_from_primitive! {
    bool => 1,
    u8 => 8,
    u16 => 16,
    u32 => 32,
    u64 => 64,
    u128 => 128,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scalar_zero() {
        let s = Scalar::zero(32);
        assert_eq!(s.bits(), 32);
        assert!(s.is_zero());
        assert_eq!(s.to_u128(), Some(0));
    }

    #[test]
    fn test_scalar_from_u128() {
        let s = Scalar::from_u128(255, 8);
        assert_eq!(s.bits(), 8);
        assert_eq!(s.to_u128(), Some(255));

        let s = Scalar::from_u128(256, 8);
        assert_eq!(s.to_u128(), Some(0)); // truncated
    }

    #[test]
    fn test_scalar_bool() {
        assert_eq!(Scalar::from_bool(true).to_bool(), Some(true));
        assert_eq!(Scalar::from_bool(false).to_bool(), Some(false));
    }

    #[test]
    fn test_scalar_large() {
        let big: BigUint = BigUint::from(1u128) << 200usize;
        let s = Scalar::from_biguint(big.clone(), 256);
        assert_eq!(s.bits(), 256);
        assert_eq!(s.to_biguint(), big);
    }

    #[test]
    fn test_scalar_debug() {
        assert_eq!(format!("{:?}", Scalar::from(42u8)), "42u8");
        assert_eq!(format!("{:?}", Scalar::from_u128(100, 16)), "100u16");
    }
}
