//! Scalar representation with arbitrary precision support

use std::fmt;

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};

/// Scalar value representation supporting arbitrary precision.
///
/// For values up to 128 bits, uses inline storage.
/// For larger values (u256, u512, etc.), uses BigUint.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ScalarRepr {
    /// Inline storage for values up to 128 bits
    Inline {
        /// The value data (little-endian)
        data: u128,
        /// Number of bytes (1-16)
        size: u8,
    },
    /// Heap storage for values larger than 128 bits
    Big {
        /// The value as arbitrary precision unsigned integer
        value: BigUint,
        /// Number of bytes
        size: u32,
    },
}

impl ScalarRepr {
    /// Creates a scalar from a u8.
    pub fn from_u8(value: u8) -> Self {
        ScalarRepr::Inline {
            data: value as u128,
            size: 1,
        }
    }

    /// Creates a scalar from a u16.
    pub fn from_u16(value: u16) -> Self {
        ScalarRepr::Inline {
            data: value as u128,
            size: 2,
        }
    }

    /// Creates a scalar from a u32.
    pub fn from_u32(value: u32) -> Self {
        ScalarRepr::Inline {
            data: value as u128,
            size: 4,
        }
    }

    /// Creates a scalar from a u64.
    pub fn from_u64(value: u64) -> Self {
        ScalarRepr::Inline {
            data: value as u128,
            size: 8,
        }
    }

    /// Creates a scalar from a u128.
    pub fn from_u128(value: u128) -> Self {
        ScalarRepr::Inline {
            data: value,
            size: 16,
        }
    }

    /// Creates a scalar from bytes (little-endian).
    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        if bytes.len() <= 16 {
            let mut data = [0u8; 16];
            data[..bytes.len()].copy_from_slice(bytes);
            ScalarRepr::Inline {
                data: u128::from_le_bytes(data),
                size: bytes.len() as u8,
            }
        } else {
            ScalarRepr::Big {
                value: BigUint::from_bytes_le(bytes),
                size: bytes.len() as u32,
            }
        }
    }

    /// Creates a scalar from a BigUint with specified byte size.
    pub fn from_biguint(value: BigUint, size: u32) -> Self {
        if size <= 16 {
            let bytes = value.to_bytes_le();
            let mut data = [0u8; 16];
            let copy_len = bytes.len().min(16);
            data[..copy_len].copy_from_slice(&bytes[..copy_len]);
            ScalarRepr::Inline {
                data: u128::from_le_bytes(data),
                size: size as u8,
            }
        } else {
            ScalarRepr::Big { value, size }
        }
    }

    /// Creates a zero scalar with the specified byte size.
    pub fn zero(size: u32) -> Self {
        if size <= 16 {
            ScalarRepr::Inline {
                data: 0,
                size: size as u8,
            }
        } else {
            ScalarRepr::Big {
                value: BigUint::zero(),
                size,
            }
        }
    }

    /// Returns the size in bytes.
    pub fn size(&self) -> u32 {
        match self {
            ScalarRepr::Inline { size, .. } => *size as u32,
            ScalarRepr::Big { size, .. } => *size,
        }
    }

    /// Converts to u8 if it fits.
    pub fn to_u8(&self) -> Option<u8> {
        match self {
            ScalarRepr::Inline { data, size } if *size <= 1 => Some(*data as u8),
            ScalarRepr::Big { value, size } if *size <= 1 => value.to_u8(),
            _ => None,
        }
    }

    /// Converts to u16 if it fits.
    pub fn to_u16(&self) -> Option<u16> {
        match self {
            ScalarRepr::Inline { data, size } if *size <= 2 => Some(*data as u16),
            ScalarRepr::Big { value, size } if *size <= 2 => value.to_u16(),
            _ => None,
        }
    }

    /// Converts to u32 if it fits.
    pub fn to_u32(&self) -> Option<u32> {
        match self {
            ScalarRepr::Inline { data, size } if *size <= 4 => Some(*data as u32),
            ScalarRepr::Big { value, size } if *size <= 4 => value.to_u32(),
            _ => None,
        }
    }

    /// Converts to u64 if it fits.
    pub fn to_u64(&self) -> Option<u64> {
        match self {
            ScalarRepr::Inline { data, size } if *size <= 8 => Some(*data as u64),
            ScalarRepr::Big { value, size } if *size <= 8 => value.to_u64(),
            _ => None,
        }
    }

    /// Converts to u128 if it fits.
    pub fn to_u128(&self) -> Option<u128> {
        match self {
            ScalarRepr::Inline { data, .. } => Some(*data),
            ScalarRepr::Big { value, size } if *size <= 16 => value.to_u128(),
            _ => None,
        }
    }

    /// Returns the value as a BigUint.
    pub fn to_biguint(&self) -> BigUint {
        match self {
            ScalarRepr::Inline { data, size } => {
                let bytes = data.to_le_bytes();
                BigUint::from_bytes_le(&bytes[..*size as usize])
            }
            ScalarRepr::Big { value, .. } => value.clone(),
        }
    }

    /// Returns the value as bytes (little-endian).
    pub fn to_bytes_le(&self) -> Vec<u8> {
        match self {
            ScalarRepr::Inline { data, size } => {
                let bytes = data.to_le_bytes();
                bytes[..*size as usize].to_vec()
            }
            ScalarRepr::Big { value, size } => {
                let mut bytes = value.to_bytes_le();
                bytes.resize(*size as usize, 0);
                bytes
            }
        }
    }

    /// Returns true if the value is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            ScalarRepr::Inline { data, .. } => *data == 0,
            ScalarRepr::Big { value, .. } => value.is_zero(),
        }
    }

    /// Truncates to the specified byte size.
    pub fn truncate(&self, new_size: u32) -> Self {
        let bytes = self.to_bytes_le();
        let truncated: Vec<u8> = bytes.into_iter().take(new_size as usize).collect();
        Self::from_bytes_le(&truncated)
    }

    /// Zero-extends to the specified byte size.
    pub fn zero_extend(&self, new_size: u32) -> Self {
        let mut bytes = self.to_bytes_le();
        bytes.resize(new_size as usize, 0);
        Self::from_bytes_le(&bytes)
    }

    /// Sign-extends to the specified byte size.
    pub fn sign_extend(&self, new_size: u32) -> Self {
        let mut bytes = self.to_bytes_le();
        let sign_byte = if bytes.last().map_or(false, |&b| b & 0x80 != 0) {
            0xFF
        } else {
            0x00
        };
        bytes.resize(new_size as usize, sign_byte);
        Self::from_bytes_le(&bytes)
    }
}

impl fmt::Debug for ScalarRepr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScalarRepr::Inline { data, size } => {
                write!(f, "0x{:0width$x}_u{}", data, size * 8, width = *size as usize * 2)
            }
            ScalarRepr::Big { value, size } => {
                write!(f, "0x{:x}_u{}", value, size * 8)
            }
        }
    }
}

impl Default for ScalarRepr {
    fn default() -> Self {
        ScalarRepr::zero(8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inline_scalars() {
        let s8 = ScalarRepr::from_u8(42);
        assert_eq!(s8.to_u8(), Some(42));
        assert_eq!(s8.size(), 1);

        let s64 = ScalarRepr::from_u64(0x123456789ABCDEF0);
        assert_eq!(s64.to_u64(), Some(0x123456789ABCDEF0));
        assert_eq!(s64.size(), 8);
    }

    #[test]
    fn test_big_scalars() {
        // Create a 256-bit scalar
        let bytes: Vec<u8> = (0..32).collect();
        let s256 = ScalarRepr::from_bytes_le(&bytes);
        assert_eq!(s256.size(), 32);

        let result = s256.to_bytes_le();
        assert_eq!(result, bytes);
    }

    #[test]
    fn test_zero_extend() {
        let s8 = ScalarRepr::from_u8(0xFF);
        let s16 = s8.zero_extend(2);
        assert_eq!(s16.to_u16(), Some(0x00FF));
    }

    #[test]
    fn test_sign_extend() {
        let s8 = ScalarRepr::from_u8(0xFF);
        let s16 = s8.sign_extend(2);
        assert_eq!(s16.to_u16(), Some(0xFFFF));

        let s8_pos = ScalarRepr::from_u8(0x7F);
        let s16_pos = s8_pos.sign_extend(2);
        assert_eq!(s16_pos.to_u16(), Some(0x007F));
    }
}
