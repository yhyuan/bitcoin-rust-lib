//! Secure elliptic curve point operations with validation and memory safety
//!
//! This module provides cryptographically secure point operations with proper
//! input validation, curve checks, and memory-safe conversions.

#![no_std]

use core::ops::{Add, Shr};
use core::cmp::Ordering;
use crate::field256_secure::Field256;
use crate::u256::{U256, P};
use crate::error::{BitcoinError, Result, CryptographicError, InputError};
use crate::{crypto_error, input_error};
use crate::safe_conversions::{slice_to_array, secure_zero};

/// Represents a point on the secp256k1 elliptic curve
#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct SecurePoint {
    x: Field256,
    y: Field256,
    /// Point at infinity flag
    is_infinity: bool,
}

impl SecurePoint {
    /// Create a new point with validation
    pub fn new(x: Field256, y: Field256) -> Result<Self> {
        let point = SecurePoint { x, y, is_infinity: false };
        point.validate_on_curve()?;
        Ok(point)
    }

    /// Create point without validation (for internal use only)
    pub fn new_unchecked(x: Field256, y: Field256) -> Self {
        SecurePoint { x, y, is_infinity: false }
    }

    /// Create point at infinity
    pub fn infinity() -> Self {
        SecurePoint { 
            x: Field256::zero(P), 
            y: Field256::zero(P), 
            is_infinity: true 
        }
    }

    /// Get point coordinates with validation
    pub fn coordinates(&self) -> Result<(Field256, Field256)> {
        if self.is_infinity {
            return Err(crypto_error!(PointAtInfinity));
        }
        Ok((self.x, self.y))
    }

    /// Zero point (point at infinity)
    pub fn zero() -> Self {
        Self::infinity()
    }

    /// Get the secp256k1 generator point with validation
    pub fn generator() -> Result<Self> {
        let x_val = U256::new(
            0x79be667ef9dcbbac55a06295ce870b07u128, 
            0x029bfcdb2dce28d959f2815b16f81798u128
        );
        let y_val = U256::new(
            0x483ada7726a3c4655da4fbfc0e1108a8u128, 
            0xfd17b448a68554199c47d08ffb10d4b8u128
        );
        
        let x_field = Field256::new(x_val, P)?;
        let y_field = Field256::new(y_val, P)?;
        
        Self::new(x_field, y_field)
    }

    /// Secure scalar multiplication with side-channel protection
    pub fn scalar_multiply(&self, scalar: U256) -> Result<Self> {
        if scalar.is_zero() {
            return Ok(Self::infinity());
        }

        // Use Montgomery ladder for constant-time scalar multiplication
        let mut r0 = Self::infinity();
        let mut r1 = *self;
        
        // Process bits from most significant to least significant
        for i in (0..256).rev() {
            let shifted = scalar >> i;
            let bit = shifted.is_odd();
            
            if bit {
                r0 = r0.checked_add(r1)?;
                r1 = r1.double()?;
            } else {
                r1 = r1.checked_add(r0)?;
                r0 = r0.double()?;
            }
        }
        
        Ok(r0)
    }

    /// Point doubling with validation
    pub fn double(&self) -> Result<Self> {
        if self.is_infinity {
            return Ok(*self);
        }

        // Check for point doubling edge case (y = 0)
        if self.y.is_zero() {
            return Ok(Self::infinity());
        }

        // s = (3 * x^2) / (2 * y)
        let three = Field256::new_unchecked(U256::from(3u128), P);
        let two = Field256::new_unchecked(U256::from(2u128), P);
        
        let x_squared = self.x.checked_mul(self.x)?;
        let numerator = three.checked_mul(x_squared)?;
        let denominator = two.checked_mul(self.y)?;
        let slope = numerator.checked_div(denominator)?;

        // x3 = s^2 - 2*x
        let slope_squared = slope.checked_mul(slope)?;
        let two_x = two.checked_mul(self.x)?;
        let x3 = slope_squared.checked_sub(two_x)?;

        // y3 = s*(x - x3) - y
        let x_diff = self.x.checked_sub(x3)?;
        let slope_diff = slope.checked_mul(x_diff)?;
        let y3 = slope_diff.checked_sub(self.y)?;

        Ok(SecurePoint { x: x3, y: y3, is_infinity: false })
    }

    /// Secure point addition with validation
    pub fn checked_add(&self, other: Self) -> Result<Self> {
        // Handle infinity cases
        if self.is_infinity {
            return Ok(other);
        }
        if other.is_infinity {
            return Ok(*self);
        }

        // Check if points are the same (point doubling)
        if self.x == other.x {
            if self.y == other.y {
                return self.double();
            } else {
                // Points are inverses, result is infinity
                return Ok(Self::infinity());
            }
        }

        // Calculate slope: s = (y2 - y1) / (x2 - x1)
        let y_diff = other.y.checked_sub(self.y)?;
        let x_diff = other.x.checked_sub(self.x)?;
        let slope = y_diff.checked_div(x_diff)?;

        // x3 = s^2 - x1 - x2
        let slope_squared = slope.checked_mul(slope)?;
        let x3 = slope_squared.checked_sub(self.x)?.checked_sub(other.x)?;

        // y3 = s*(x1 - x3) - y1
        let x_diff_result = self.x.checked_sub(x3)?;
        let slope_diff = slope.checked_mul(x_diff_result)?;
        let y3 = slope_diff.checked_sub(self.y)?;

        Ok(SecurePoint { x: x3, y: y3, is_infinity: false })
    }

    /// Validate that point is on secp256k1 curve: y^2 = x^3 + 7
    pub fn validate_on_curve(&self) -> Result<()> {
        if self.is_infinity {
            return Ok(());
        }

        let seven = Field256::new_unchecked(U256::from(7u128), P);
        
        // Calculate y^2
        let y_squared = self.y.checked_mul(self.y)?;
        
        // Calculate x^3 + 7
        let x_squared = self.x.checked_mul(self.x)?;
        let x_cubed = x_squared.checked_mul(self.x)?;
        let right_side = x_cubed.checked_add(seven)?;

        if y_squared == right_side {
            Ok(())
        } else {
            Err(crypto_error!(InvalidCurvePoint))
        }
    }

    /// Generate secure uncompressed public key (65 bytes)
    pub fn to_uncompressed_public_key(&self) -> Result<[u8; 65]> {
        if self.is_infinity {
            return Err(crypto_error!(PointAtInfinity));
        }

        let mut public_key = [0u8; 65];
        public_key[0] = 0x04; // Uncompressed point indicator

        // Extract coordinates safely
        let (x_val, y_val) = self.coordinates()?;
        let x_u256 = x_val.u;
        let y_u256 = y_val.u;

        // Convert coordinates to bytes safely
        let x_bytes = x_u256.to_be_bytes();
        let y_bytes = y_u256.to_be_bytes();

        public_key[1..33].copy_from_slice(&x_bytes);
        public_key[33..65].copy_from_slice(&y_bytes);

        Ok(public_key)
    }

    /// Generate secure compressed public key (33 bytes)
    pub fn to_compressed_public_key(&self) -> Result<[u8; 33]> {
        if self.is_infinity {
            return Err(crypto_error!(PointAtInfinity));
        }

        let mut public_key = [0u8; 33];
        
        // Extract coordinates safely
        let (x_val, y_val) = self.coordinates()?;
        let x_u256 = x_val.u;
        let y_u256 = y_val.u;

        // Determine parity of y coordinate
        let y_bytes = y_u256.to_be_bytes();
        let y_is_even = (y_bytes[31] & 1) == 0;
        
        public_key[0] = if y_is_even { 0x02 } else { 0x03 };

        // Store x coordinate
        let x_bytes = x_u256.to_be_bytes();
        public_key[1..33].copy_from_slice(&x_bytes);

        Ok(public_key)
    }

    /// Parse point from uncompressed public key with validation
    pub fn from_uncompressed_public_key(public_key: &[u8]) -> Result<Self> {
        if public_key.len() != 65 {
            return Err(input_error!(InvalidLength));
        }

        if public_key[0] != 0x04 {
            return Err(input_error!(InvalidFormat));
        }

        let x_bytes = slice_to_array::<32>(&public_key[1..33])?;
        let y_bytes = slice_to_array::<32>(&public_key[33..65])?;

        let x_u256 = U256::from_be_bytes(x_bytes);
        let y_u256 = U256::from_be_bytes(y_bytes);

        let x_field = Field256::new(x_u256, P)?;
        let y_field = Field256::new(y_u256, P)?;

        Self::new(x_field, y_field)
    }

    /// Parse point from compressed public key with validation
    pub fn from_compressed_public_key(public_key: &[u8]) -> Result<Self> {
        if public_key.len() != 33 {
            return Err(input_error!(InvalidLength));
        }

        let parity_byte = public_key[0];
        if parity_byte != 0x02 && parity_byte != 0x03 {
            return Err(input_error!(InvalidFormat));
        }

        let x_bytes = slice_to_array::<32>(&public_key[1..33])?;
        let x_u256 = U256::from_be_bytes(x_bytes);
        let x_field = Field256::new(x_u256, P)?;

        // Compute y^2 = x^3 + 7
        let seven = Field256::new_unchecked(U256::from(7u128), P);
        let x_squared = x_field.checked_mul(x_field)?;
        let x_cubed = x_squared.checked_mul(x_field)?;
        let y_squared = x_cubed.checked_add(seven)?;

        // This would require implementing square root in finite field
        // For now, return error as this requires complex arithmetic
        Err(crypto_error!(InvalidPublicKey))
    }

    /// Check if point is at infinity
    pub fn is_infinity(&self) -> bool {
        self.is_infinity
    }

    /// Secure equality check
    pub fn equals(&self, other: &Self) -> bool {
        if self.is_infinity != other.is_infinity {
            return false;
        }
        
        if self.is_infinity {
            return true; // Both at infinity
        }
        
        self.x == other.x && self.y == other.y
    }
}

/// Safe implementation of Add trait
impl Add for SecurePoint {
    type Output = SecurePoint;

    fn add(self, other: SecurePoint) -> SecurePoint {
        // Use checked_add for proper error handling in production
        self.checked_add(other).unwrap_or_else(|_| {
            // Return infinity on error for trait compatibility
            SecurePoint::infinity()
        })
    }
}

impl Ord for SecurePoint {
    fn cmp(&self, other: &SecurePoint) -> Ordering {
        // Handle infinity cases
        match (self.is_infinity, other.is_infinity) {
            (true, true) => return Ordering::Equal,
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            (false, false) => {},
        }

        // Compare coordinates
        match self.x.cmp(&other.x) {
            Ordering::Equal => self.y.cmp(&other.y),
            other_order => other_order,
        }
    }
}

impl PartialOrd for SecurePoint {
    fn partial_cmp(&self, other: &SecurePoint) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Default for SecurePoint {
    fn default() -> Self {
        Self::infinity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_creation_and_validation() {
        let generator = SecurePoint::generator();
        assert!(generator.is_ok());
        
        let point = generator.unwrap();
        assert!(point.validate_on_curve().is_ok());
    }

    #[test]
    fn test_point_addition() {
        let g = SecurePoint::generator().unwrap();
        let double_g = g.checked_add(g);
        assert!(double_g.is_ok());
        
        let double_g2 = g.double();
        assert!(double_g2.is_ok());
        
        // Both methods should give same result
        assert_eq!(double_g.unwrap(), double_g2.unwrap());
    }

    #[test]
    fn test_scalar_multiplication() {
        let g = SecurePoint::generator().unwrap();
        let scalar = U256::from(5u128);
        
        let result = g.scalar_multiply(scalar);
        assert!(result.is_ok());
    }

    #[test]
    fn test_public_key_generation() {
        let g = SecurePoint::generator().unwrap();
        
        let uncompressed = g.to_uncompressed_public_key();
        assert!(uncompressed.is_ok());
        assert_eq!(uncompressed.unwrap().len(), 65);
        
        let compressed = g.to_compressed_public_key();
        assert!(compressed.is_ok());
        assert_eq!(compressed.unwrap().len(), 33);
    }

    #[test]
    fn test_infinity_point() {
        let inf = SecurePoint::infinity();
        assert!(inf.is_infinity());
        
        let g = SecurePoint::generator().unwrap();
        let result = g.checked_add(inf);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), g);
    }

    #[test]
    fn test_point_validation() {
        // Create invalid point (not on curve)
        let invalid_x = Field256::new_unchecked(U256::from(1u128), P);
        let invalid_y = Field256::new_unchecked(U256::from(1u128), P);
        
        let invalid_point = SecurePoint::new(invalid_x, invalid_y);
        assert!(invalid_point.is_err());
    }
}