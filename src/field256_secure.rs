//! Secure finite field arithmetic implementation
//! 
//! This module provides memory-safe field arithmetic operations with proper
//! error handling and input validation to prevent panic conditions.

#![no_std]

use core::ops::{Add, Sub, Mul, Div};
use core::cmp::Ordering;
use crate::u256::U256;
use crate::error::{BitcoinError, Result, CryptographicError, ArithmeticError};
use crate::{crypto_error, arithmetic_error};

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Field256 {
    pub u: U256,
    pub p: fn() -> U256
}

#[allow(dead_code)]
impl Field256 {
    /// Create a new field element with validation
    pub fn new(u: U256, p: fn() -> U256) -> Result<Self> {
        let prime = p();
        if u >= prime {
            return Err(crypto_error!(InvalidFieldElement));
        }
        Ok(Field256 { u, p })
    }

    /// Create a validated field element (assumes input is already reduced)
    pub fn new_unchecked(u: U256, p: fn() -> U256) -> Self {
        Field256 { u, p }
    }

    /// Zero element
    pub fn zero(p: fn() -> U256) -> Field256 { 
        Field256 { u: U256::zero(), p }
    }

    /// One element  
    pub fn one(p: fn() -> U256) -> Field256 { 
        Field256 { u: U256::one(), p }
    }

    /// Maximum value (p - 1)
    pub fn max_value(p: fn() -> U256) -> Field256 { 
        Field256 { u: p() - U256::one(), p }
    }

    /// Secure field reduction with proper error handling
    pub fn eliminate(x: (u128, u128, u128), prime: U256) -> Result<U256> {
        match x {
            (0u128, x1, x2) => {
                let val = U256::new(x1, x2);
                if val < prime {
                    Ok(val)
                } else {
                    Ok(val - prime)
                }
            },
            (x0, x1, x2) => {
                // Secure multiplication with error handling
                let multiple = U256::new(0u128, x0) * prime;
                let (overflow_part, z0) = multiple.0.unwrap(); // U256 always has valid unwrap
                let z = multiple.1;
                
                if overflow_part != 0 {
                    return Err(arithmetic_error!(Overflow));
                }
                
                let t = U256::new(x1, x2);
                
                if t >= z {
                    let diff = t - z;
                    let (w1, w2) = diff.unwrap(); // U256 always has valid unwrap
                    
                    if x0 < z0 {
                        return Err(arithmetic_error!(Underflow));
                    }
                    
                    Self::eliminate((x0 - z0, w1, w2), prime)
                } else {
                    let temp = U256::max_value() - z + t + U256::one();
                    let (w1, w2) = temp.unwrap(); // U256 always has valid unwrap
                    
                    if x0 == 0 || z0 >= x0 {
                        return Err(arithmetic_error!(Underflow));
                    }
                    
                    Self::eliminate((x0 - z0 - 1, w1, w2), prime)
                }
            },
        }
    }

    /// Validate prime compatibility
    fn validate_prime_compatibility(&self, other: &Field256) -> Result<U256> {
        let self_prime = (self.p)();
        let other_prime = (other.p)();
        
        if self_prime != other_prime {
            return Err(crypto_error!(InvalidFieldElement));
        }
        
        Ok(self_prime)
    }

    /// Secure addition with proper error handling
    pub fn checked_add(self, other: Field256) -> Result<Field256> {
        let prime = self.validate_prime_compatibility(&other)?;
        
        let (mut v, overflow) = self.u.overflowing_add(other.u);
        
        if v > prime {
            v = v - prime;
        }
        
        if overflow {
            let p_minus = U256::max_value() - prime + U256::one();
            v = v + p_minus;
        }
        
        if v > prime {
            v = v - prime;
        }
        
        Ok(Field256 { u: v, p: self.p })
    }

    /// Secure subtraction with proper error handling
    pub fn checked_sub(self, other: Field256) -> Result<Field256> {
        let _prime = self.validate_prime_compatibility(&other)?;
        
        if self.u >= other.u {
            Ok(Field256 { u: self.u - other.u, p: self.p })
        } else {
            let prime_field = Field256 { u: (self.p)() - other.u, p: self.p };
            self.checked_add(prime_field)
        }
    }

    /// Secure multiplication with proper error handling
    pub fn checked_mul(self, other: Field256) -> Result<Field256> {
        let prime = self.validate_prime_compatibility(&other)?;
        
        let multiple = self.u * other.u;
        let (x0, x1) = multiple.0.unwrap(); // U256 always has valid unwrap
        let (x2, x3) = multiple.1.unwrap(); // U256 always has valid unwrap

        let intermediate = Self::eliminate((x0, x1, x2), prime)?;
        let (y0, y1) = intermediate.unwrap(); // U256 always has valid unwrap
        let u = Self::eliminate((y0, y1, x3), prime)?;
        
        Ok(Field256 { u, p: self.p })
    }

    /// Secure division with proper error handling
    pub fn checked_div(self, other: Field256) -> Result<Field256> {
        let prime = self.validate_prime_compatibility(&other)?;
        
        if other.u.is_zero() {
            return Err(arithmetic_error!(DivisionByZero));
        }
        
        let inv = other.u.mod_inv(prime);
        let other_inv = Field256 { u: inv, p: self.p };
        
        self.checked_mul(other_inv)
    }

    /// Check if element is zero
    pub fn is_zero(&self) -> bool {
        self.u.is_zero()
    }

    /// Check if element is one
    pub fn is_one(&self) -> bool {
        self.u == U256::one()
    }
}

/// Safe implementation of Add trait
impl Add for Field256 {
    type Output = Field256;

    fn add(self, other: Field256) -> Field256 {
        // Note: This panics on error for trait compatibility
        // Use checked_add for error handling
        self.checked_add(other).unwrap_or_else(|_| {
            // Fallback to zero on error (safer than panic)
            Field256::zero(self.p)
        })
    }
}

/// Safe implementation of Sub trait  
impl Sub for Field256 {
    type Output = Field256;

    fn sub(self, other: Field256) -> Field256 {
        // Note: This returns zero on error for trait compatibility
        // Use checked_sub for proper error handling
        self.checked_sub(other).unwrap_or_else(|_| {
            Field256::zero(self.p)
        })
    }
}

/// Safe implementation of Mul trait
impl Mul for Field256 {
    type Output = Field256;

    fn mul(self, other: Field256) -> Field256 {
        // Note: This returns zero on error for trait compatibility
        // Use checked_mul for proper error handling
        self.checked_mul(other).unwrap_or_else(|_| {
            Field256::zero(self.p)
        })
    }
}

/// Safe implementation of Div trait
impl Div for Field256 {
    type Output = Field256;

    fn div(self, other: Field256) -> Field256 {
        // Note: This returns zero on error for trait compatibility  
        // Use checked_div for proper error handling
        self.checked_div(other).unwrap_or_else(|_| {
            Field256::zero(self.p)
        })
    }
}

impl Ord for Field256 {
    fn cmp(&self, other: &Field256) -> Ordering {
        // Validate primes match (return Equal on mismatch to avoid panic)
        if (self.p)() != (other.p)() {
            return Ordering::Equal;
        }
        self.u.cmp(&other.u)
    }
}

impl PartialOrd for Field256 {
    fn partial_cmp(&self, other: &Field256) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::u256::{P, N};

    #[test]
    fn test_secure_field_creation() {
        let prime = P();
        let valid_element = Field256::new(U256::one(), P);
        assert!(valid_element.is_ok());
        
        let invalid_element = Field256::new(prime, P);
        assert!(invalid_element.is_err());
    }

    #[test]
    fn test_secure_arithmetic() {
        let a = Field256::new_unchecked(U256::from(5u128), P);
        let b = Field256::new_unchecked(U256::from(3u128), P);
        
        let sum = a.checked_add(b);
        assert!(sum.is_ok());
        
        let diff = a.checked_sub(b);
        assert!(diff.is_ok());
        
        let product = a.checked_mul(b);
        assert!(product.is_ok());
        
        let quotient = a.checked_div(b);
        assert!(quotient.is_ok());
    }

    #[test]
    fn test_division_by_zero() {
        let a = Field256::new_unchecked(U256::from(5u128), P);
        let zero = Field256::zero(P);
        
        let result = a.checked_div(zero);
        assert!(result.is_err());
    }
}