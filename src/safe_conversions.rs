//! Safe type conversions and array operations
//!
//! This module provides memory-safe alternatives to unsafe operations
//! like transmute, ensuring bounds checking and type safety.

#![no_std]

use crate::error::{BitcoinError, Result, MemoryError, InputError};
use crate::{memory_error, input_error};

/// Safe conversion from array to different sized array with bounds checking
pub fn safe_array_convert<const FROM: usize, const TO: usize>(
    source: [u8; FROM],
) -> Result<[u8; TO]> {
    if FROM != TO {
        return Err(memory_error!(InvalidBounds));
    }
    
    let mut result = [0u8; TO];
    result.copy_from_slice(&source[..TO.min(FROM)]);
    Ok(result)
}

/// Safe conversion from u32 array to bytes with proper endianness
pub fn u32_array_to_bytes_20(source: [u32; 5]) -> [u8; 20] {
    let mut result = [0u8; 20];
    for (i, &value) in source.iter().enumerate() {
        let bytes = value.to_be_bytes();
        result[i * 4..(i + 1) * 4].copy_from_slice(&bytes);
    }
    result
}

/// Safe conversion from u32 array to bytes with proper endianness (32 bytes)
pub fn u32_array_to_bytes_32(source: [u32; 8]) -> [u8; 32] {
    let mut result = [0u8; 32];
    for (i, &value) in source.iter().enumerate() {
        let bytes = value.to_be_bytes();
        result[i * 4..(i + 1) * 4].copy_from_slice(&bytes);
    }
    result
}

/// Safe conversion from bytes to u32 array with bounds checking
pub fn bytes_to_u32_array<const N: usize>(source: &[u8]) -> Result<[u32; N]> {
    if source.len() != N * 4 {
        return Err(input_error!(InvalidLength));
    }
    
    let mut result = [0u32; N];
    for i in 0..N {
        let start = i * 4;
        let end = start + 4;
        if end > source.len() {
            return Err(memory_error!(InvalidBounds));
        }
        
        let bytes: [u8; 4] = [
            source[start],
            source[start + 1], 
            source[start + 2],
            source[start + 3],
        ];
        result[i] = u32::from_be_bytes(bytes);
    }
    Ok(result)
}

/// Safe slice to fixed array conversion with bounds checking
pub fn slice_to_array<const N: usize>(source: &[u8]) -> Result<[u8; N]> {
    if source.len() != N {
        return Err(input_error!(InvalidLength));
    }
    
    let mut result = [0u8; N];
    result.copy_from_slice(source);
    Ok(result)
}

/// Safe conversion from slice to array with exact length check
pub fn checked_slice_to_array<const N: usize>(source: &[u8], start: usize) -> Result<[u8; N]> {
    if start + N > source.len() {
        return Err(memory_error!(InvalidBounds));
    }
    
    let mut result = [0u8; N];
    result.copy_from_slice(&source[start..start + N]);
    Ok(result)
}

/// Safe base58 encoding with proper bounds checking (simplified version)
pub fn encode_base58_simple(input: &[u8]) -> Result<[u8; 66]> {
    if input.len() > 32 {
        return Err(input_error!(InvalidLength));
    }
    
    // Simple implementation - return the input as hex for now
    // A full base58 implementation would be more complex
    let mut result = [0u8; 66];
    let hex_chars = b"0123456789abcdef";
    
    let mut output_pos = 0;
    for &byte in input {
        if output_pos + 1 < 66 {
            result[output_pos] = hex_chars[(byte >> 4) as usize];
            result[output_pos + 1] = hex_chars[(byte & 0xf) as usize];
            output_pos += 2;
        }
    }
    
    Ok(result)
}


/// Safe memory zeroing to prevent information leakage
pub fn secure_zero(data: &mut [u8]) {
    for byte in data.iter_mut() {
        *byte = 0;
    }
    // Compiler fence to prevent optimization
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Safe array bounds checking
pub fn check_bounds(index: usize, len: usize) -> Result<()> {
    if index >= len {
        Err(memory_error!(InvalidBounds))
    } else {
        Ok(())
    }
}

/// Safe slice bounds checking
pub fn check_slice_bounds(start: usize, end: usize, len: usize) -> Result<()> {
    if start > end || end > len {
        Err(memory_error!(InvalidBounds))
    } else {
        Ok(())
    }
}