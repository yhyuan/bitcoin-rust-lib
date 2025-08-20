//! Comprehensive security tests for hardened Bitcoin library
//!
//! This module validates that all security improvements are working correctly
//! and that the library is protected against various attack vectors.

#![cfg(test)]

use crate::error::{BitcoinError, CryptographicError, MemoryError, ScriptError};
use crate::field256_secure::Field256;
use crate::point_secure::SecurePoint;
use crate::safe_conversions::*;
use crate::script_secure::ScriptExecutor;
use crate::stack_secure::SecureStack;
use crate::u256::{P, U256};

/// Test that stack overflow protection works
#[test]
fn test_stack_overflow_protection() {
    let mut stack = SecureStack::new();

    // Try to fill stack beyond capacity
    let mut success_count = 0;
    for i in 0..2000 {
        let data = [i as u8; 1];
        if stack.push(&data).is_ok() {
            success_count += 1;
        } else {
            break;
        }
    }

    // Should hit limit before 2000
    assert!(success_count < 2000);
    assert!(success_count > 0);
}

/// Test that memory bomb protection works
#[test]
fn test_memory_bomb_protection() {
    let mut stack = SecureStack::new();

    // Try to push very large item
    let large_data = [0u8; 1000];
    let result = stack.push(&large_data);
    assert!(result.is_err());

    if let Err(BitcoinError::Memory(MemoryError::BufferTooLarge)) = result {
        // Expected error
    } else {
        panic!("Expected BufferTooLarge error");
    }
}

/// Test script execution limits
#[test]
fn test_script_execution_limits() {
    let mut executor = ScriptExecutor::new();

    // Test script size limit
    let oversized_script = [0x61u8; 20000]; // Many NOPs
    let result = executor.execute(&oversized_script);
    assert!(result.is_err());

    // Test operation count limit
    executor.reset();
    let many_ops_script = [0x61u8; 300]; // Too many NOPs
    let result = executor.execute(&many_ops_script);
    assert!(result.is_err());
}

/// Test that invalid opcodes are rejected
#[test]
fn test_invalid_opcode_rejection() {
    let mut executor = ScriptExecutor::new();

    // Script with invalid opcode
    let invalid_script = [0xFF]; // Invalid opcode
    let result = executor.execute(&invalid_script);
    assert!(result.is_err());

    if let Err(BitcoinError::Script(ScriptError::InvalidOpcode)) = result {
        // Expected error
    } else {
        panic!("Expected InvalidOpcode error");
    }
}

/// Test bounds checking in script execution
#[test]
fn test_script_bounds_checking() {
    let mut executor = ScriptExecutor::new();

    // Script that tries to push more data than available
    let malformed_script = [0x10]; // Push 16 bytes, but only 1 byte total
    let result = executor.execute(&malformed_script);
    assert!(result.is_err());
}

/// Test field arithmetic error handling
#[test]
fn test_field_arithmetic_safety() {
    // Test division by zero protection
    let a = Field256::new_unchecked(U256::from(5u128), P);
    let zero = Field256::zero(P);

    let result = a.checked_div(zero);
    assert!(result.is_err());
}

/// Test point validation
#[test]
fn test_curve_point_validation() {
    // Try to create invalid point (not on curve)
    let invalid_x = Field256::new_unchecked(U256::from(1u128), P);
    let invalid_y = Field256::new_unchecked(U256::from(1u128), P);

    let result = SecurePoint::new(invalid_x, invalid_y);
    assert!(result.is_err());

    if let Err(BitcoinError::Cryptographic(CryptographicError::InvalidCurvePoint)) = result {
        // Expected error
    } else {
        panic!("Expected InvalidCurvePoint error");
    }
}

/// Test safe conversions
#[test]
fn test_safe_conversions() {
    // Test bounds checking
    let result = check_bounds(10, 5);
    assert!(result.is_err());

    let result = check_bounds(3, 5);
    assert!(result.is_ok());

    // Test slice bounds checking
    let result = check_slice_bounds(5, 10, 8);
    assert!(result.is_err());

    let result = check_slice_bounds(2, 5, 10);
    assert!(result.is_ok());
}

/// Test that public key generation is secure
#[test]
fn test_secure_public_key_generation() {
    let generator = SecurePoint::generator();
    assert!(generator.is_ok());

    let point = generator.unwrap();

    // Test uncompressed public key
    let uncompressed = point.to_uncompressed_public_key();
    assert!(uncompressed.is_ok());

    let pubkey = uncompressed.unwrap();
    assert_eq!(pubkey.len(), 65);
    assert_eq!(pubkey[0], 0x04); // Uncompressed indicator

    // Test compressed public key
    let compressed = point.to_compressed_public_key();
    assert!(compressed.is_ok());

    let compressed_pubkey = compressed.unwrap();
    assert_eq!(compressed_pubkey.len(), 33);
    assert!(compressed_pubkey[0] == 0x02 || compressed_pubkey[0] == 0x03);
}

/// Test memory zeroing
#[test]
fn test_secure_memory_zeroing() {
    let mut sensitive_data = [0x42u8; 32];

    // Verify data is set
    assert_eq!(sensitive_data[0], 0x42);

    // Zero it securely
    secure_zero(&mut sensitive_data);

    // Verify it's zeroed
    for &byte in &sensitive_data {
        assert_eq!(byte, 0);
    }
}

/// Test error type completeness
#[test]
fn test_error_types_coverage() {
    // Test each error type can be created
    let arithmetic_error = BitcoinError::Arithmetic(crate::error::ArithmeticError::DivisionByZero);
    let crypto_error = BitcoinError::Cryptographic(CryptographicError::InvalidCurvePoint);
    let script_error = BitcoinError::Script(ScriptError::StackOverflow);
    let memory_error = BitcoinError::Memory(MemoryError::BufferTooLarge);
    let input_error = BitcoinError::Input(crate::error::InputError::InvalidLength);

    // Just verify they're different types
    assert!(matches!(arithmetic_error, BitcoinError::Arithmetic(_)));
    assert!(matches!(crypto_error, BitcoinError::Cryptographic(_)));
    assert!(matches!(script_error, BitcoinError::Script(_)));
    assert!(matches!(memory_error, BitcoinError::Memory(_)));
    assert!(matches!(input_error, BitcoinError::Input(_)));
}

/// Integration test: Complete secure script execution
#[test]
fn test_secure_script_integration() {
    let mut executor = ScriptExecutor::new();

    // Test valid script: Push 1, Push 1, Add, should result in 2
    let script = [0x51, 0x51, 0x93]; // OP_1, OP_1, OP_ADD
    let result = executor.execute(&script);
    assert!(result.is_ok());
    assert!(result.unwrap()); // Should be true (non-zero result)

    // Test that stack is properly managed
    executor.reset();
    assert_eq!(executor.get_stack_size(), 0);
}

/// Test resource limit enforcement
#[test]
fn test_resource_limits() {
    let mut stack = SecureStack::new();

    // Test total memory limit
    let mut items_added = 0;

    loop {
        let data = [0u8; 500];
        if stack.push(&data).is_ok() {
            items_added += 1;
        } else {
            break;
        }
    }

    // Should hit memory limit before adding too many items
    assert!(items_added > 0);
    assert!(items_added < 100); // Should be limited
}

/// Test that all major attack vectors are mitigated
#[test]
fn test_attack_vector_mitigation() {
    // Buffer overflow protection
    test_stack_overflow_protection();

    // Memory bomb protection
    test_memory_bomb_protection();

    // Script execution limits
    test_script_execution_limits();

    // Input validation
    test_invalid_opcode_rejection();
    test_script_bounds_checking();

    // Cryptographic validation
    test_curve_point_validation();
    test_field_arithmetic_safety();

    // Memory safety
    test_secure_memory_zeroing();

    // All attack vector mitigations verified
}
