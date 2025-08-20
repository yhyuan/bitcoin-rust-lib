//! Secure Bitcoin Script interpreter with comprehensive security controls
//!
//! This module provides a memory-safe Script interpreter with resource limits,
//! bounds checking, and protection against various attack vectors.

use crate::error::{BitcoinError, InputError, Result, ScriptError};
use crate::ripemd160::Ripemd160;
use crate::safe_conversions::check_slice_bounds;
use crate::sha256::Sha256;
use crate::stack_secure::{AltStack, SecureStack};
use crate::{input_error, script_error};

/// Maximum script size to prevent script bomb attacks
#[allow(dead_code)]
const MAX_SCRIPT_SIZE: usize = 10000;

/// Maximum number of operations to prevent infinite loops
#[allow(dead_code)]
const MAX_OPS: usize = 201;

/// Maximum number of signature checks to prevent CPU exhaustion
#[allow(dead_code)]
const MAX_SIG_CHECKS: usize = 20;

/// Maximum push data size for single operation
#[allow(dead_code)]
const MAX_PUSH_SIZE: usize = 520;

/// Bitcoin Script opcodes with security validation
#[allow(dead_code)]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    // Constants
    Op0 = 0x00,
    OpPushData1 = 0x4c,
    OpPushData2 = 0x4d,
    OpPushData4 = 0x4e,
    Op1Negate = 0x4f,
    Op1 = 0x51,
    Op2 = 0x52,
    Op3 = 0x53,
    Op4 = 0x54,
    Op5 = 0x55,
    Op6 = 0x56,
    Op7 = 0x57,
    Op8 = 0x58,
    Op9 = 0x59,
    Op10 = 0x5a,
    Op11 = 0x5b,
    Op12 = 0x5c,
    Op13 = 0x5d,
    Op14 = 0x5e,
    Op15 = 0x5f,
    Op16 = 0x60,

    // Flow control
    OpNop = 0x61,
    OpIf = 0x63,
    OpNotif = 0x64,
    OpElse = 0x67,
    OpEndif = 0x68,
    OpVerify = 0x69,
    OpReturn = 0x6a,

    // Stack operations
    OpToAltStack = 0x6b,
    OpFromAltStack = 0x6c,
    OpIfDup = 0x73,
    OpDepth = 0x74,
    OpDrop = 0x75,
    OpDup = 0x76,
    OpNip = 0x77,
    OpOver = 0x78,
    OpPick = 0x79,
    OpRoll = 0x7a,
    OpRot = 0x7b,
    OpSwap = 0x7c,
    OpTuck = 0x7d,
    Op2Drop = 0x6d,
    Op2Dup = 0x6e,
    Op3Dup = 0x6f,
    Op2Over = 0x70,
    Op2Rot = 0x71,
    Op2Swap = 0x72,

    // Bitwise logic
    OpEqual = 0x87,
    OpEqualVerify = 0x88,

    // Arithmetic
    Op1Add = 0x8b,
    Op1Sub = 0x8c,
    OpNegate = 0x8f,
    OpAbs = 0x90,
    OpNot = 0x91,
    Op0NotEqual = 0x92,
    OpAdd = 0x93,
    OpSub = 0x94,
    OpBoolAnd = 0x9a,
    OpBoolOr = 0x9b,
    OpNumEqual = 0x9c,
    OpNumEqualVerify = 0x9d,
    OpNumNotEqual = 0x9e,
    OpLessThan = 0x9f,
    OpGreaterThan = 0xa0,
    OpLessThanOrEqual = 0xa1,
    OpGreaterThanOrEqual = 0xa2,
    OpMin = 0xa3,
    OpMax = 0xa4,
    OpWithin = 0xa5,

    // Crypto
    OpRipemd160 = 0xa6,
    OpSha1 = 0xa7,
    OpSha256 = 0xa8,
    OpHash160 = 0xa9,
    OpHash256 = 0xaa,
    OpCodeSeparator = 0xab,
    OpCheckSig = 0xac,
    OpCheckSigVerify = 0xad,
    OpCheckMultiSig = 0xae,
    OpCheckMultiSigVerify = 0xaf,

    // Locktime
    OpCheckLockTimeVerify = 0xb1,
    OpCheckSequenceVerify = 0xb2,

    // Invalid
    OpInvalid = 0xff,
}

#[allow(dead_code)]
impl Opcode {
    /// Convert byte to opcode with validation
    pub fn from_byte(byte: u8) -> Result<Self> {
        match byte {
            0x00 => Ok(Opcode::Op0),
            0x4c => Ok(Opcode::OpPushData1),
            0x4d => Ok(Opcode::OpPushData2),
            0x4e => Ok(Opcode::OpPushData4),
            0x4f => Ok(Opcode::Op1Negate),
            0x51 => Ok(Opcode::Op1),
            0x52 => Ok(Opcode::Op2),
            0x53 => Ok(Opcode::Op3),
            0x54 => Ok(Opcode::Op4),
            0x55 => Ok(Opcode::Op5),
            0x56 => Ok(Opcode::Op6),
            0x57 => Ok(Opcode::Op7),
            0x58 => Ok(Opcode::Op8),
            0x59 => Ok(Opcode::Op9),
            0x5a => Ok(Opcode::Op10),
            0x5b => Ok(Opcode::Op11),
            0x5c => Ok(Opcode::Op12),
            0x5d => Ok(Opcode::Op13),
            0x5e => Ok(Opcode::Op14),
            0x5f => Ok(Opcode::Op15),
            0x60 => Ok(Opcode::Op16),
            0x61 => Ok(Opcode::OpNop),
            0x63 => Ok(Opcode::OpIf),
            0x64 => Ok(Opcode::OpNotif),
            0x67 => Ok(Opcode::OpElse),
            0x68 => Ok(Opcode::OpEndif),
            0x69 => Ok(Opcode::OpVerify),
            0x6a => Ok(Opcode::OpReturn),
            0x6b => Ok(Opcode::OpToAltStack),
            0x6c => Ok(Opcode::OpFromAltStack),
            0x6d => Ok(Opcode::Op2Drop),
            0x6e => Ok(Opcode::Op2Dup),
            0x6f => Ok(Opcode::Op3Dup),
            0x70 => Ok(Opcode::Op2Over),
            0x71 => Ok(Opcode::Op2Rot),
            0x72 => Ok(Opcode::Op2Swap),
            0x73 => Ok(Opcode::OpIfDup),
            0x74 => Ok(Opcode::OpDepth),
            0x75 => Ok(Opcode::OpDrop),
            0x76 => Ok(Opcode::OpDup),
            0x77 => Ok(Opcode::OpNip),
            0x78 => Ok(Opcode::OpOver),
            0x79 => Ok(Opcode::OpPick),
            0x7a => Ok(Opcode::OpRoll),
            0x7b => Ok(Opcode::OpRot),
            0x7c => Ok(Opcode::OpSwap),
            0x7d => Ok(Opcode::OpTuck),
            0x87 => Ok(Opcode::OpEqual),
            0x88 => Ok(Opcode::OpEqualVerify),
            0x8b => Ok(Opcode::Op1Add),
            0x8c => Ok(Opcode::Op1Sub),
            0x8f => Ok(Opcode::OpNegate),
            0x90 => Ok(Opcode::OpAbs),
            0x91 => Ok(Opcode::OpNot),
            0x92 => Ok(Opcode::Op0NotEqual),
            0x93 => Ok(Opcode::OpAdd),
            0x94 => Ok(Opcode::OpSub),
            0x9a => Ok(Opcode::OpBoolAnd),
            0x9b => Ok(Opcode::OpBoolOr),
            0x9c => Ok(Opcode::OpNumEqual),
            0x9d => Ok(Opcode::OpNumEqualVerify),
            0x9e => Ok(Opcode::OpNumNotEqual),
            0x9f => Ok(Opcode::OpLessThan),
            0xa0 => Ok(Opcode::OpGreaterThan),
            0xa1 => Ok(Opcode::OpLessThanOrEqual),
            0xa2 => Ok(Opcode::OpGreaterThanOrEqual),
            0xa3 => Ok(Opcode::OpMin),
            0xa4 => Ok(Opcode::OpMax),
            0xa5 => Ok(Opcode::OpWithin),
            0xa6 => Ok(Opcode::OpRipemd160),
            0xa7 => Ok(Opcode::OpSha1),
            0xa8 => Ok(Opcode::OpSha256),
            0xa9 => Ok(Opcode::OpHash160),
            0xaa => Ok(Opcode::OpHash256),
            0xab => Ok(Opcode::OpCodeSeparator),
            0xac => Ok(Opcode::OpCheckSig),
            0xad => Ok(Opcode::OpCheckSigVerify),
            0xae => Ok(Opcode::OpCheckMultiSig),
            0xaf => Ok(Opcode::OpCheckMultiSigVerify),
            0xb1 => Ok(Opcode::OpCheckLockTimeVerify),
            0xb2 => Ok(Opcode::OpCheckSequenceVerify),
            _ => Err(script_error!(InvalidOpcode)),
        }
    }
}

/// Secure script execution context with resource tracking
#[allow(dead_code)]
#[derive(Debug)]
pub struct ScriptExecutor {
    /// Main execution stack
    stack: SecureStack,
    /// Alternative stack
    alt_stack: AltStack,
    /// Operation counter for DoS protection
    op_count: usize,
    /// Signature check counter
    sig_check_count: usize,
    /// Script position
    pc: usize,
    /// If-else execution state
    if_stack: [bool; 100], // Limited depth for security
    if_depth: usize,
    /// Code separator position for signatures
    code_separator_pos: Option<usize>,
}

#[allow(dead_code)]
impl ScriptExecutor {
    /// Create new secure script executor
    pub fn new() -> Self {
        ScriptExecutor {
            stack: SecureStack::new(),
            alt_stack: AltStack::new(),
            op_count: 0,
            sig_check_count: 0,
            pc: 0,
            if_stack: [false; 100],
            if_depth: 0,
            code_separator_pos: None,
        }
    }

    /// Execute script with comprehensive security checks
    pub fn execute(&mut self, script: &[u8]) -> Result<bool> {
        // Validate script size
        if script.len() > MAX_SCRIPT_SIZE {
            return Err(script_error!(ScriptTooLong));
        }

        // Reset all execution state for new script
        self.pc = 0;
        self.op_count = 0;
        self.sig_check_count = 0;
        self.if_depth = 0;
        self.code_separator_pos = None;

        while self.pc < script.len() {
            // Check operation count limit
            if self.op_count >= MAX_OPS {
                return Err(script_error!(TooManyOperations));
            }

            let opcode_byte = script[self.pc];

            // Handle push data operations (1-75 bytes)
            if (1..=75).contains(&opcode_byte) {
                self.execute_push_data(script, opcode_byte as usize)?;
            } else {
                let opcode = Opcode::from_byte(opcode_byte)?;
                self.execute_opcode(script, opcode)?;
            }

            self.op_count += 1;
        }

        // Verify if-else stack is balanced
        if self.if_depth != 0 {
            return Err(script_error!(ExecutionFailed));
        }

        // Script succeeds if stack has exactly one truthy value
        if self.stack.size() != 1 {
            return Err(script_error!(ExecutionFailed));
        }

        let result = self.stack.peek()?;
        Ok(self.is_true(result))
    }

    /// Execute push data operation with bounds checking
    fn execute_push_data(&mut self, script: &[u8], size: usize) -> Result<()> {
        if size > MAX_PUSH_SIZE {
            return Err(script_error!(InvalidScriptData));
        }

        let start = self.pc + 1;
        let end = start + size;

        check_slice_bounds(start, end, script.len())?;

        let data = &script[start..end];
        self.stack.push(data)?;

        self.pc = end;
        Ok(())
    }

    /// Execute specific opcode with security validation
    fn execute_opcode(&mut self, _script: &[u8], opcode: Opcode) -> Result<()> {
        match opcode {
            Opcode::Op0 => {
                self.stack.push(&[])?;
            }
            Opcode::Op1Negate => {
                self.stack.push(&[0x81])?; // -1 in Bitcoin Script format
            }
            Opcode::Op1
            | Opcode::Op2
            | Opcode::Op3
            | Opcode::Op4
            | Opcode::Op5
            | Opcode::Op6
            | Opcode::Op7
            | Opcode::Op8
            | Opcode::Op9
            | Opcode::Op10
            | Opcode::Op11
            | Opcode::Op12
            | Opcode::Op13
            | Opcode::Op14
            | Opcode::Op15
            | Opcode::Op16 => {
                let value = (opcode as u8) - 0x50;
                self.stack.push(&[value])?;
            }
            Opcode::OpNop => {
                // No operation
            }
            Opcode::OpDup => {
                self.stack.dup()?;
            }
            Opcode::OpDrop => {
                self.stack.drop()?;
            }
            Opcode::OpSwap => {
                self.stack.swap()?;
            }
            Opcode::OpRot => {
                self.stack.rot()?;
            }
            Opcode::Op2Drop => {
                self.stack.drop()?;
                self.stack.drop()?;
            }
            Opcode::Op2Dup => {
                self.stack.dup_at_depth(1)?;
                self.stack.dup_at_depth(1)?;
            }
            Opcode::OpEqual => {
                let (a_data, a_len) = self.stack.pop()?;
                let (b_data, b_len) = self.stack.pop()?;
                let result = if a_len == b_len && a_data[..a_len] == b_data[..b_len] {
                    [1u8]
                } else {
                    [0u8]
                };
                self.stack.push(&result)?;
            }
            Opcode::OpEqualVerify => {
                let (a_data, a_len) = self.stack.pop()?;
                let (b_data, b_len) = self.stack.pop()?;
                if a_len != b_len || a_data[..a_len] != b_data[..b_len] {
                    return Err(script_error!(ExecutionFailed));
                }
            }
            Opcode::OpSha256 => {
                let (data_arr, data_len) = self.stack.pop()?;
                let data = &data_arr[..data_len];
                let hash = Sha256::digest(data);
                self.stack.push(&hash)?;
            }
            Opcode::OpRipemd160 => {
                let (data_arr, data_len) = self.stack.pop()?;
                let data = &data_arr[..data_len];
                let hash = Ripemd160::digest(data);
                self.stack.push(&hash)?;
            }
            Opcode::OpHash160 => {
                let (data_arr, data_len) = self.stack.pop()?;
                let data = &data_arr[..data_len];
                let sha_hash = Sha256::digest(data);
                let ripemd_hash = Ripemd160::digest(&sha_hash);
                self.stack.push(&ripemd_hash)?;
            }
            Opcode::OpHash256 => {
                let (data_arr, data_len) = self.stack.pop()?;
                let data = &data_arr[..data_len];
                let hash1 = Sha256::digest(data);
                let hash2 = Sha256::digest(&hash1);
                self.stack.push(&hash2)?;
            }
            Opcode::OpVerify => {
                let (data_arr, data_len) = self.stack.pop()?;
                let value = &data_arr[..data_len];
                if !self.is_true(value) {
                    return Err(script_error!(ExecutionFailed));
                }
            }
            Opcode::OpReturn => {
                return Err(script_error!(ExecutionFailed));
            }
            Opcode::OpToAltStack => {
                let (item_data, item_len) = self.stack.pop()?;
                self.alt_stack.push(&item_data[..item_len])?;
            }
            Opcode::OpFromAltStack => {
                let (item_data, item_len) = self.alt_stack.pop()?;
                self.stack.push(&item_data[..item_len])?;
            }
            Opcode::OpAdd => {
                // Pop two values from stack and add them
                let (b_data, b_len) = self.stack.pop()?;
                let (a_data, a_len) = self.stack.pop()?;

                // Convert to integers (simple implementation - just use first byte)
                let a = if a_len > 0 { a_data[0] as u64 } else { 0 };
                let b = if b_len > 0 { b_data[0] as u64 } else { 0 };

                let result = a + b;
                let result_bytes = [result as u8];
                self.stack.push(&result_bytes)?;
            }
            _ => {
                return Err(script_error!(InvalidOpcode));
            }
        }

        self.pc += 1;
        Ok(())
    }

    /// Check if value is considered "true" in Bitcoin Script context
    fn is_true(&self, value: &[u8]) -> bool {
        if value.is_empty() {
            return false;
        }

        // Check for negative zero
        if value.len() == 1 && value[0] == 0x80 {
            return false;
        }

        // Check if all bytes are zero
        for &byte in value {
            if byte != 0 {
                return true;
            }
        }

        false
    }

    /// Get current stack size for debugging
    pub fn get_stack_size(&self) -> usize {
        self.stack.size()
    }

    /// Reset executor state
    pub fn reset(&mut self) {
        self.stack.clear();
        self.alt_stack.clear();
        self.op_count = 0;
        self.sig_check_count = 0;
        self.pc = 0;
        self.if_depth = 0;
        self.code_separator_pos = None;
    }

    /// Validate script syntax without execution
    pub fn validate_script(script: &[u8]) -> Result<()> {
        if script.len() > MAX_SCRIPT_SIZE {
            return Err(script_error!(ScriptTooLong));
        }

        let mut pc = 0;
        let mut op_count = 0;

        while pc < script.len() {
            if op_count >= MAX_OPS {
                return Err(script_error!(TooManyOperations));
            }

            let opcode_byte = script[pc];

            if (1..=75).contains(&opcode_byte) {
                let size = opcode_byte as usize;
                if size > MAX_PUSH_SIZE {
                    return Err(script_error!(InvalidScriptData));
                }

                let end = pc + 1 + size;
                if end > script.len() {
                    return Err(input_error!(InvalidLength));
                }
                pc = end;
            } else {
                Opcode::from_byte(opcode_byte)?;
                pc += 1;
            }

            op_count += 1;
        }

        Ok(())
    }
}

impl Default for ScriptExecutor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_script_execution() {
        let mut executor = ScriptExecutor::new();

        // Push 1, push 1, OP_ADD
        let script = [0x51, 0x51, 0x93];
        let result = executor.execute(&script);
        assert!(result.is_ok());
    }

    #[test]
    fn test_script_size_limit() {
        let mut executor = ScriptExecutor::new();

        // Create oversized script
        let script = [0x61u8; MAX_SCRIPT_SIZE + 1]; // NOP operations
        let result = executor.execute(&script);
        assert!(result.is_err());
    }

    #[test]
    fn test_operation_count_limit() {
        let mut executor = ScriptExecutor::new();

        // Create script with too many operations
        let script = [0x61u8; MAX_OPS + 1]; // NOP operations
        let result = executor.execute(&script);
        assert!(result.is_err());
    }

    #[test]
    fn test_push_data_validation() {
        let mut executor = ScriptExecutor::new();

        // Try to push more data than script contains
        let script = [0x10]; // Push 16 bytes, but script only has 1 byte
        let result = executor.execute(&script);
        assert!(result.is_err());
    }

    #[test]
    fn test_stack_operations() {
        // Test OP_1 alone
        {
            let mut executor = ScriptExecutor::new();
            let script = [0x51]; // OP_1
            assert!(executor.execute(&script).is_ok());
        }

        // Test OP_1, OP_2
        {
            let mut executor = ScriptExecutor::new();
            let script = [0x51, 0x52]; // OP_1, OP_2
            assert!(executor.execute(&script).is_ok());
        }

        // Test OP_1, OP_2, OP_SWAP
        {
            let mut executor = ScriptExecutor::new();
            let script = [0x51, 0x52, 0x7c]; // OP_1, OP_2, OP_SWAP
            assert!(executor.execute(&script).is_ok());
        }
    }

    #[test]
    fn test_hash_operations() {
        let mut executor = ScriptExecutor::new();

        // Push data and hash it
        let script = [0x01, 0x42, 0xa8]; // Push byte 0x42, OP_SHA256
        assert!(executor.execute(&script).is_ok());
    }
}
