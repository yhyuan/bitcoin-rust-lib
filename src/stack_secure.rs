//! Memory-safe stack implementation for Bitcoin Script execution
//!
//! This module provides a secure stack with bounds checking, resource limits,
//! and memory safety guarantees to prevent script execution attacks.

#![no_std]

use crate::error::{BitcoinError, Result, ScriptError, MemoryError};
use crate::{script_error, memory_error};

/// Maximum stack size to prevent memory exhaustion attacks
const MAX_STACK_SIZE: usize = 1000;

/// Maximum individual item size to prevent memory bombs
const MAX_ITEM_SIZE: usize = 520;

/// Maximum total memory usage for the stack
const MAX_TOTAL_MEMORY: usize = 10_000;

/// A memory-safe stack implementation for Bitcoin Script execution
#[derive(Debug, Clone)]
pub struct SecureStack {
    /// Stack data stored as fixed-size byte arrays to prevent allocation attacks
    data: [[u8; MAX_ITEM_SIZE]; MAX_STACK_SIZE],
    /// Length of each item (0 means slot is empty)
    lengths: [usize; MAX_STACK_SIZE],
    /// Current number of items on stack
    count: usize,
    /// Total memory usage tracking
    total_memory: usize,
}

impl SecureStack {
    /// Create a new empty secure stack
    pub fn new() -> Self {
        SecureStack {
            data: [[0u8; MAX_ITEM_SIZE]; MAX_STACK_SIZE],
            lengths: [0; MAX_STACK_SIZE],
            count: 0,
            total_memory: 0,
        }
    }

    /// Push data onto the stack with security checks
    pub fn push(&mut self, data: &[u8]) -> Result<()> {
        // Check stack overflow
        if self.count >= MAX_STACK_SIZE {
            return Err(script_error!(StackOverflow));
        }

        // Check item size limit
        if data.len() > MAX_ITEM_SIZE {
            return Err(memory_error!(BufferTooLarge));
        }

        // Check total memory limit
        if self.total_memory + data.len() > MAX_TOTAL_MEMORY {
            return Err(script_error!(ResourceLimitExceeded));
        }

        // Validate data is not empty (Bitcoin Script requirement)
        if data.is_empty() {
            return Err(script_error!(InvalidScriptData));
        }

        // Copy data safely
        let index = self.count;
        self.data[index][..data.len()].copy_from_slice(data);
        self.lengths[index] = data.len();
        self.count += 1;
        self.total_memory += data.len();

        Ok(())
    }

    /// Pop data from the stack with security checks
    pub fn pop(&mut self) -> Result<([u8; MAX_ITEM_SIZE], usize)> {
        if self.count == 0 {
            return Err(script_error!(StackUnderflow));
        }

        let index = self.count - 1;
        let length = self.lengths[index];
        
        if length == 0 {
            return Err(script_error!(InvalidScriptData));
        }

        // Copy data safely
        let mut result = [0u8; MAX_ITEM_SIZE];
        result[..length].copy_from_slice(&self.data[index][..length]);

        // Clear the slot for security
        self.data[index] = [0u8; MAX_ITEM_SIZE];
        self.lengths[index] = 0;
        self.count -= 1;
        self.total_memory = self.total_memory.saturating_sub(length);

        Ok((result, length))
    }

    /// Peek at top item without removing it
    pub fn peek(&self) -> Result<&[u8]> {
        if self.count == 0 {
            return Err(script_error!(StackUnderflow));
        }

        let index = self.count - 1;
        let length = self.lengths[index];
        
        if length == 0 {
            return Err(script_error!(InvalidScriptData));
        }

        Ok(&self.data[index][..length])
    }

    /// Get item at specific depth (0 = top)
    pub fn peek_at_depth(&self, depth: usize) -> Result<&[u8]> {
        if depth >= self.count {
            return Err(script_error!(StackUnderflow));
        }

        let index = self.count - 1 - depth;
        let length = self.lengths[index];
        
        if length == 0 {
            return Err(script_error!(InvalidScriptData));
        }

        Ok(&self.data[index][..length])
    }

    /// Duplicate top item
    pub fn dup(&mut self) -> Result<()> {
        let top_slice = self.peek()?;
        let mut top_data = [0u8; MAX_ITEM_SIZE];
        top_data[..top_slice.len()].copy_from_slice(top_slice);
        self.push(&top_data[..top_slice.len()])
    }

    /// Duplicate item at specified depth
    pub fn dup_at_depth(&mut self, depth: usize) -> Result<()> {
        let item_slice = self.peek_at_depth(depth)?;
        let mut item_data = [0u8; MAX_ITEM_SIZE];
        item_data[..item_slice.len()].copy_from_slice(item_slice);
        self.push(&item_data[..item_slice.len()])
    }

    /// Drop (remove) top item
    pub fn drop(&mut self) -> Result<()> {
        self.pop().map(|_| ())
    }

    /// Swap top two items
    pub fn swap(&mut self) -> Result<()> {
        if self.count < 2 {
            return Err(script_error!(StackUnderflow));
        }

        let (item1_data, item1_len) = self.pop()?;
        let (item2_data, item2_len) = self.pop()?;
        
        self.push(&item1_data[..item1_len])?;
        self.push(&item2_data[..item2_len])?;
        
        Ok(())
    }

    /// Rotate top three items (3rd item becomes top)
    pub fn rot(&mut self) -> Result<()> {
        if self.count < 3 {
            return Err(script_error!(StackUnderflow));
        }

        let (item1_data, item1_len) = self.pop()?;
        let (item2_data, item2_len) = self.pop()?;
        let (item3_data, item3_len) = self.pop()?;
        
        self.push(&item2_data[..item2_len])?;
        self.push(&item1_data[..item1_len])?;
        self.push(&item3_data[..item3_len])?;
        
        Ok(())
    }

    /// Get current stack size
    pub fn size(&self) -> usize {
        self.count
    }

    /// Check if stack is empty
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Get total memory usage
    pub fn memory_usage(&self) -> usize {
        self.total_memory
    }

    /// Clear the entire stack securely
    pub fn clear(&mut self) {
        // Securely zero all data
        for i in 0..self.count {
            self.data[i] = [0u8; MAX_ITEM_SIZE];
            self.lengths[i] = 0;
        }
        self.count = 0;
        self.total_memory = 0;
    }

    /// Validate stack integrity
    pub fn validate(&self) -> Result<()> {
        let mut calculated_memory = 0;
        
        for i in 0..self.count {
            let length = self.lengths[i];
            
            if length > MAX_ITEM_SIZE {
                return Err(memory_error!(InvalidBounds));
            }
            
            calculated_memory += length;
        }
        
        if calculated_memory != self.total_memory {
            return Err(script_error!(InvalidScriptData));
        }
        
        Ok(())
    }

    /// Create iterator over stack items (top to bottom)
    pub fn iter(&self) -> SecureStackIterator {
        SecureStackIterator {
            stack: self,
            current: 0,
        }
    }
}

impl Default for SecureStack {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator for secure stack
pub struct SecureStackIterator<'a> {
    stack: &'a SecureStack,
    current: usize,
}

impl<'a> Iterator for SecureStackIterator<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.stack.count {
            return None;
        }

        let index = self.stack.count - 1 - self.current;
        let length = self.stack.lengths[index];
        
        if length == 0 {
            return None;
        }

        self.current += 1;
        Some(&self.stack.data[index][..length])
    }
}

/// Alternative stack for Bitcoin Script (OP_TOALTSTACK/OP_FROMALTSTACK)
#[derive(Debug, Clone)]
pub struct AltStack {
    stack: SecureStack,
}

impl AltStack {
    pub fn new() -> Self {
        AltStack {
            stack: SecureStack::new(),
        }
    }

    pub fn push(&mut self, data: &[u8]) -> Result<()> {
        self.stack.push(data)
    }

    pub fn pop(&mut self) -> Result<([u8; MAX_ITEM_SIZE], usize)> {
        self.stack.pop()
    }

    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn size(&self) -> usize {
        self.stack.size()
    }

    pub fn clear(&mut self) {
        self.stack.clear()
    }
}

impl Default for AltStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_stack_operations() {
        let mut stack = SecureStack::new();
        
        // Test push and pop
        let data = b"hello";
        assert!(stack.push(data).is_ok());
        assert_eq!(stack.size(), 1);
        
        let (popped_data, popped_len) = stack.pop().unwrap();
        assert_eq!(&popped_data[..popped_len], data);
        assert_eq!(stack.size(), 0);
    }

    #[test]
    fn test_stack_overflow_protection() {
        let mut stack = SecureStack::new();
        
        // Fill stack to capacity
        for i in 0..MAX_STACK_SIZE {
            let data = [i as u8; 1];
            assert!(stack.push(&data).is_ok());
        }
        
        // Next push should fail
        let data = [255u8; 1];
        assert!(stack.push(&data).is_err());
    }

    #[test]
    fn test_item_size_limit() {
        let mut stack = SecureStack::new();
        
        // Try to push oversized item
        let large_data = [0u8; MAX_ITEM_SIZE + 1];
        assert!(stack.push(&large_data).is_err());
    }

    #[test]
    fn test_memory_limit() {
        let mut stack = SecureStack::new();
        
        // Fill to memory limit
        let item_size = MAX_ITEM_SIZE;
        let max_items = MAX_TOTAL_MEMORY / item_size;
        
        for _ in 0..max_items {
            let data = [1u8; MAX_ITEM_SIZE];
            assert!(stack.push(&data).is_ok());
        }
        
        // One more should fail
        let data = [1u8; 1];
        assert!(stack.push(&data).is_err());
    }

    #[test]
    fn test_stack_underflow_protection() {
        let mut stack = SecureStack::new();
        
        // Pop from empty stack should fail
        assert!(stack.pop().is_err());
        assert!(stack.peek().is_err());
    }

    #[test]
    fn test_dup_operation() {
        let mut stack = SecureStack::new();
        
        let data = b"test";
        stack.push(data).unwrap();
        stack.dup().unwrap();
        
        assert_eq!(stack.size(), 2);
        assert_eq!(stack.peek().unwrap(), data);
    }

    #[test]
    fn test_swap_operation() {
        let mut stack = SecureStack::new();
        
        let data1 = b"first";
        let data2 = b"second";
        
        stack.push(data1).unwrap();
        stack.push(data2).unwrap();
        stack.swap().unwrap();
        
        let (pop1_data, pop1_len) = stack.pop().unwrap();
        assert_eq!(&pop1_data[..pop1_len], data1);
        
        let (pop2_data, pop2_len) = stack.pop().unwrap();
        assert_eq!(&pop2_data[..pop2_len], data2);
    }
}