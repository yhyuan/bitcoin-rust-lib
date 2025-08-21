//! Comprehensive error handling for Bitcoin library
//!
//! This module provides secure error types that prevent information leakage
//! and enable proper error propagation throughout the library.

use core::fmt::{Display, Formatter, Result as FmtResult};

/// Main error type for all Bitcoin library operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitcoinError {
    /// Arithmetic operation errors
    Arithmetic(ArithmeticError),
    /// Cryptographic operation errors  
    Cryptographic(CryptographicError),
    /// Script execution errors
    Script(ScriptError),
    /// Memory/buffer operation errors
    Memory(MemoryError),
    /// Input validation errors
    Input(InputError),
}

/// Arithmetic operation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithmeticError {
    /// Division by zero
    DivisionByZero,
    /// Integer overflow
    Overflow,
    /// Integer underflow
    Underflow,
    /// Invalid modular operation
    InvalidModulo,
    /// Conversion error between number types
    ConversionError,
}

/// Cryptographic operation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CryptographicError {
    /// Invalid private key
    InvalidPrivateKey,
    /// Invalid public key  
    InvalidPublicKey,
    /// Point not on curve
    InvalidCurvePoint,
    /// Invalid signature
    InvalidSignature,
    /// Hash function error
    HashError,
    /// Invalid field element
    InvalidFieldElement,
    /// Point at infinity in invalid context
    PointAtInfinity,
}

/// Script execution errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptError {
    /// Stack underflow
    StackUnderflow,
    /// Stack overflow
    StackOverflow,
    /// Invalid opcode
    InvalidOpcode,
    /// Script too long
    ScriptTooLong,
    /// Too many operations
    TooManyOperations,
    /// Invalid script data
    InvalidScriptData,
    /// Script execution failed
    ExecutionFailed,
    /// Resource limit exceeded
    ResourceLimitExceeded,
}

/// Memory and buffer operation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryError {
    /// Buffer too small
    BufferTooSmall,
    /// Buffer too large
    BufferTooLarge,
    /// Invalid buffer bounds
    InvalidBounds,
    /// Null pointer access
    NullPointer,
    /// Memory alignment error
    AlignmentError,
}

/// Input validation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputError {
    /// Invalid length
    InvalidLength,
    /// Invalid format
    InvalidFormat,
    /// Invalid encoding
    InvalidEncoding,
    /// Invalid range
    InvalidRange,
    /// Missing required data
    MissingData,
}

/// Result type alias for convenience
pub type Result<T> = core::result::Result<T, BitcoinError>;

impl Display for BitcoinError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            BitcoinError::Arithmetic(err) => write!(f, "Arithmetic error: {}", err),
            BitcoinError::Cryptographic(err) => write!(f, "Cryptographic error: {}", err),
            BitcoinError::Script(err) => write!(f, "Script error: {}", err),
            BitcoinError::Memory(err) => write!(f, "Memory error: {}", err),
            BitcoinError::Input(err) => write!(f, "Input error: {}", err),
        }
    }
}

impl Display for ArithmeticError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ArithmeticError::DivisionByZero => write!(f, "Division by zero"),
            ArithmeticError::Overflow => write!(f, "Integer overflow"),
            ArithmeticError::Underflow => write!(f, "Integer underflow"),
            ArithmeticError::InvalidModulo => write!(f, "Invalid modular operation"),
            ArithmeticError::ConversionError => write!(f, "Number conversion error"),
        }
    }
}

impl Display for CryptographicError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            CryptographicError::InvalidPrivateKey => write!(f, "Invalid private key"),
            CryptographicError::InvalidPublicKey => write!(f, "Invalid public key"),
            CryptographicError::InvalidCurvePoint => write!(f, "Point not on curve"),
            CryptographicError::InvalidSignature => write!(f, "Invalid signature"),
            CryptographicError::HashError => write!(f, "Hash function error"),
            CryptographicError::InvalidFieldElement => write!(f, "Invalid field element"),
            CryptographicError::PointAtInfinity => write!(f, "Point at infinity"),
        }
    }
}

impl Display for ScriptError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ScriptError::StackUnderflow => write!(f, "Stack underflow"),
            ScriptError::StackOverflow => write!(f, "Stack overflow"),
            ScriptError::InvalidOpcode => write!(f, "Invalid opcode"),
            ScriptError::ScriptTooLong => write!(f, "Script too long"),
            ScriptError::TooManyOperations => write!(f, "Too many operations"),
            ScriptError::InvalidScriptData => write!(f, "Invalid script data"),
            ScriptError::ExecutionFailed => write!(f, "Script execution failed"),
            ScriptError::ResourceLimitExceeded => write!(f, "Resource limit exceeded"),
        }
    }
}

impl Display for MemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            MemoryError::BufferTooSmall => write!(f, "Buffer too small"),
            MemoryError::BufferTooLarge => write!(f, "Buffer too large"),
            MemoryError::InvalidBounds => write!(f, "Invalid buffer bounds"),
            MemoryError::NullPointer => write!(f, "Null pointer access"),
            MemoryError::AlignmentError => write!(f, "Memory alignment error"),
        }
    }
}

impl Display for InputError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            InputError::InvalidLength => write!(f, "Invalid length"),
            InputError::InvalidFormat => write!(f, "Invalid format"),
            InputError::InvalidEncoding => write!(f, "Invalid encoding"),
            InputError::InvalidRange => write!(f, "Invalid range"),
            InputError::MissingData => write!(f, "Missing required data"),
        }
    }
}

/// Convenience macros for error creation
#[macro_export]
macro_rules! arithmetic_error {
    ($kind:ident) => {
        BitcoinError::Arithmetic(ArithmeticError::$kind)
    };
}

#[macro_export]
macro_rules! crypto_error {
    ($kind:ident) => {
        BitcoinError::Cryptographic(CryptographicError::$kind)
    };
}

#[macro_export]
macro_rules! script_error {
    ($kind:ident) => {
        BitcoinError::Script(ScriptError::$kind)
    };
}

#[macro_export]
macro_rules! memory_error {
    ($kind:ident) => {
        BitcoinError::Memory(MemoryError::$kind)
    };
}

#[macro_export]
macro_rules! input_error {
    ($kind:ident) => {
        BitcoinError::Input(InputError::$kind)
    };
}

/// Trait for converting results to Bitcoin errors
#[allow(dead_code)]
pub trait ToBitcoinError<T> {
    fn to_bitcoin_error(self) -> Result<T>;
}

impl<T> ToBitcoinError<T> for Option<T> {
    fn to_bitcoin_error(self) -> Result<T> {
        self.ok_or(input_error!(MissingData))
    }
}
