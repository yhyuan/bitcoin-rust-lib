# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a bare minimal Bitcoin implementation in Rust focused on cryptographic primitives and Bitcoin Script operations. The library is designed to be `#![no_std]` compatible and implements core Bitcoin cryptographic operations from scratch.

## Core Architecture

### Cryptographic Foundation
- **U256** (`src/u256.rs`): 256-bit unsigned integer implementation, the foundation for all cryptographic operations
- **Field256** (`src/field256.rs`): Finite field arithmetic over secp256k1 prime field
- **Point** (`src/point.rs`): Elliptic curve point operations for secp256k1
- **S256** (`src/s256.rs`): Secp256k1 curve-specific operations

### Hash Functions
- **SHA256** (`src/sha256.rs`): SHA-256 implementation with HMAC support
- **RIPEMD160** (`src/ripemd160.rs`): RIPEMD-160 hash function for Bitcoin address generation

### Bitcoin Script Engine
- **Script** (`src/script.rs`): Bitcoin Script interpreter with comprehensive opcode support
- **Stack** (`src/stack.rs`): Custom double-linked list implementation for Script execution stack

## Development Commands

### Build Commands
```bash
cargo build          # Build the library
cargo build --release # Build optimized release version
cargo check          # Check code without building
```

### Testing
```bash
cargo test           # Run all tests
cargo test [testname] # Run specific test containing testname
```

### Code Quality
```bash
cargo clippy         # Run Clippy linter
cargo fmt            # Format code
```

## Key Implementation Details

### No Standard Library
The entire codebase uses `#![no_std]` to ensure compatibility with embedded systems and minimal runtime environments.

### Custom Data Structures
- Custom linked list implementation in `stack.rs` using raw pointers for performance
- All cryptographic operations implemented from scratch without external dependencies

### Bitcoin Script Implementation
The Script interpreter (`src/script.rs`) implements a comprehensive set of Bitcoin opcodes including:
- Stack operations (OP_DUP, OP_DROP, OP_SWAP, etc.)
- Arithmetic operations (OP_ADD, OP_SUB, OP_MUL, etc.)
- Cryptographic operations (OP_HASH160, OP_CHECKSIG, etc.)
- Flow control (OP_IF, OP_ELSE, OP_ENDIF, etc.)

### Mathematical Operations
- Field arithmetic operations are implemented with custom modular reduction
- Elliptic curve operations follow secp256k1 specifications
- All operations are designed for constant-time execution where possible

## File Dependencies

The module dependency chain is:
1. `u256.rs` - Base 256-bit integer (no dependencies)
2. `field256.rs` - Depends on u256
3. `point.rs` - Depends on field256 and u256
4. `s256.rs` - Depends on field256, point, and u256
5. `sha256.rs`, `ripemd160.rs` - Hash functions (minimal dependencies)
6. `script.rs` - Depends on all cryptographic modules
7. `stack.rs` - Independent data structure for script execution

## Testing Strategy

Currently no test framework is configured. When adding tests, use standard Rust testing patterns with `#[cfg(test)]` modules in each source file.