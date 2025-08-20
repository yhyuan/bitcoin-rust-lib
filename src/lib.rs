//https://en.bitcoin.it/wiki/Address
// Rust Bitcoin Library
// Written in 2014 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! # Big unsigned integer types
//!
//! Implementation of a various large-but-fixed sized unsigned integer types.
//! The functions here are designed to be fast.
//!
//https://github.com/jedisct1/rust-hmac-sha256
//https://crates.io/crates/hmac-sha256
//https://blog.nanpuyue.com/2019/049.html
//https://github.com/nanpuyue/sha256/blob/master/src/lib.rs
//https://blog.csdn.net/u011583927/article/details/80905740
//https://rosettacode.org/wiki/RIPEMD-160#Python
//https://rosettacode.org/wiki/SHA-256#Rust
//https://github.com/paulmillr/noble-ripemd160

#![no_std]
//#![allow(clippy::unreadable_literal)]
mod error;
mod field256;
mod field256_secure;
mod point;
mod point_secure;
mod ripemd160;
mod s256;
mod safe_conversions;
mod sha256;
mod u256;
// mod stack; // Disabled: uses Box which is incompatible with no_std
mod script_secure;
mod security_tests;
mod stack_secure;
//mod hmac;
pub use error::{BitcoinError, Result};
pub use s256::S256;
//use hmac::HMAC;
//use core::default::Default;
