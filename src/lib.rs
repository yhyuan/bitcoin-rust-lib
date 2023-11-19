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
mod ripemd160;
mod sha256;
mod u256;
mod s256;
mod field256;
mod point;

//mod hmac;
use core::convert::{From, Into};
use core::ops::{Not, Add, Sub, Mul, Div, Shr, Shl};
use core::cmp::Ordering;
use sha256::Sha256;
use sha256::HMAC;
use ripemd160::Ripemd160;
pub use u256::U256;
pub use s256::S256;
//use hmac::HMAC;
//use core::default::Default;
use core::mem::transmute;
