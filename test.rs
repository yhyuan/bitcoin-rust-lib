use std::convert::{From, Into};
use std::ops::{Not, Add, Sub, Mul, Div, Shr, Shl};
use std::cmp::Ordering;
use sha256::Sha256;
use ripemd160::Ripemd160;
//use core::default::Default;
use std::mem::transmute;

//use core::str;
/*
use std::convert::{From, Into};
use std::ops::{Not, Add, Sub, Mul, Div, Shr, Shl};
use std::cmp::Ordering;
*/
#[allow(dead_code)]
mod ripemd160 {
    use std::default::Default;
    use std::mem::transmute;
    const H: [u32; 5] = [
        0x67452301u32, 0xEFCDAB89u32, 0x98BADCFEu32, 0x10325476u32, 0xC3D2E1F0u32
    ];

    pub struct Ripemd160 {
        state: [u32; 5],  // 160 bit
        completed_data_blocks: u64,
        pending: [u8; 64], //512 bit
        num_pending: usize,
    }

    impl Default for Ripemd160 {
        fn default() -> Self {
            Self {
                state: H, // 160 bit
                completed_data_blocks: 0,
                pending: [0u8; 64], // 512 bit
                num_pending: 0,
            }
        }
    }

    //h0 = 0x67452301; h1 = 0xEFCDAB89; h2 = 0x98BADCFE; h3 = 0x10325476; h4 = 0xC3D2E1F0;
    impl Ripemd160 {
        fn word_select(j: usize, msg: &[u8], offsets: &[usize]) -> u32 {
            let word_offset = /*(i * 16 * 4) + (*/offsets[j] * 4/*)*/;
            // little-endian here
            u32::from_be_bytes([
                msg[word_offset + 3],
                msg[word_offset + 2],
                msg[word_offset + 1],
                msg[word_offset + 0],
            ])
        }
        //f
        fn func(j: usize, x: u32, y: u32, z: u32) -> u32 {
            match j {
                0..=15 => x ^ y ^ z,
                16..=31 => (x & y) | (!x & z),
                32..=47 => (x | !y) ^ z,
                48..=63 => (x & z) | (y & !z),
                64..=79 => x ^ (y | !z),
                _ => {
                    unreachable!();
                }
            }
        }
        //k
        fn constant_k(j: usize) -> u32 {
            match j {
                0..=15 => 0x00000000u32,
                16..=31 => 0x5A827999u32,
                32..=47 => 0x6ED9EBA1u32,
                48..=63 => 0x8F1BBCDCu32,
                64..=79 => 0xA953FD4Eu32,
                _ => {
                    unreachable!();
                }
            }
        }
        //k'
        fn constant_k_p(j: usize) -> u32 {
            match j {
                0..=15 => 0x50A28BE6u32,
                16..=31 => 0x5C4DD124u32,
                32..=47 => 0x6D703EF3u32,
                48..=63 => 0x7A6D76E9u32,
                64..=79 => 0x00000000u32,
                _ => {
                    unreachable!();
                }
            }
        }

        //state: 160 bit. one data block: 512 bit
        fn update_state(state: &mut [u32; 5], data: &[u8; 64]) {
            //r
            const R_OFFSETS: &[usize] = &[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
                2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
                13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
            ];
            //r'
            const R_P_OFFSETS: &[usize] = &[
                5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
                4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
                12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
            ];
            //s
            const ROTATIONS: &[u32] = &[
                11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
                9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
                15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
            ];
            //s'
            const ROTATIONS_P: &[u32] = &[
                8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
                7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
                6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
            ];

            let mut h = *state;
            let mut a = h[0];
            let mut b = h[1];
            let mut c = h[2];
            let mut d = h[3];
            let mut e = h[4];
            let mut a_p = h[0];
            let mut b_p = h[1];
            let mut c_p = h[2];
            let mut d_p = h[3];
            let mut e_p = h[4];

            let mut t;

            for j in 0..80 {
                t = a
                    .wrapping_add(Ripemd160::func(j, b, c, d))
                    .wrapping_add(Ripemd160::word_select(j, data, R_OFFSETS))
                    .wrapping_add(Ripemd160::constant_k(j))
                    .rotate_left(ROTATIONS[j])
                    .wrapping_add(e);
                a = e;
                e = d;
                d = c.rotate_left(10);
                c = b;
                b = t;

                t = a_p
                    .wrapping_add(Ripemd160::func(79 - j, b_p, c_p, d_p))
                    .wrapping_add(Ripemd160::word_select(j, data, R_P_OFFSETS))
                    .wrapping_add(Ripemd160::constant_k_p(j))
                    .rotate_left(ROTATIONS_P[j])
                    .wrapping_add(e_p);

                a_p = e_p;
                e_p = d_p;
                d_p = c_p.rotate_left(10);
                c_p = b_p;
                b_p = t;
            }

            t = h[1].wrapping_add(c).wrapping_add(d_p);
            h[1] = h[2].wrapping_add(d).wrapping_add(e_p);
            h[2] = h[3].wrapping_add(e).wrapping_add(a_p);
            h[3] = h[4].wrapping_add(a).wrapping_add(b_p);
            h[4] = h[0].wrapping_add(b).wrapping_add(c_p);
            h[0] = t;

            for (i, v) in state.iter_mut().enumerate() {
                *v = h[i];
            }
        }

        pub fn update(&mut self, data: &[u8]) {
            let mut len = data.len();
            let mut offset = 0;
            //This will only called when the finish is called.
            if self.num_pending > 0 && self.num_pending + len >= 64 {
                //if the pending is is between 1 to 56, then everything is done. 
                // Otherwise, the for loop below will be run once. 
                self.pending[self.num_pending..].copy_from_slice(&data[..64 - self.num_pending]);
                Self::update_state(&mut self.state, &self.pending);
                self.completed_data_blocks += 1;
                offset = 64 - self.num_pending;
                len -= offset;
                self.num_pending = 0;
            }
            
            let data_blocks = len / 64;
            let remain = len % 64;
            for _ in 0..data_blocks {
                Self::update_state(&mut self.state, unsafe {
                    transmute::<_, (&[u8; 64], usize)>(&data[offset..offset + 64]).0
                });
                offset += 64;
            }
            self.completed_data_blocks += data_blocks as u64;
            //copy the remain data to the self.pending and increase num_pending.
            if remain > 0 {
                //self.num_pending = 0.
                self.pending[self.num_pending..self.num_pending + remain]
                    .copy_from_slice(&data[offset..]);
                self.num_pending += remain;
            }
        }

        pub fn finish(mut self) -> [u8; 20] {
            let data_bits = self.completed_data_blocks * 512 + self.num_pending as u64 * 8;
            // When the num_pending (remain) is 56, it is need to pend 64 byte + 8 byte for length. 
            // This is why 72 is used. 
            let mut pending = [0u8; 72];  
            pending[0] = 128; //0x80 or 0b10000000

            let offset = if self.num_pending < 56 { // less than 448 bit.
                56 - self.num_pending
            } else {
                120 - self.num_pending
            };
            //copy the length of data bit. 
            //u64 -> little endian bytes need to fix. pending[offset+7..offset-1].copy_from_slice(&data_bits.to_be_bytes())
            //FIX 2.
            pending[offset..offset + 8].copy_from_slice(&data_bits.to_be().to_be_bytes());
            //pending[offset..offset + 8].copy_from_slice(&data_bits.to_be_bytes());
            self.update(&pending[..offset + 8]);

            for h in self.state.iter_mut() {
                *h = h.to_le(); // FIX 1 *h = h.to_be();
            }
            unsafe { transmute::<_, [u8; 20]>(self.state) }
        }

        pub fn digest(data: &[u8]) -> [u8; 20] {
            let mut ripemd160 = Self::default();
            ripemd160.update(data);
            ripemd160.finish()
        }
    }
}

#[allow(dead_code)]
mod sha256 {
    use std::default::Default;
    use std::mem::transmute;

    const H: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];


    pub struct Sha256 {
        state: [u32; 8],  // 256 bit
        completed_data_blocks: u64,
        pending: [u8; 64], //512 bit
        num_pending: usize,
    }

    impl Default for Sha256 {
        fn default() -> Self {
            Self {
                state: H, // 256 bit
                completed_data_blocks: 0,
                pending: [0u8; 64], // 512 bit
                num_pending: 0,
            }
        }
    }

    impl Sha256 {
        /*
        pub fn with_state(state: [u32; 8]) -> Self {
            Self {
                state,
                completed_data_blocks: 0,
                pending: [0u8; 64],
                num_pending: 0,
            }
        }*/
        //state: 256 bit. one data block: 512 bit
        fn update_state(state: &mut [u32; 8], data: &[u8; 64]) {
            const K: [u32; 64] = [
                0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
            ];

            let mut w: [u32; 64] = [0; 64]; // 32 * 64 = 2048 bit
            //let mut w = unsafe { MaybeUninit::<[u32; 64]>::uninit().assume_init() };
            //break chunk into sixteen 32-bit big-endian words w[0..15]
            for i in 0..16 {
                w[i] =
                    u32::from_ne_bytes(unsafe { *(data[i * 4..i * 4 + 4].as_ptr() as *const [u8; 4]) })
                        .to_be();
            }

            let [mut s0, mut s1, mut t0, mut t1, mut ch, mut ma]: [u32; 6];
            //Extend the sixteen 32-bit words into sixty-four 32-bit words:
            for i in 16..64 {
                s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }

            let mut h = *state;
            for i in 0..64 {
                //ch := (e and f) xor ((not e) and g)
                ch = (h[4] & h[5]) ^ (!h[4] & h[6]);
                //maj := (a and b) xor (a and c) xor(b and c)
                ma = (h[0] & h[1]) ^ (h[0] & h[2]) ^ (h[1] & h[2]);
                //s0 := (a rightrotate 2) xor (a rightrotate 13) xor(a rightrotate 22)
                s0 = h[0].rotate_right(2) ^ h[0].rotate_right(13) ^ h[0].rotate_right(22);
                //s1 := (e rightrotate 6) xor (e rightrotate 11) xor(e rightrotate 25)
                s1 = h[4].rotate_right(6) ^ h[4].rotate_right(11) ^ h[4].rotate_right(25);
                //t1 := h + s1 + ch + k[i] + w[i]
                t0 = h[7]
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]); // 32 bit.
                //t2 := s0 + maj
                t1 = s0.wrapping_add(ma);

                h[7] = h[6]; //h := g
                h[6] = h[5]; //g := f
                h[5] = h[4]; //f := e
                h[4] = h[3].wrapping_add(t0); //e := d + t1
                h[3] = h[2]; //d := c
                h[2] = h[1]; //c := b
                h[1] = h[0]; //b := a
                h[0] = t0.wrapping_add(t1); //a := t1 + t2
            }
            /*
                h0 := h0 + a
                h1 := h1 + b
                h2 := h2 + c
                h3 := h3 + d
                h4 := h4 + e
                h5 := h5 + f
                h6 := h6 + g
                h7 := h7 + h
            */
            for (i, v) in state.iter_mut().enumerate() {
                *v = v.wrapping_add(h[i]);
            }
        }

        pub fn update(&mut self, data: &[u8]) {
            let mut len = data.len();
            let mut offset = 0;

            if self.num_pending > 0 && self.num_pending + len >= 64 {
                self.pending[self.num_pending..].copy_from_slice(&data[..64 - self.num_pending]);
                Self::update_state(&mut self.state, &self.pending);
                self.completed_data_blocks += 1;
                offset = 64 - self.num_pending;
                len -= offset;
                self.num_pending = 0;
            }

            let data_blocks = len / 64;
            let remain = len % 64;
            for _ in 0..data_blocks {
                Self::update_state(&mut self.state, unsafe {
                    transmute::<_, (&[u8; 64], usize)>(&data[offset..offset + 64]).0
                });
                offset += 64;
            }
            self.completed_data_blocks += data_blocks as u64;
            //copy the remain data to the self.pending and increase num_pending.
            if remain > 0 {
                self.pending[self.num_pending..self.num_pending + remain]
                    .copy_from_slice(&data[offset..]);
                self.num_pending += remain;
            }
        }

        pub fn finish(mut self) -> [u8; 32] {
            let data_bits = self.completed_data_blocks * 512 + self.num_pending as u64 * 8;
            let mut pending = [0u8; 72]; //all zero.
            pending[0] = 128; //0x80 or 0b10000000

            let offset = if self.num_pending < 56 { // less than 448 bit.
                56 - self.num_pending
            } else {
                120 - self.num_pending
            };
            //copy the length of data bit.
            pending[offset..offset + 8].copy_from_slice(&data_bits.to_be_bytes());
            self.update(&pending[..offset + 8]);

            for h in self.state.iter_mut() {
                *h = h.to_be();
            }
            unsafe { transmute::<_, [u8; 32]>(self.state) }
        }

        pub fn digest(data: &[u8]) -> [u8; 32] {
            let mut sha256 = Self::default();
            sha256.update(data);
            sha256.finish()
        }
        /*
        pub fn state(&self) -> [u32; 8] {
            self.state
        }*/
    }
}

const N: fn() -> U256 = || -> U256 {
    U256((0xfffffffffffffffffffffffffffffffeu128, 0xbaaedce6af48a03bbfd25e8cd0364141u128))
};

const BTC_ALPHA: [u8; 58] = [49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 77, 78, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]; 
#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct U256((u128, u128));
impl U256 {
    pub fn zero() -> U256 { U256((0u128, 0u128)) }
    pub fn one() -> U256 { U256((0u128, 1u128)) }
    pub fn from_be_bytes(x: [u8; 32]) -> U256 {
        let mut x0: [u8; 16] = [0; 16];
        x0[0..16].copy_from_slice(&x[0..16]);
        let mut x1: [u8; 16] = [0; 16];
        x1[0..16].copy_from_slice(&x[16..32]);
        U256((u128::from_be_bytes(x0), u128::from_be_bytes(x1)))
    }
    pub fn to_be_bytes(self) -> [u8; 32] {
        let mut x: [u8; 32] = [0; 32];
        let U256((x0, x1)) = self;
        let x0_bytes = x0.to_be_bytes();
        x[0..16].copy_from_slice(&x0_bytes[0..16]);
        let x1_bytes = x1.to_be_bytes();
        x[16..32].copy_from_slice(&x1_bytes[0..16]);
        x
    }
    pub fn max_value() -> U256 { U256((u128::max_value(), u128::max_value())) }
    pub fn multiple_u128(x: &u128, y: &u128) -> U256 {
        let divide_u128 = |x: &u128| -> (u128, u128) {
            //(x.overflowing_shr(64).0, x.overflowing_shl(64).0.overflowing_shr(64).0)
            (x.overflowing_shr(64).0, x & 0x0000_0000_0000_0000FFFF_FFFF_FFFF_FFFF_u128)
        };
        let (x0, x1) = divide_u128(&x);
        let (y0, y1) = divide_u128(&y);
        let (v, o) = (x0 * y1).overflowing_add(x1 * y0);
        let (v0, v1) = divide_u128(&v); //6, 2
        let v0_1 = if o {v0 + 1u128.overflowing_shl(64).0} else {v0};
        let (z1, o) = (x1 * y1).overflowing_add(v1.overflowing_shl(64).0);
        let v0_2 = if o {v0_1 + 1} else {v0_1}; // 17
        let z0 = x0 * y0 + v0_2;
        U256((z0, z1))
    }

    pub fn overflowing_add(self, other: U256) -> (U256, bool) {
        let U256((self_upper, self_lower)) = self;
        let U256((other_upper, other_lower)) = other;
        let (v_lower, o1) = self_lower.overflowing_add(other_lower);
        if o1 {
            let (temp_upper, o2) = self_upper.overflowing_add(1);
            let (v_upper, o3) = other_upper.overflowing_add(temp_upper);
            (U256((v_upper, v_lower)), o2 || o3)
        } else {
            let (v_upper, o2) = self_upper.overflowing_add(other_upper);
            (U256((v_upper, v_lower)), o2)
        }
    }

    #[inline]
    pub fn is_odd(self) -> bool {
        let U256((_, self_lower)) = self;
        self_lower & 1u128 == 1u128
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        let U256((x0, x1)) = self;
        x0 == 0u128 && x1 == 0u128
    }

    pub fn mod_inv(self, module: U256) -> U256 {
        let mut mn = (S256((module, true)), S256((self, true)));
        let mut xy = (S256((U256::zero(), true)), S256((U256::one(), true)));
        let is_zero = |x: &S256| -> bool {
            let S256((u, _)) = *x;
            u.is_zero()
        };
        //print_s256(&(mn.1));
        while !is_zero(&(mn.1)){
            let (divider, remainder) = mn.0 / mn.1;
            let (_, z1) = divider * xy.1;
            xy = (xy.1, xy.0 - z1);
            mn = (mn.1, remainder);
        }
        let S256((mut result, s)) = xy.0;
        if !s {
            result = module - result;
        }
        result
    }

    pub fn divide_58_384bit(u: (u128, u128, u128)) -> ((u128, u128, u128), usize) {
        let divide_58_256bit = |x: (u128, u128)| -> ((u128, u128), usize) {
            let (x0, x1) = x;
            let a0 = x0 / 58;
            let b0 = x0 % 58;
            let a1 = x1 / 58;
            let b1 = x1 % 58;

            let a = 0x469ee58469ee58469ee58469ee58469u128; //hex((2 ** 128) // 58)
            let b = 54u128;

            let t = b0 * b + b1;
            let remainder = t % 58;

            let mut y0 = a0;
            let y1 = a1 + t / 58;
            //let t1 = b0 * a;
            let (y1, s) = y1.overflowing_add(b0 * a);
            if s {
                y0 = y0 + 1;
            }
            ((y0, y1), remainder as usize)
        };

        match u {
            (0u128, 0u128, x2)   =>  ((0u128, 0u128, x2 / 58), (x2 % 58) as usize),
            (0u128, x1, x2)   =>  {
                let ((y1, y2), r) = divide_58_256bit((x1, x2));
                ((0u128, y1, y2), r)
            },
            (x0, x1, x2)   =>  {
                let ((y0, y1), r1) = divide_58_256bit((x0, x1));
                let ((z0, z1), r2) = divide_58_256bit((r1 as u128, x2));
                let (z2, s) = y1.overflowing_add(z0);
                if s {
                    ((y0 + 1, z2, z1), r2)
                } else {
                    ((y0, z2, z1), r2)
                }
            },
        }
    }

    pub fn to_base58(u: (u128, u128, u128), num_of_zeros: u8) -> [u8; 66] {
        let mut base58: [u8; 66] = [0; 66]; // log(2**384) / log(58) = 65.5
        let mut x = u;
        let mut i = base58.len();
        let is_zero = |x: (u128, u128, u128)| -> bool {
            let (x0, x1, x2) = x;
            x0 == 0u128 && x1 == 0u128 && x2 == 0u128
        };
        while !is_zero(x) {
            let (divider, remainder) = U256::divide_58_384bit(x);
            if i == 0 {
                unreachable!();
            }
            base58[i - 1] = BTC_ALPHA[remainder];
            x = divider;
            i = i - 1; 
        }
        // 66 - i is the size of result.
        for _ in 0..num_of_zeros {
            base58[i - 1] = BTC_ALPHA[0];
            i = i - 1;
        } 
        unsafe { transmute::<_, [u8; 66]>(base58) }
    }

    pub fn calculate_p2pkh_address(self, is_testnet: bool)  -> [u8; 34]{
        let U256((x0, x1)) = self;
        let public_key = Point::g().multiple(U256((x0, x1))).calculate_public_key();
        let result = Ripemd160::digest(&Sha256::digest(&public_key));
        let mut ripemd160: [u8; 21] = [0; 21]; // 32 * 65
        ripemd160[0] = if is_testnet {0x6fu8} else {0x00u8}; //main net. test net 0x6fu8
        ripemd160[1..21].copy_from_slice(&result);
        let mut num_of_zeros = 0u8;
        for i in 0..21 {
            if ripemd160[i] == 0x00u8 {
                num_of_zeros = num_of_zeros + 1;
            } else {
                break;
            }
        }
        let double_sha256 = Sha256::digest(&Sha256::digest(&ripemd160));
        let mut v: [u8; 32] = [0u8; 32]; // 32 * 65
        v[7..28].copy_from_slice(&ripemd160[0..21]); //The first 7 byte are 0.
        v[28..].copy_from_slice(&double_sha256[..4]);        
        let U256((x0, x1)) = U256::from_be_bytes(v); // v has 25 bytes. First byte is for main net for test net. The last 4 bytes are double sha. 
        //math.log(0x70*2**192) / math.log(58) = 33.93. The address for main net and test net are always less than 34.
        let base58 = U256::to_base58((0u128, x0, x1), num_of_zeros);
        let mut address: [u8; 34] = [0u8; 34];
        address[0..34].copy_from_slice(&base58[32..66]);        
        address
    }
   
    pub fn sign(self, z: U256) -> (U256, U256) {
        let U256((x0, x1)) = self;
        let k = self.deterministic_k(z);
        let U256((x0, x1)) = k;
        println!("k: {:x}, {:x}", x0, x1);
        let Point((f, _)) = Point::g().multiple(k);
        let r = f.u;
        let U256((x0, x1)) = r;
        println!("r: {:x}, {:x}", x0, x1);
        let k_f = Field256 {u: k, p: N};
        let r_f = Field256 {u: r, p: N};
        let z_f = Field256 {u: z, p: N};
        let key_f = Field256 {u: U256((x0, x1)), p: N};
        let x = r_f * key_f;
        let U256((x0, x1)) = x.u;
        println!("r_f * key_f: {:x}, {:x}", x0, x1);
        let s_f = (z_f + (r_f * key_f)) / k_f;
        let mut s = s_f.u;
        
        if s > U256((0xfffffffffffffffffffffffffffffffeu128 / 2u128, 0xbaaedce6af48a03bbfd25e8cd0364141u128 / 2u128)) {
            s = N() - s;
        }
        (r, s)
    }

    pub fn deterministic_k(self, z_input: U256) -> U256 {
        let mut k = U256::zero().to_be_bytes();
        let mut v = [0x01; 32];
        let mut z = z_input;
        if z > N() {
            z = z - N();
        }
        let z_bytes = z.to_be_bytes();
        let secret_bytes = self.to_be_bytes();
        let mut data = [0u8; 97];
        data[0..32].copy_from_slice(&v[0..32]);
        data[32] = 0x00;
        data[33..65].copy_from_slice(&secret_bytes[0..32]);
        data[65..97].copy_from_slice(&z_bytes[0..32]);
        k = HMAC::mac(&data, &k);
        v = HMAC::mac(&v, &k);
        data[0..32].copy_from_slice(&v[0..32]);
        data[32] = 0x01;
        data[33..65].copy_from_slice(&secret_bytes[0..32]);
        data[65..97].copy_from_slice(&z_bytes[0..32]);
        k = HMAC::mac(&data, &k);
        v = HMAC::mac(&v, &k);
        loop {
            v = HMAC::mac(&v, &k);
            let candidate = U256::from_be_bytes(v);
            if candidate >= U256::one() && candidate < N() {
                return candidate;
            }
            let mut data_2 = [0u8; 33];
            data_2[0..32].copy_from_slice(&v[0..32]);
            data_2[32] = 0x00;
            k = HMAC::mac(&data_2, &k);
            v = HMAC::mac(&v, &k);
        }
    }

   pub fn calculate_wif(self, is_testnet: bool)  -> [u8; 51]{
        let U256((x0, x1)) = self;
        let mut a: [u8; 33] = [0; 33]; // 32 * 65
        a[0] = if is_testnet {0xefu8} else {0x80u8};//main net
        a[1..17].copy_from_slice(&x0.to_be_bytes());
        a[17..33].copy_from_slice(&x1.to_be_bytes());
        let double_sha256 = Sha256::digest(&Sha256::digest(&a));

        let mut b: [u8; 16] = [0; 16];
        b[11..16].copy_from_slice(&a[0..5]);
        let x0 = u128::from_be_bytes(b);
        b[0..16].copy_from_slice(&a[5..21]);
        let x1 = u128::from_be_bytes(b);
        b[0..12].copy_from_slice(&a[21..33]);
        b[12..16].copy_from_slice(&double_sha256[0..4]);
        let x2 = u128::from_be_bytes(b);
        let base58 = U256::to_base58((x0, x1, x2), 0); // 0 because of a[0] can not be zero.
        let mut wif: [u8; 51] = [0u8; 51];
        wif[0..51].copy_from_slice(&base58[15..66]);        
        wif
    }

   pub fn calculate_compressed_wif(self, is_testnet: bool)  -> [u8; 52]{
        let U256((x0, x1)) = self;
        let mut a: [u8; 34] = [0; 34]; 
        a[0] = if is_testnet {0xefu8} else {0x80u8};//main net
        a[1..17].copy_from_slice(&x0.to_be_bytes());
        a[17..33].copy_from_slice(&x1.to_be_bytes());
        a[33] = 0x01u8;
        let double_sha256 = Sha256::digest(&Sha256::digest(&a));

        let mut b: [u8; 16] = [0; 16];
        b[10..16].copy_from_slice(&a[0..6]);
        let x0 = u128::from_be_bytes(b);
        b[0..16].copy_from_slice(&a[6..22]);
        let x1 = u128::from_be_bytes(b);
        b[0..12].copy_from_slice(&a[22..34]);
        b[12..16].copy_from_slice(&double_sha256[0..4]);
        let x2 = u128::from_be_bytes(b);
        let base58 = U256::to_base58((x0, x1, x2), 0); // 0 because of a[0] can not be zero.
        let mut wif: [u8; 52] = [0u8; 52];
        wif[0..52].copy_from_slice(&base58[14..66]);        
        wif
    }

}

impl From<u128> for U256 {
    fn from(val: u128) -> U256 {
        U256((0u128, val))
    }
}

impl Into<u128> for U256 {
    fn into(self) -> u128 {
        let U256((self_upper, self_lower)) = self;
        assert!(self_upper == 0u128);
        self_lower
    }
}

impl Not for U256 {
    type Output = U256;

    fn not(self) -> U256 {
        let U256((self_upper, self_lower)) = self;
        U256((!self_upper, !self_lower))
    }
}

impl Add for U256 {
    type Output = U256;

    fn add(self, other: U256) -> U256 {
        let (v, o) = self.overflowing_add(other);
        assert!(o == false);
        v
    }
}

impl Ord for U256 {
    fn cmp(&self, other: &U256) -> Ordering {
        let U256((self_upper, self_lower)) = self;
        let U256((other_upper, other_lower)) = other;
        let compare_u128 = |x: &u128, y: &u128| -> Ordering {
            if x == y {
                Ordering::Equal
            } else if x > y {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        };
        if self_upper == other_upper {
            compare_u128(&self_lower, &other_lower)
        } else {
            compare_u128(&self_upper, &other_upper)
        }
    }
}

impl PartialOrd for U256 {
    fn partial_cmp(&self, other: &U256) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Sub for U256 {
    type Output = U256;

    fn sub(self, other: U256) -> U256 {
        let U256((self_upper, self_lower)) = self;
        let U256((other_upper, other_lower)) = other;
        if self_upper == other_upper {
            assert!(self_lower >= other_lower);
            U256((0u128, self_lower - other_lower))
        } else {
            assert!(self_upper > other_upper);
            if self_lower >= other_lower {
                U256((self_upper - other_upper, self_lower - other_lower))
            } else {
                U256((self_upper - other_upper - 1, self_lower + (u128::max_value() - other_lower) + 1))
            }
        }
    }
}

impl Mul for U256 {
    type Output = (U256, U256);

    fn mul(self, other: U256) -> (U256, U256) {
        let U256((x0, x1)) = self;
        let U256((y0, y1)) = other;
        let (v, o) = U256::multiple_u128(&x0, &y1).overflowing_add(U256::multiple_u128(&x1, &y0));
        let U256((v0, v1)) = v;
        let v0_1 = if o {U256((1u128, v0))} else {U256((0u128, v0))};
        let (z1, o) = U256::multiple_u128(&x1, &y1).overflowing_add(U256((v1, 0u128)));
        let v0_2 = if o {v0_1 + U256::one()} else {v0_1}; // 17
        let z0 = U256::multiple_u128(&x0, &y0) + v0_2;
        (z0, z1)
    }
}

impl Div for U256 {
    type Output = (U256, U256);

    fn div(self, other: U256) -> (U256, U256) {
        assert!(other != U256::zero());
        let divide_by_max = |x: &u128| -> (u128, u128) {
            let a = u128::max_value() / x;
            let b = u128::max_value() % x;
            if b == x - 1 {
                (a + 1, 0)
            } else {
                (a, b + 1)
            }
        };
        match self.cmp(&other) {
            Ordering::Less =>  (U256::zero(), self),
            Ordering::Equal => (U256::one(), U256::zero()),
            Ordering::Greater => {
                match (self, other) {
                    (U256((x0, x1)), U256((0u128, y1))) if y1 == 1u128 => (U256((x0, x1)), U256::zero()),
                    (U256((0u128, x1)), U256((0u128, y1))) => (U256((0u128, x1 / y1)), U256((0u128, x1 % y1))),
                    (U256((x0, x1)), U256((0u128, y1))) if x0 >= y1 => {
                        let (z0, z1) = U256((x0%y1, x1%y1)) / U256((0u128, y1)); 
                        (U256((x0/y1, x1/y1)) + z0, z1)
                    },
                    (U256((x0, x1)), U256((0u128, y1))) if x0 < y1 => {
                        let (a, b) = divide_by_max(&y1);
                        let (z0, z1) = (U256::multiple_u128(&x0, &b) + U256((0u128, x1)))/ U256((0u128, y1)); 
                        (U256::multiple_u128(&x0, &a) + z0, z1)
                    },
                    (U256((x0, x1)), U256((y0, y1))) if x0 == y0 => (U256::one(), U256((0u128, x1 - y1))),
                    (U256((x0, x1)), U256((y0, y1))) => {
                        let temp = x0 / (y0 + 1);
                        let (_, u) = U256((y0, y1)) * U256((0, temp));
                        let (z0, z1) = (U256((x0, x1)) - u) / U256((y0, y1));
                        (U256((0, temp)) + z0, z1)
                    },
                }
            }
        }
    }
}

impl Shl<usize> for U256 {
    type Output = U256;

    fn shl(self, shift: usize) -> U256 {
        let U256((x0, x1)) = self;
        if shift < 128 {
            let v = ((1u128.shl(shift) - 1).shl(128 - shift) & x1).shr(128 - shift);
            U256((x0.shl(shift) + v, x1.shl(shift)))
        } else {
            U256((x1.shl(shift - 128), 0u128))
        }
    }
}

impl Shr<usize> for U256 {
    type Output = U256;

    fn shr(self, shift: usize) -> U256 {
        let U256((x0, x1)) = self;
        if shift < 128 {
            let v = ((1u128.shl(shift) - 1) & x0).shl(128 - shift);
            U256((x0.shr(shift), x1.shr(shift) + v))
        } else {
            U256((0u128, x0.shr(shift - 128)))
        }
    }
}

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct S256((U256, bool));

impl Add for S256 {
    type Output = S256;

    fn add(self, other: S256) -> S256 {
        match (self, other) {
            (S256((u1, true)),  S256((u2, true)))   =>  S256((u1 + u2, true)),
            (S256((u1, true)),  S256((u2, false)))  =>  if u1 >= u2 {S256((u1 - u2, true))} else {S256((u2 - u1, false))},
            (S256((u1, false)), S256((u2, true)))   =>  if u2 >= u1 {S256((u2 - u1, true))} else {S256((u1 - u2, false))},
            (S256((u1, false)), S256((u2, false)))  =>  S256((u1 + u2, false)),
        }
    }
}

impl Sub for S256 {
    type Output = S256;

    fn sub(self, other: S256) -> S256 {
        match (self, other) {
            (S256((u1, true)), S256((u2, true)))  =>  if u1 >= u2 {S256((u1 - u2, true))} else {S256((u2 - u1, false))},
            (S256((u1, true)), S256((u2, false))) =>  S256((u1 + u2, true)),
            (S256((u1, false)), S256((u2, true))) =>  S256((u1 + u2, false)),
            (S256((u1, false)), S256((u2, false)))  => if u2 >= u1 {S256((u2 - u1, true))} else {S256((u1 - u2, false))},
        }
    }
}

impl Mul for S256 {
    type Output = (S256, S256);

    fn mul(self, other: S256) -> (S256, S256) {
        let S256((u1, s1)) = self;
        let S256((u2, s2)) = other;
        let (z0, z1) = u1 * u2;
        (S256((z0, s1 == s2)), S256((z1, s1 == s2)))
    }
}

impl Div for S256 {
    type Output = (S256, S256);

    fn div(self, other: S256) -> (S256, S256) {
        let S256((u1, _)) = self;
        let S256((u2, _)) = other;
        assert!(u2 != U256::zero());
        let (z0, z1) = u1 / u2;
        match (self, other) {
            (S256((_, true)), S256((_, true)))  =>  (S256((z0, true)), S256((z1, true))),
            (S256((_, true)), S256((u2, false))) =>  (S256((z0 + U256::one(), false)), S256((u2 - z1, false))),
            (S256((_, false)), S256((u2, true))) =>  (S256((z0 + U256::one(), false)), S256((u2 - z1, true))),
            (S256((_, false)), S256((_, false)))  =>  (S256((z0, true)), S256((z1, false))),
        }
    }
}

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
struct Field256 {
    u: U256,
    p: fn() -> U256
}

const P: fn() -> U256 = || -> U256 {
    U256((0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128, 0xFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2Fu128))
};


impl Field256 {
    pub fn zero(p: fn() -> U256) -> Field256 { Field256 {u: U256((0u128, 0u128)), p: p}}
    pub fn one(p: fn() -> U256) -> Field256 { Field256 {u: U256((0u128, 1u128)), p: p}}
    pub fn max_value(p: fn() -> U256) -> Field256 { Field256 {u: p() - U256::one(), p: p}}
}

impl Add for Field256 {
    type Output = Field256;

    fn add(self, other: Field256) -> Field256 {
        let self_u256 = self.u;
        let other_u256 = other.u;
        let self_p = self.p;
        let other_p = other.p;
        let prime = self_p();
        assert_eq!(prime, other_p());
        let (mut v, o) = self_u256.overflowing_add(other_u256);
        if v > prime {
            v = v - prime;
        }
        if o {
            let p_minus = U256::max_value() - prime + U256::one();
            v = v + p_minus;
        }
        if v > prime {
            v = v - prime;
        }
        Field256 {u: v, p: self_p}
    }
}

impl Ord for Field256 {
    fn cmp(&self, other: &Field256) -> Ordering {
        let self_u256 = self.u;
        let other_u256 = other.u;
        let self_p = self.p;
        let other_p = other.p;
        let prime = self_p();
        assert_eq!(prime, other_p());
        self_u256.cmp(&other_u256)
    }
}

impl PartialOrd for Field256 {
    fn partial_cmp(&self, other: &Field256) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Sub for Field256 {
    type Output = Field256;

    fn sub(self, other: Field256) -> Field256 {
        let self_u256 = self.u;
        let other_u256 = other.u;
        let self_p = self.p;
        let other_p = other.p;
        let prime = self_p();
        assert_eq!(prime, other_p());
        if self_u256 >= other_u256 {
            Field256 {u: self_u256 - other_u256, p: self_p}
        } else {
            Field256 {u: self_u256, p: self_p} + Field256 {u: prime - other_u256, p: self_p}
        }
    }
}

impl Mul for Field256 {
    type Output = Field256;

    fn mul(self, other: Field256) -> Field256 {
        let self_u256 = self.u;
        let other_u256 = other.u;
        let self_p = self.p;
        let other_p = other.p;
        let prime = self_p();
        assert_eq!(prime, other_p());
        let p_minus = U256::max_value() - prime + U256::one();
        let (U256((x0, x1)), U256((x2, x3))) = self_u256 * other_u256;
        let eliminate = |x: u128, u: U256| -> U256 {
            let U256((_, p_minus_x1)) = p_minus;
            let (mut v, o) = U256::multiple_u128(&x, &p_minus_x1).overflowing_add(u);
            let u_p = prime;
            if v >= u_p {
                v = v - u_p;
            }
            if o {
                let u_p_minus = p_minus;
                v = v + u_p_minus;
            }
            if v >= u_p {
                v = v - u_p;
            }
            v
        };
        let U256((y0, y1)) = eliminate(x0, U256((x1, x2)));
        let u = eliminate(y0, U256((y1, x3)));
        Field256 {u: u, p: self_p}
    }
}

impl Div for Field256 {
    type Output = Field256;

    fn div(self, other: Field256) -> Field256 {
        let self_u256 = self.u;
        let other_u256 = other.u;
        let self_p = self.p;
        let other_p = other.p;
        let prime = self_p();
        assert_eq!(prime, other_p());
        let f1 = Field256 {u: self_u256, p: self_p};
        let f2 = Field256 {u: other_u256.mod_inv(prime), p: self_p} ;
        let r =  f1 * f2;
        r
    }
}

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Point((Field256, Field256));
impl Point {
    #[inline]
    pub fn zero() -> Point {
        Point((
            Field256::zero(P),
            Field256::zero(P)
        ))
    }

    #[inline]
    pub fn g() -> Point {
        Point((
            (Field256 {u: U256((0x79be667ef9dcbbac55a06295ce870b07u128, 0x029bfcdb2dce28d959f2815b16f81798u128)), p: P}),
            (Field256 {u: U256((0x483ada7726a3c4655da4fbfc0e1108a8u128, 0xfd17b448a68554199c47d08ffb10d4b8u128)), p: P})
        ))
    }

    pub fn multiple(self, other: U256) -> Point {
        let mut x = Point::g();
        let mut sum = Point::zero();
        let mut u = other;
        for _ in 0..256 {
            if u.is_odd() {
                sum = sum + x;
            }
            u = u.shr(1usize);
            x = x + x;
        }
        sum
    }

    pub fn calculate_public_key(self) -> [u8; 65] {
        let Point((x, y)) = self;
        let U256((x0, x1)) = x.u;
        let U256((y0, y1)) = y.u;
        let mut public_key: [u8; 65] = [0; 65]; // 32 * 65
        public_key[0] = 0x04u8; //main net
        public_key[1..17].copy_from_slice(&x0.to_be_bytes());
        public_key[17..33].copy_from_slice(&x1.to_be_bytes());
        public_key[33..49].copy_from_slice(&y0.to_be_bytes());
        public_key[49..65].copy_from_slice(&y1.to_be_bytes());        
        unsafe { transmute::<_, [u8; 65]>(public_key) }
    }

    pub fn calculate_compressed_public_key(self) -> [u8; 33] {
        let Point((x, y)) = self;
        let U256((x0, x1)) = x.u;
        let U256((_, y1)) = y.u;
        let mut public_key: [u8; 33] = [0; 33]; // 32 * 65
        public_key[0] = if y1 % 2 == 0u128 {0x02u8} else {0x03u8}; //main net
        public_key[1..17].copy_from_slice(&x0.to_be_bytes());
        public_key[17..33].copy_from_slice(&x1.to_be_bytes());
        unsafe { transmute::<_, [u8; 33]>(public_key) }
    }

}

impl Ord for Point {
    fn cmp(&self, other: &Point) -> Ordering {
        let Point((self_x, self_y)) = self;
        let Point((other_x, other_y)) = other;
        match self_x.cmp(&other_x) {
            Ordering::Less =>  Ordering::Less,
            Ordering::Equal => self_y.cmp(&other_y),
            Ordering::Greater => Ordering::Greater
        }
    }
}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Point) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add for Point {
    type Output = Point;

    fn add(self, other: Point) -> Point {
        let zero = Field256::zero(P);
        match (self, other) {
            (Point((x1, _)), Point((x2, _))) if x1 == zero && x2 == zero => Point::zero(),
            (Point((x1, _)), _) if x1 == zero => other,
            (_, Point((x2, _))) if x2 == zero => self,
            (Point((x1, y1)), Point((x2, y2))) if x1 == x2 && y1 != y2 => Point::zero(),
            (Point((x1, y1)), Point((x2, y2))) if x1 == x2 && y1 == y2 => {
                let t_1 = x1 * x1;
                let t_2 = t_1 + t_1;
                let t_3 = t_2 + t_1;
                let s = /*( + Point::a())*/ t_3/(y1 + y1);
                let x3 = s * s - (x1 + x1);
                let y3 = s * (x1 - x3) - y1;
                Point((x3, y3))
            },
            (Point((x1, y1)), Point((x2, y2))) => {
                let s = (y2 - y1) / (x2 - x1);
                let x3 = s * s - (x1 + x2);
                let y3 = s * (x1 - x3) - y1;
                Point((x3, y3))
            }
        }
    }
}

pub struct HMAC;

impl HMAC {
    /// Compute HMAC-SHA256(`input`, `k`)
    pub fn mac(input: &[u8], k: &[u8]) -> [u8; 32] {
        let mut key = [0u8; 64];
        if k.len() > 64 {
            let hash_key = Sha256::digest(k);
            key[0..32].copy_from_slice(&hash_key[0..32]);
        } else {
            key[0..k.len()].copy_from_slice(&k[..]);
        }
        let mut i_key_pad = [0x36; 64];
        for i in 0..64 {
            i_key_pad[i] = i_key_pad[i] ^ key[i];
        } 
        let mut sha256 = Sha256::default();        
        sha256.update(&i_key_pad);
        sha256.update(input);

        let mut o_key_pad = [0x5c; 64];
        for i in 0..64 {
            o_key_pad[i] = o_key_pad[i] ^ key[i];
        } 
        let mut sha256_2 = Sha256::default();        
        sha256_2.update(&o_key_pad);
        sha256_2.update(&sha256.finish());
        sha256_2.finish()
    }
}


fn main() {
    let (U256((x0, x1)), U256((y0, y1))) = U256((0x85fe9664cdfb27264efd2450c1dd9a8du128, 0x8bc6b7f666d9941515ad6367401548d4u128)).sign(U256((0x27996e34954f08e92178c39c4d53e364u128, 0x6f3d7b382bd3d6659eb8d9121b8d5a6au128)));
    println!("{:x}, {:x}", x0, x1);
    println!("{:x}, {:x}", y0, y1);
}
