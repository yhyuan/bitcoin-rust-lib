use core::default::Default;
use core::mem::transmute;
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
