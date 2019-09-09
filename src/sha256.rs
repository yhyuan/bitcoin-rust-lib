use core::default::Default;
use core::mem::transmute;

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

