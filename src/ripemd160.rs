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

#[cfg(test)]
mod tests {
    use ripemd160::Ripemd160;
    #[test]
    fn ripemd_160() {
        let result = Ripemd160::digest("Rosetta Code".as_bytes());
        let correct = [0xb3u8, 0xbeu8, 0x15u8, 0x98u8, 0x60u8, 0x84u8, 0x2cu8, 0xebu8, 0xaau8, 0x71u8, 0x74u8, 0xc8u8, 0xffu8, 0xf0u8, 0xaau8, 0x9eu8, 0x50u8, 0xa5u8, 0x19u8, 0x9fu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");

        let result = Ripemd160::digest("hqrnoyepkvxhjtlagcmizaeffkyoqwfcoacsxkbwiclhmlgisbo".as_bytes());
        let correct = [0xcdu8, 0xa6u8, 0x26u8, 0xbfu8, 0x7bu8, 0x80u8, 0xecu8, 0x7fu8, 0x3cu8, 0x14u8, 0xe6u8, 0x6eu8, 0xebu8, 0x7cu8, 0x40u8, 0x4eu8, 0x99u8, 0x1eu8, 0x67u8, 0xa3u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("trtdvodkjvzfqycwbmmxzjrovknbgvtoxnkvobhjpwcqdahlyw".as_bytes());
        let correct = [0xcdu8, 0xa8u8, 0xa1u8, 0xdbu8, 0x7du8, 0xa6u8, 0x11u8, 0xc9u8, 0x04u8, 0x98u8, 0xc2u8, 0x21u8, 0x73u8, 0xcdu8, 0xeau8, 0xf7u8, 0xa4u8, 0xe7u8, 0x22u8, 0xe7u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("gpshlnvxfgqxjyopehyfkddyobavxljojgomzyleboysdkuuxrrimuaznbfujwkvc".as_bytes());
        let correct = [0x19u8, 0x4eu8, 0x20u8, 0xe2u8, 0x56u8, 0x8fu8, 0xa9u8, 0xbdu8, 0xc6u8, 0x95u8, 0xfeu8, 0xb3u8, 0x53u8, 0xefu8, 0xb4u8, 0xf2u8, 0x95u8, 0x64u8, 0x5bu8, 0x44u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("srzmrtmdldqliteweqwxfwboipagsmfpylilyzzrtgrepbgtvfwbstmonwjbgtxchsuj".as_bytes());
        let correct = [0x0cu8, 0xa0u8, 0xd3u8, 0xa7u8, 0x64u8, 0xadu8, 0x8cu8, 0x0au8, 0x44u8, 0xfdu8, 0xcdu8, 0x6eu8, 0x4eu8, 0xc6u8, 0xe4u8, 0x5eu8, 0x54u8, 0xcbu8, 0x05u8, 0xebu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("slfjrjeycezqwfwhavwzuwaomojsfbvjwiqwnpifgjgakgivdjjaybimqxpmsek".as_bytes());
        let correct = [0x45u8, 0x24u8, 0x56u8, 0xcbu8, 0xb7u8, 0x79u8, 0x9du8, 0x5cu8, 0x0bu8, 0x3bu8, 0x82u8, 0x36u8, 0x03u8, 0x49u8, 0xfbu8, 0xe2u8, 0xc5u8, 0x7au8, 0x9du8, 0x1cu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("ulisiqcoqwivxguexfhzgizxbnuwujfopeakpshsitwofebapkncamegvqeuekcu".as_bytes());
        let correct = [0xcbu8, 0x67u8, 0xd8u8, 0xe1u8, 0x62u8, 0x0du8, 0x92u8, 0xa3u8, 0xc1u8, 0xecu8, 0x61u8, 0x6eu8, 0xecu8, 0x6du8, 0x92u8, 0xc4u8, 0xf1u8, 0x8fu8, 0x02u8, 0xd4u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("wyydvwwioegriueqilbakxyieadmitfhsqqpeumclbgnqtwiaasegedfwkskkzut".as_bytes());
        let correct = [0xdbu8, 0x2bu8, 0x64u8, 0x74u8, 0x08u8, 0x97u8, 0x34u8, 0x52u8, 0xb8u8, 0x72u8, 0x2du8, 0xc2u8, 0x5au8, 0x7au8, 0x16u8, 0x7cu8, 0x80u8, 0x4au8, 0xf5u8, 0xdbu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("gjysxfgcstvzkbbeyhibdspkexhnutbbudarzikfkbkfiihtjjdo".as_bytes());
        let correct = [0x08u8, 0x8cu8, 0xedu8, 0x46u8, 0x08u8, 0x64u8, 0x5du8, 0x45u8, 0xb8u8, 0xf8u8, 0xadu8, 0x0cu8, 0x1du8, 0xafu8, 0x1du8, 0x3cu8, 0x93u8, 0x19u8, 0x8bu8, 0x1bu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("gpxsibfhhcedqbnpckeuseltrdebyxzhxjfnxxnmssilcdqxldwbpdojoyngdkju".as_bytes());
        let correct = [0x6fu8, 0x86u8, 0xe5u8, 0xeeu8, 0xe7u8, 0xa9u8, 0x0eu8, 0xbdu8, 0xc5u8, 0xdfu8, 0x55u8, 0x63u8, 0xd9u8, 0x51u8, 0x6au8, 0x13u8, 0x39u8, 0xc8u8, 0x75u8, 0xf8u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("yexdiozrkzohvbpwodrjbxuydbqokqmtyockrirngogovbiedenfojpxxvjy".as_bytes());
        let correct = [0xb8u8, 0xf5u8, 0xdbu8, 0x39u8, 0x44u8, 0x37u8, 0x18u8, 0x40u8, 0xa2u8, 0xc8u8, 0x49u8, 0xf7u8, 0xe3u8, 0xbbu8, 0xe6u8, 0x97u8, 0xc5u8, 0xfcu8, 0xf6u8, 0xa1u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("lddkisqfinnlbmfyyxctxldmqgeokgbjpkstmmnewvyursjzmgcsgujmxzrdkxlq".as_bytes());
        let correct = [0x9fu8, 0x60u8, 0xbbu8, 0xeeu8, 0x3bu8, 0xf2u8, 0xcau8, 0x42u8, 0x7bu8, 0xdfu8, 0x33u8, 0x9au8, 0xedu8, 0x39u8, 0x15u8, 0x0eu8, 0x2cu8, 0x07u8, 0x4du8, 0x96u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("kyvfronpthoiyhvrkajgspoyavvgmobjddgpnqclnicqazcveaqdkjtgduihkmk".as_bytes());
        let correct = [0x57u8, 0xdcu8, 0x0du8, 0xbau8, 0xe9u8, 0x70u8, 0x45u8, 0x44u8, 0xe9u8, 0xffu8, 0x70u8, 0x12u8, 0x47u8, 0xbcu8, 0x1bu8, 0x84u8, 0x4fu8, 0x70u8, 0x8cu8, 0x63u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("dfyirkznvtcnorfnahhicdzwkdfzrmiexrtthnjivobvxkmjwq".as_bytes());
        let correct = [0x12u8, 0x5fu8, 0xb7u8, 0x3eu8, 0x4eu8, 0x27u8, 0x68u8, 0x2fu8, 0x68u8, 0xecu8, 0xbcu8, 0x0fu8, 0xc1u8, 0x50u8, 0xdfu8, 0x9du8, 0x20u8, 0x19u8, 0xf8u8, 0xc5u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("pbbjpyzrceogdyyfkcetnqzhrgzszjsgpwbnqasuqoagqabfgqtuccfmrhzdlsubw".as_bytes());
        let correct = [0x1au8, 0x7au8, 0x74u8, 0x25u8, 0xe6u8, 0xb3u8, 0xf0u8, 0x8bu8, 0x1cu8, 0x08u8, 0x7cu8, 0x14u8, 0x27u8, 0x67u8, 0x23u8, 0xb3u8, 0xa7u8, 0x2eu8, 0xeau8, 0xc2u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("ykxcouwqsulevarsarxvbswulsbozpaidhpguhrldcchaywvtptdbrfdfburq".as_bytes());
        let correct = [0x7fu8, 0xb3u8, 0x55u8, 0x83u8, 0xa2u8, 0xa4u8, 0xb4u8, 0x9cu8, 0x14u8, 0x89u8, 0x6au8, 0x43u8, 0x6bu8, 0xffu8, 0xfbu8, 0xb8u8, 0x7bu8, 0x76u8, 0xf2u8, 0xfau8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("wiwneduzbennxxwxlpgzjdxuxibsvwnxhfwhbxeuscqcmmdlzdntm".as_bytes());
        let correct = [0x09u8, 0xe2u8, 0x06u8, 0x36u8, 0xcau8, 0x69u8, 0x30u8, 0xcbu8, 0x86u8, 0x5au8, 0xd7u8, 0xedu8, 0x27u8, 0x9du8, 0x31u8, 0xb5u8, 0x5au8, 0x93u8, 0xd5u8, 0x26u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("udclddrbjzajuosrazngclpdeeybkjmjypxffqxxtsivptorqzwenvh".as_bytes());
        let correct = [0x90u8, 0xbau8, 0x45u8, 0xa8u8, 0xa3u8, 0xc3u8, 0xd9u8, 0xd6u8, 0xb7u8, 0xe9u8, 0xe6u8, 0x4eu8, 0x0eu8, 0xb6u8, 0x4eu8, 0x7eu8, 0xd4u8, 0x4au8, 0xc3u8, 0x05u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("pcjzgvwqszddihoqvihiplowkpnzyexmdrefonrjthzzhqzzab".as_bytes());
        let correct = [0xd0u8, 0xa9u8, 0x4cu8, 0x76u8, 0x46u8, 0x7cu8, 0x4bu8, 0xd0u8, 0x21u8, 0xa6u8, 0x82u8, 0x2cu8, 0x47u8, 0x91u8, 0x2du8, 0xc7u8, 0x2bu8, 0x15u8, 0x00u8, 0xbcu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("viceaqsaausnpkmvjegeodslcmduvliypddodlbqcnuyhhjhqlhjezbmazhycmrye".as_bytes());
        let correct = [0x32u8, 0x5bu8, 0x5au8, 0x92u8, 0x56u8, 0x8au8, 0x3eu8, 0x33u8, 0x1au8, 0x56u8, 0x85u8, 0xb7u8, 0x0du8, 0xd8u8, 0x60u8, 0x6fu8, 0x0au8, 0x00u8, 0xbdu8, 0x6eu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("dtaknbidnocquucxzwmdoirwxprojexgvjimtmfyxvxngcwgogmsb".as_bytes());
        let correct = [0xa7u8, 0xa7u8, 0xe8u8, 0xb1u8, 0x80u8, 0xd2u8, 0xc8u8, 0x69u8, 0xbbu8, 0x23u8, 0x3du8, 0x7eu8, 0x0eu8, 0x14u8, 0xb9u8, 0x33u8, 0x2fu8, 0xbau8, 0x5eu8, 0xd3u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("rezixdtmjsiunkfdgbkeytcbuyltpponnyhvrpfcjcymsogdlmmdwxmblzgggqkahuwjl".as_bytes());
        let correct = [0xb3u8, 0x2du8, 0x9cu8, 0x03u8, 0x16u8, 0x96u8, 0x5fu8, 0x92u8, 0x1cu8, 0xacu8, 0x91u8, 0x86u8, 0xefu8, 0xe6u8, 0x8du8, 0x56u8, 0x68u8, 0x34u8, 0x91u8, 0xa1u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("xolhvmjnunykcmxkgxouihduspavuqhdllcegioyqawlxehbtygqsqknxynqbwftqpjqt".as_bytes());
        let correct = [0xfeu8, 0xc9u8, 0xb3u8, 0xb3u8, 0x00u8, 0x9cu8, 0xf8u8, 0xf3u8, 0xbdu8, 0xabu8, 0x4bu8, 0x07u8, 0x1du8, 0xa1u8, 0x5eu8, 0xbau8, 0x27u8, 0x15u8, 0xedu8, 0xadu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("hanajfmayellbdshtzfofjmrjpdljqpzedxytcqdwhlkepnvwxvpwgljsivxfnyjj".as_bytes());
        let correct = [0x8cu8, 0x29u8, 0x93u8, 0x50u8, 0xf5u8, 0xc6u8, 0x99u8, 0xafu8, 0xabu8, 0x84u8, 0x32u8, 0x0fu8, 0x94u8, 0x37u8, 0x61u8, 0x33u8, 0x90u8, 0xb2u8, 0x31u8, 0x59u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("mefowmodpbrvwzdjgdrhfgzulqfrfmbiffdsjblsnxfhguzcaswmerwvvinonjbusrmzl".as_bytes());
        let correct = [0x87u8, 0x34u8, 0x61u8, 0x96u8, 0xa9u8, 0x1bu8, 0x43u8, 0xe9u8, 0xb7u8, 0x67u8, 0x1eu8, 0xc1u8, 0xdfu8, 0x75u8, 0xb2u8, 0xe1u8, 0x21u8, 0xfeu8, 0x6bu8, 0x94u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("lthvcnsgerpzwetxjuvticzvyxjfbeqzqjrufpptxphxqcuwdzqyyy".as_bytes());
        let correct = [0x54u8, 0xffu8, 0x9eu8, 0x28u8, 0x33u8, 0xe7u8, 0xa5u8, 0xeau8, 0xe2u8, 0x98u8, 0x7eu8, 0x70u8, 0x2bu8, 0x2au8, 0xe4u8, 0xefu8, 0x46u8, 0xa2u8, 0xb6u8, 0x63u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("inguvkvusfzaiwaaaqcjpfbtjveluxhzygosayndvcrplegpxghvfx".as_bytes());
        let correct = [0x6du8, 0xaau8, 0x1fu8, 0x21u8, 0x81u8, 0xbeu8, 0xfeu8, 0x66u8, 0xd6u8, 0x72u8, 0x1eu8, 0xb4u8, 0xa3u8, 0x3du8, 0x4du8, 0xf0u8, 0x56u8, 0xf7u8, 0x90u8, 0xcdu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("ygnrgttatqocmyvhjfwfgzpxdvwfhystybgvnkqyvnvrxgmtrxdgkqlpokuqdhmicecp".as_bytes());
        let correct = [0xfcu8, 0x8eu8, 0x43u8, 0x48u8, 0xf5u8, 0x8fu8, 0xb2u8, 0x46u8, 0xc5u8, 0x26u8, 0xdcu8, 0x49u8, 0xe9u8, 0x07u8, 0x39u8, 0x57u8, 0x55u8, 0xafu8, 0xd5u8, 0x36u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("ficshdrroioqjdbgzrjsvolgrdgufrgvnetevarccgsmfxkzmaatipeedg".as_bytes());
        let correct = [0x02u8, 0x40u8, 0x89u8, 0x4fu8, 0x27u8, 0x12u8, 0x09u8, 0x3bu8, 0x93u8, 0x6fu8, 0x0au8, 0xc7u8, 0xedu8, 0xeeu8, 0x8eu8, 0xd0u8, 0x77u8, 0x1eu8, 0xa3u8, 0xc5u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("wnvdkrxlkxfxvaavedqgjugxhdmwlnfuamtxlvatnfdpqlvakptiszuhy".as_bytes());
        let correct = [0xdfu8, 0x4du8, 0x07u8, 0x4cu8, 0xd6u8, 0xb5u8, 0x0bu8, 0x31u8, 0xb2u8, 0x5fu8, 0xc4u8, 0xbdu8, 0x23u8, 0x34u8, 0xa3u8, 0xa5u8, 0x06u8, 0x7fu8, 0x2du8, 0xa3u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("atxlcvqoiigzimqijoslfllxctwmeqliwcrwnfesfbygmsogeddkkzizhvmh".as_bytes());
        let correct = [0x7du8, 0xe5u8, 0x58u8, 0x33u8, 0x61u8, 0x2au8, 0xc8u8, 0x07u8, 0xbau8, 0x8du8, 0x3du8, 0x96u8, 0x69u8, 0x76u8, 0x75u8, 0x1du8, 0x1bu8, 0x0bu8, 0x71u8, 0xfdu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("sjkvjuakrdhtfbkkjrncdqiseimflqbowmtsdgvikvkdeeoyqqxnvffqqlwkk".as_bytes());
        let correct = [0xdbu8, 0xe2u8, 0xaeu8, 0xf0u8, 0xc3u8, 0x6au8, 0x4du8, 0x40u8, 0x11u8, 0x97u8, 0x17u8, 0xf5u8, 0xcfu8, 0xa5u8, 0x46u8, 0x91u8, 0x9au8, 0xf5u8, 0x88u8, 0x28u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("fwilglucwyegjvdusinruybetrasblmhmtciyizbrecwivndauzb".as_bytes());
        let correct = [0x65u8, 0x47u8, 0xe5u8, 0xb9u8, 0x27u8, 0x5cu8, 0xd9u8, 0x77u8, 0x9cu8, 0x23u8, 0x5du8, 0xf6u8, 0xb6u8, 0xafu8, 0x7fu8, 0x46u8, 0xf3u8, 0xa3u8, 0x3au8, 0x8cu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("xtucrmvnqvuzncoqxqgusjxokcrsejcmawgwuaogexgeititbnijiuna".as_bytes());
        let correct = [0xa0u8, 0x0cu8, 0xfau8, 0x84u8, 0xbbu8, 0x00u8, 0x4au8, 0xd4u8, 0x8cu8, 0xdau8, 0x9cu8, 0xf8u8, 0x3fu8, 0xaeu8, 0xccu8, 0x7du8, 0x13u8, 0x98u8, 0x16u8, 0x76u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("gibqddqvipptmlbhktpkokdooktphojqmtefcvozedicrlscymudjxrzzysbvuud".as_bytes());
        let correct = [0x1fu8, 0x01u8, 0xb0u8, 0xdau8, 0xcfu8, 0xdcu8, 0x6au8, 0x96u8, 0x75u8, 0x87u8, 0x91u8, 0xd6u8, 0x70u8, 0xd4u8, 0x61u8, 0x99u8, 0x65u8, 0x72u8, 0xe0u8, 0xf4u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("zdagaquzqohctqqajgizqwcdwmenwtvrludorpqwrgwopwpdcnxsewkotkgcxkxwcpdyld".as_bytes());
        let correct = [0xacu8, 0xedu8, 0xaau8, 0x12u8, 0x24u8, 0x6du8, 0x46u8, 0x96u8, 0x6fu8, 0x94u8, 0xb0u8, 0x05u8, 0x57u8, 0x13u8, 0x98u8, 0xc8u8, 0xf3u8, 0x11u8, 0x91u8, 0xc6u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("anrbsmprybwfhoperxwijlfglcsblhmrcxynzvkiayuntcjqks".as_bytes());
        let correct = [0xe6u8, 0xd1u8, 0x3cu8, 0x30u8, 0xf6u8, 0x2du8, 0x47u8, 0xffu8, 0xa5u8, 0xb5u8, 0xd3u8, 0xc4u8, 0xfdu8, 0xf2u8, 0x09u8, 0x60u8, 0x42u8, 0x87u8, 0x29u8, 0xcbu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("bswldcfhccadwedstzwcgxvcvbcbeegwhcfsrlunzrartmqlwg".as_bytes());
        let correct = [0x90u8, 0x84u8, 0xa9u8, 0x8au8, 0xc2u8, 0x8du8, 0x67u8, 0xe9u8, 0xd5u8, 0x93u8, 0xc9u8, 0xfeu8, 0x8du8, 0xf3u8, 0x5fu8, 0x06u8, 0x92u8, 0xadu8, 0xb1u8, 0x00u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("lixgbgqchxphdicrvekhranlkbcsaidinuxwhwlsrcsojfmcrbylqyedbaqqovcbnwfd".as_bytes());
        let correct = [0x19u8, 0x7au8, 0x40u8, 0x1cu8, 0xe6u8, 0x9cu8, 0x8bu8, 0xc9u8, 0x06u8, 0xe0u8, 0x1bu8, 0x3bu8, 0xd4u8, 0x3fu8, 0x72u8, 0xdeu8, 0x00u8, 0x8cu8, 0xdeu8, 0x92u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("rvapvmypnqooultnsbxzvarpofkipvpusnxnlivddakmcoekvihkabflck".as_bytes());
        let correct = [0xdbu8, 0x99u8, 0xa9u8, 0x0bu8, 0xbcu8, 0xdeu8, 0x67u8, 0x56u8, 0x3eu8, 0xc7u8, 0xb6u8, 0x1eu8, 0xb1u8, 0x31u8, 0xffu8, 0xecu8, 0x2cu8, 0x20u8, 0x6eu8, 0x17u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
        let result = Ripemd160::digest("cludkoqupkgskdrxluuorzpjchiqyhgesnfafiulykefcpvgajofvdaqewvoovhcxadme".as_bytes());
        let correct = [0x77u8, 0x20u8, 0x5cu8, 0x48u8, 0x8au8, 0x65u8, 0x00u8, 0x7fu8, 0x1bu8, 0xa8u8, 0x3au8, 0xedu8, 0x3au8, 0xc9u8, 0x6au8, 0xd2u8, 0xedu8, 0x3fu8, 0xcbu8, 0xdfu8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
    }
}