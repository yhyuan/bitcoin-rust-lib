use core::ops::{Add, Shr};
use core::cmp::Ordering;
use core::mem::transmute;
use crate::field256::Field256;
use crate::u256::{U256, P};

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Point((Field256, Field256));

impl Point {
    pub fn new(field1: Field256, field2: Field256) -> Self {
        Point((field1, field2))
    }

    pub fn unwrap(&self) -> (Field256, Field256) {
        self.0
    }

    #[inline]
    pub fn zero() -> Point {
        Point((
            Field256::zero(P),
            Field256::zero(P)
        ))
    }

    #[inline]
    pub fn g() -> Point {
        let u1 = U256::new(0x79be667ef9dcbbac55a06295ce870b07u128, 0x029bfcdb2dce28d959f2815b16f81798u128);
        let u2 = U256::new(0x483ada7726a3c4655da4fbfc0e1108a8u128, 0xfd17b448a68554199c47d08ffb10d4b8u128);
        let field1 = Field256::new(u1, P);
        let field2 = Field256::new(u2, P);
        Point::new(field1, field2)
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
        // let U256((x0, x1)) = x.u;
        let (x0, x1) = x.u.unwrap();
        // let U256((y0, y1)) = y.u;
        let (y0, y1) = y.u.unwrap();
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
        // let U256((x0, x1)) = x.u;
        let (x0, x1) = x.u.unwrap();
        // let U256((_, y1)) = y.u;
        let (_, y1) = y.u.unwrap();
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

#[cfg(test)]
mod tests {
    use crate::point::Point;
    use crate::u256::{U256, P, N};
    use crate::field256::Field256;

    #[test]
    fn point_add() {
        let n_7 = Field256::new(U256::new(0u128, 7u128), P);
        let p1 = Point::g();
        let p2 = p1 + p1;
        let (x, y) = p2.unwrap();
        assert_eq!(Field256::new(U256::new(0xc6047f9441ed7d6d3045406e95c07cd8u128, 0x5c778e4b8cef3ca7abac09b95c709ee5u128), P), x);
        assert_eq!(Field256::new(U256::new(0x1ae168fea63dc339a3c58419466ceaeeu128, 0xf7f632653266d0e1236431a950cfe52au128), P), y);
        assert_eq!(y*y, x*x*x + n_7);
        let (x1, y1) = p1.unwrap();
        let (x2, y2) = p2.unwrap();
        assert_eq!(x2, Field256::new(U256::new(0xc6047f9441ed7d6d3045406e95c07cd8u128, 0x5c778e4b8cef3ca7abac09b95c709ee5u128), P));
        assert_eq!(y2, Field256::new(U256::new(0x1ae168fea63dc339a3c58419466ceaeeu128, 0xf7f632653266d0e1236431a950cfe52au128), P));
        assert_eq!(x1, Field256::new(U256::new(0x79be667ef9dcbbac55a06295ce870b07u128, 0x029bfcdb2dce28d959f2815b16f81798u128), P));
        assert_eq!(y1, Field256::new(U256::new(0x483ada7726a3c4655da4fbfc0e1108a8u128, 0xfd17b448a68554199c47d08ffb10d4b8u128), P));
        let s = (y2 - y1) / (x2 - x1);
        assert_eq!(s, Field256::new(U256::new(0x342119815c0f816f31f431a9fe98a6c7u128, 0x6d11425ecaeaecf2d0ef6def197c56b0u128), P));
        let s2 = s * s;
        assert_eq!(s2, Field256::new(U256::new(0x38f37014ce22fc29cf19f28a5ce4da09u128, 0x1445536c3e2cff318ba07c2a3048f518u128), P));
        let x3 = s * s - (x1 + x2);
        assert_eq!(x3, Field256::new(U256::new(0xf9308a019258c31049344f85f89d5229u128, 0xb531c845836f99b08601f113bce036f9u128), P));
    
        let y3 = s * (x1 - x3) - y1;
        assert_eq!(y3, Field256::new(U256::new(0x388f7b0f632de8140fe337e62a37f356u128, 0x6500a99934c2231b6cb9fd7584b8e672u128), P));
        
        let p3 = p2 + p1;
        let (x, y) = p3.unwrap();
        assert_eq!(x, Field256::new(U256::new(0xf9308a019258c31049344f85f89d5229u128, 0xb531c845836f99b08601f113bce036f9u128), P));
        assert_eq!(y, Field256::new(U256::new(0x388f7b0f632de8140fe337e62a37f356u128, 0x6500a99934c2231b6cb9fd7584b8e672u128), P));
    
        
        let p3 = p2 + p1;
        let Point((x, y)) = p3;
        assert_eq!(y*y, x*x*x + n_7);
    }
/*     
    #[test]
    fn point_mulitiple() {
        //assert_eq!(Point((FiniteElement(U256::new(0xcd5cd78e17f6faf3bd045f1b71ad9053u128, 0xc5f13f6d79a28ee1deff1e2c0852a771u128)), FiniteElement(U256::new(0x0c91336c9d739dc9840755404441f2beu128, 0xb596b7322202828d4d14b28c78acbee1u128)))), Point::g().multiple(U256::new(0x61c20033a14357ce57747697d7e80893u128, 0x46e76a5bfa360954cd0baa23f1d6e4f9u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xeab2fa3463f05722f18da474a4065e2fu128, 0x6e773b7b4550bf632137b60685495138u128)), FiniteElement(U256::new(0x69da3eefd549a839e4241e181fbd6d68u128, 0x214b267af050aea7b80a0c7fa8fd1847u128)))), Point::g().multiple(U256::new(0xf2466907b8e9b359c1149b63e8f888e8u128, 0xe49eb045e412311b75985789246451a9u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x1e9f74e4f2649951b755d6ae9ee69395u128, 0xd4fe0fed96aa8f8eba19e5875f452e98u128)), FiniteElement(U256::new(0x55ba50709b01bbc7af2f137a87741cf4u128, 0xdbbf77b24e5d6d45899155fe32348e15u128)))), Point::g().multiple(U256::new(0x42b4f2b18018754260447cb7913c9bb8u128, 0xb3e222e4ce30f5596179b0969c7ba503u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x18514056ba18350c44e2ee847df113fdu128, 0xda695414cc97bdcd3fdb8df155608d39u128)), FiniteElement(U256::new(0x28a4c4f39cab47bf9c34edee47ca5834u128, 0x27fc41ffd24f0aadbe71949bfb7c252du128)))), Point::g().multiple(U256::new(0xe56c0b2626fe9994a894e63572c4c1ecu128, 0x153cb9602b4cf901a69d3be094a9f279u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x537642fe714a4db59bd11bded895516cu128, 0x5a58d1f025ffcbf4fdba51cacc13ea06u128)), FiniteElement(U256::new(0xf5287363376fa2b5ff7ede46d803de68u128, 0x579875c6c5c19048d7bc305a150dba2fu128)))), Point::g().multiple(U256::new(0xf97115b4ef1e2cb2efdcaa97dc8de32cu128, 0x9123462dac19329bf3ea5cffb8ef8baeu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x53f3ea6ff822f7640f62f207169fc3bcu128, 0xfa1e96dc319a8d9afb4ed0b3f4520377u128)), FiniteElement(U256::new(0xbb5883b1ee4735d294ea7cc30f996e5eu128, 0x53b35b091d9ee3e3cd15d1ae987905b7u128)))), Point::g().multiple(U256::new(0xd003f7b4aef851bedb7e1efbae414dd6u128, 0x58a6b3b215dd2a651fa364185a3d8064u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc5dfdd15413165e6d1770163010b5d5au128, 0xad910512775288935e283c0b39349b56u128)), FiniteElement(U256::new(0x5143720346fcaadd0119fde3ecc3f37du128, 0x581c38317dc87bd5540219d04b3ea284u128)))), Point::g().multiple(U256::new(0xc502c1083a5be657dc9bf4c6c9c131bfu128, 0x9f0d544a92ea318f47c26dd5fa3b43d6u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x6c02c74ccbee9f9ab6fb896b8b83f478u128, 0x8a66be0f399b1063993baa8d18bc529au128)), FiniteElement(U256::new(0x0e757f2f163f16ea6645cd6be9f1ac63u128, 0x55d9a160da3376c987d5668373d420ebu128)))), Point::g().multiple(U256::new(0x4552649dc3d18fa147020ff29a608dbcu128, 0xd3b2c3d6fe57fb834174b2c701e2dab9u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xb555620162af0648bfffbb0cbc9cc231u128, 0x2077299f46a187cf93fdc502d53af697u128)), FiniteElement(U256::new(0xcdfec2230258a0516562939a4c7fa6b1u128, 0x4dd56773a4b7fe139e61724b5b8c10d2u128)))), Point::g().multiple(U256::new(0x05d8457529b44934508bd22d6d66d907u128, 0x9622c71d40c1db6beff63c22acfd8b37u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x528d72483d424c67c035749b809535fcu128, 0xfc7c769fba64eccf141f1837e3a0740fu128)), FiniteElement(U256::new(0x6385baf1f25545eff82c3874f60b180cu128, 0x5f5f5ef1e51ac8004e0771e1d5a2b338u128)))), Point::g().multiple(U256::new(0xbea27c34909ee5bd1600053b2e616727u128, 0x1bb95dc879984af768fcafe5d14b4dbeu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xab4c6d70f8de42b7b00cc15dfba9e055u128, 0xaa9a767890faedfc474ef11338334026u128)), FiniteElement(U256::new(0xec7bea9aff268279036d6ab4546fffcbu128, 0xb60bead9841054970bef8e65a19411dcu128)))), Point::g().multiple(U256::new(0x592bf80985fd7728b7e846d9f40971edu128, 0x117ec46cfd6db337dd86dbfae793cbc3u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x999eae9befae604598d2dad09b9ce9fdu128, 0xe98fe0214ecb2e5fe0567bdf0ee577b8u128)), FiniteElement(U256::new(0x1fde2d59d687f2f057ff906eab0f1c7cu128, 0x1db1f7fa53273b5d91e13426f03e3fafu128)))), Point::g().multiple(U256::new(0x56135dd5ffda868568a03268ffd592fbu128, 0x0a004c800fca688486fa685751e85445u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc7492da89642e723b92b638b040d9418u128, 0x6b81bf9b4314ffc4440a64e88f776bd4u128)), FiniteElement(U256::new(0x4bf2e35851c1a7263651d51db76a6facu128, 0x394e806756ce35989a21903058d11906u128)))), Point::g().multiple(U256::new(0x2395fa27598d18a584a2708c865594b2u128, 0x0cf0526071dc64e8f6e09bd6f96a690eu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x4cfe45b63815afac2e883f4843654701u128, 0x93da2e76a0b6ac5870ad30a34d50c163u128)), FiniteElement(U256::new(0xb57eb37c2f6911a6f371557e1224cf59u128, 0x141794f0afaf743b323dc7e48a2b4dd3u128)))), Point::g().multiple(U256::new(0x038c1d2ce6a04b09d2ff04cb2fcc08c5u128, 0xd41e1d1315e7ab3a532f4e4c25f339c8u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3683150e4414315e96d7f5a7ec6b2f67u128, 0x2970daf9c2f627f94f2e7c877601a77eu128)), FiniteElement(U256::new(0xc76e4c916756f51774ec83766382703du128, 0x67b2bff5ebb59f36aa0a452c7b4164c2u128)))), Point::g().multiple(U256::new(0x6be2b6867b74b69ce5b45ba59325a9b3u128, 0x3cbc0a5192c6ac46685286d2ad49f8d7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xb8da0131028041aa8487c426dca954b4u128, 0x7a598a2982b4473a62ae18e89302dd83u128)), FiniteElement(U256::new(0x0d2ade4590fd584769b6a392f51fc31au128, 0x3945f91b092793a0aa6d1fcec8e1863cu128)))), Point::g().multiple(U256::new(0xc4d22407785ee38eefa8622f26118c78u128, 0x69dd0fb694c89a50c2f8f6a891c7a091u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xe9aae9722521c411107d88adbd33ae45u128, 0xae3ed51eebfc7df8ade4e88ab00a4292u128)), FiniteElement(U256::new(0xce46cc7c3f82e929a26188178493eadfu128, 0x43c2885368a86d86dc9992c877e9bcbbu128)))), Point::g().multiple(U256::new(0x08f0fd55d2928f55ce569cbe9d249241u128, 0xbc77dab83bc46dfa6aa8522f1fbdf164u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x26d0d94b7825ca38622c16d7b08445e0u128, 0x38fd521812df45a67c0a29a708e5a8f9u128)), FiniteElement(U256::new(0xb6cfa65a0685b00085140751a9d4efd1u128, 0x18ee5f911e93e812ba1319d2701a20bcu128)))), Point::g().multiple(U256::new(0x5d364f3e5ab3af4f5caabaf8f480554fu128, 0x9313a2efd5968945e89dcfccc7082cabu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x866213f519846b2df32ee14901d457c8u128, 0x2db83339d029c6be8913e296a092ae1fu128)), FiniteElement(U256::new(0x3a0998e628c03249b314cd7f3a5dc065u128, 0x7b6f8b9f60115fbdefca837f555284d7u128)))), Point::g().multiple(U256::new(0x0a2c9ef1392d133776306e10edfadd95u128, 0xc58f6aa74edc2a966cd9f63f549dd8c0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xd974825aa0566e3e9c91cd368676cd13u128, 0x6d829a0029f32fcb0df90a3c04cfe7fdu128)), FiniteElement(U256::new(0xda373f29deed5774409669dbc242bf64u128, 0x70049cfe282ec545c3f72ee29ead7154u128)))), Point::g().multiple(U256::new(0xfc12a100118b2039ca1ac8ebc9554fd8u128, 0x4017bc08bf4a2c4b21f4cef5c138f211u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xfb4095100b9b94f7b280dd3bce4a2e38u128, 0x93ae8dfafe17f70e567a770f6b6d7d50u128)), FiniteElement(U256::new(0x1d574e86b2f434360f866d5ad56e926eu128, 0x1dea71c7e4efe53ddf21914f321c0287u128)))), Point::g().multiple(U256::new(0x09b3709d99152adfca8994a100711604u128, 0x02a80589f3e90406fd0371a95432efdau128)));
        assert_eq!(Point((FiniteElement(U256::new(0xaf68fef5ca72af42397272ab2074321au128, 0xc420ecbfd5ba0d3786dac71fcd84be7eu128)), FiniteElement(U256::new(0xe6890044ebdd0ed442b925cd1958dd2eu128, 0xa89ee004882fb4c929d4cc8bf5f4ad73u128)))), Point::g().multiple(U256::new(0x0babb91e493a6fd5cefda59af0323faeu128, 0xcd47f7895bf943f9c5b40b0845257a40u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc203658599e1556790d78d67e04c6fc2u128, 0x12b7bf7ec4200c2c4f487f70cee38879u128)), FiniteElement(U256::new(0x9c34f57116ee6da5847c288e454f333au128, 0xb8602295532ba4a9aea4259d92d58549u128)))), Point::g().multiple(U256::new(0xda43b4c176815972d4fce9584f60d4d4u128, 0x558c8e59b8b911328ea2c57cfacf1470u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x4b7eddca79add983a033631ff9099287u128, 0xdf7ade31c7ff820ddf06df2a68d53c5bu128)), FiniteElement(U256::new(0xb65fefe33dc39b03a0c88a39fed3f076u128, 0x7e8eaef94ae4970b2dd4abc7648544fdu128)))), Point::g().multiple(U256::new(0x36cc4f1a453f99f7742c3e3f08a97ef6u128, 0x00cddce0f3f57971d7ce308720ebaa07u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3cf249c6ae651f59a3d4b375c6e3bb4eu128, 0x3999db17276fe80e4504cc606e9a7eecu128)), FiniteElement(U256::new(0xef28cb092972fb4ec6ea06294dbc8fbeu128, 0x292953799f965acaf325e91bbfc44210u128)))), Point::g().multiple(U256::new(0xd23399c3e92a7a337aa236d23de1560eu128, 0xdd8a394b8fb3a2c6f18c1a7d5d8ca1e8u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xeca8a7860f8e9e236af4940ea40cac72u128, 0xbb1a6026e446f34ce64f0ce0b8b184a3u128)), FiniteElement(U256::new(0x0a8741046bbab1db8af50b9b97f40131u128, 0xf08dd535d31367845b27c926711a2908u128)))), Point::g().multiple(U256::new(0x951c83b461f4c34a13e03f50a3be03e5u128, 0x5b3d559e60e51e7b874f9632a390a2d6u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x2f6de09aa452c4f08905d80107880da5u128, 0x1c328ffcc5759dbd11c61663a4a24397u128)), FiniteElement(U256::new(0x1d7e5c92dc92872ec243c99653fdc349u128, 0x53b864ccfc73cb4c4c477026b10be2c4u128)))), Point::g().multiple(U256::new(0x8d95908f52c667fb203383775c786b74u128, 0xb7428adfb6413cc361fd52ab39c1f6b7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xec88f09eb08e8e36cca96a3e1109f91du128, 0xe70c4568d3967d93f87d67e3a894711bu128)), FiniteElement(U256::new(0x3de6ef5e3e79445ebbd3eb6f7ad14c9fu128, 0x5d83c5110c0a63265cb220e12e29244au128)))), Point::g().multiple(U256::new(0x5e1d4184ff439781f3355f0aa3275b17u128, 0xefa17e9c2aa4019c95f138fdcedd48f4u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x08e53bf6cd90f25efeef11e47944463cu128, 0x870345c888141c3dd996a52fba067b80u128)), FiniteElement(U256::new(0x6bdfc3673b171932cad4cd1983020ce9u128, 0xa36ea9a8e1d5d2011b20224eb1eb2a44u128)))), Point::g().multiple(U256::new(0x2002ded61cd6171077b24db04a787095u128, 0x53f48be07faaa5e1da1b41c5c2a02db3u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xad57bdf5c0c983b2faf44d3a2b390918u128, 0xd8680f8f02c3c390a0a6992eee9416dbu128)), FiniteElement(U256::new(0xf2505091f0ceff2e37445145005c995cu128, 0x123eef12e7c9d167e61c9dac79b918dbu128)))), Point::g().multiple(U256::new(0xc5312a54e67aa9d08b58dcce8608358fu128, 0x955553aaff2e85b08ace38ff961269f4u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x2f67963f9f977b534ff91f679c5504b3u128, 0xc3c064e56f81ff87aa438f0f34faa95du128)), FiniteElement(U256::new(0xf2100efdec1e7843a8ee8a4faf09b1d4u128, 0x807f818170d3544d3bcaff89f1a46573u128)))), Point::g().multiple(U256::new(0x1b9d46dee039e81e938759daad221997u128, 0x5a68f27f39bbcea71f4c6756018c68efu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xa14186a687cd111249533ccfb5a67629u128, 0x8b05e1f1a88f813377a58008f4cca75au128)), FiniteElement(U256::new(0x434ac8e1b3eb4154f4874fe6888a79dau128, 0xb8765398e18cfdd8844a645c939e365eu128)))), Point::g().multiple(U256::new(0xfa51e5ae8775346ce40daca141c4905du128, 0xda927277c3009bc1242ceeb3c632078au128)));
        assert_eq!(Point((FiniteElement(U256::new(0x7add9efec6dfcb53a906bc82783e3596u128, 0x4c64d4dd7988ad67975233ff4e89e199u128)), FiniteElement(U256::new(0x114d403ed11f43856c554d6029fa6566u128, 0x39d2a83d1d111491a06f8fadd08e160au128)))), Point::g().multiple(U256::new(0x56061cbe554d217914ba93a7b0b945c1u128, 0xf1b054b669f9d5f809bc87d8aa3e7d43u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf68dd6aaf79e81d5c5d10b7e7d2db782u128, 0xbfd027b6e2863e5ce9e7a1dbb103903bu128)), FiniteElement(U256::new(0x622530efab3126bb707b7251ca7bd9a7u128, 0x78c23f4ad642f67bb4576598dabcd8f7u128)))), Point::g().multiple(U256::new(0xd1ad77259362b1f4c17eedd51bd93fe3u128, 0xaf7524b5a4a1e1d77c1c7d1eed80e44cu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x1a38411ccbe7dab87fd9aaee0deeb6d0u128, 0x896609198061e75e89e9238b0f20705bu128)), FiniteElement(U256::new(0xd4bc2272de4bb499c2c01aed563fcf98u128, 0xe40834b58ec637bfe94c6e63bff41995u128)))), Point::g().multiple(U256::new(0x692578333f400ea4adb587d3cb740147u128, 0xb6fff82cc0fdaea09a36e8e8f262a833u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x5a77b076a40474109834b09b0ea4f659u128, 0xf32232c7b5d87ec0f992cf05f85431fdu128)), FiniteElement(U256::new(0x36994b6a8d3b0ad57426e39fb1dd9e23u128, 0xe6e576449e173861c5f42e5a0ba5838au128)))), Point::g().multiple(U256::new(0x05517e26c12bbc75179716cf6003bcecu128, 0xda9aaa6963a08bd0a648292b01d0b038u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x105481bdde90fe29f1530fa1a753edafu128, 0xa69a657edf4838f70fd5ebfece9b4df2u128)), FiniteElement(U256::new(0xb1ae95f2eba075f65a08644eaff4a717u128, 0x7149859f0aad883445921f5bc3261941u128)))), Point::g().multiple(U256::new(0x72ab53e436bfa345f154e9f14eaa0efau128, 0x31e5bf983036a0c366695e8e2be69431u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xfa63c60b351aed679cf5d99923f632ebu128, 0x30636202d7c2600d6fbd1a39d8dd2409u128)), FiniteElement(U256::new(0xca3b3dfa24fb093879b5cbf6273e64deu128, 0xf3c55311a14a33b497b0b1969e3f7c7du128)))), Point::g().multiple(U256::new(0xd313d87a76c85840d2b2f397d966e3a5u128, 0xea4ccb0b7286acccb7f6752e932e7d5du128)));
        assert_eq!(Point((FiniteElement(U256::new(0x905e761856e8db7ce9635da05523630fu128, 0x5bb0f4ac50c36a3f32feb1ae30737300u128)), FiniteElement(U256::new(0x1bc8faac1b0f0a8ef46bd20fa7cb4d0bu128, 0xfd8ac4ac9d2def973f9c71cbf45b5f50u128)))), Point::g().multiple(U256::new(0x78373e8c0b51fab8a9bf59c107cdc4cbu128, 0xb08da277be1ef313161e923bc7dec866u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x4a15a845c51c1db1d96c4fd874cb60b5u128, 0x36ab193db1d439e4884fdc09ca9207b8u128)), FiniteElement(U256::new(0xeedc7266d6b5d052ad6776f029f9e98bu128, 0x9d4eb04e494fd9d35eddba615865ce2cu128)))), Point::g().multiple(U256::new(0x48f1a0751cd285e4f0f2992181e8652eu128, 0xd89ed7673abdb761d379bba66fd69d81u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x6244aaefde1ea214077cad8a48be6506u128, 0x4c3af7c462203c8d7aee74532bd3e4f1u128)), FiniteElement(U256::new(0xf3275acafe94be14f8602c35a448456cu128, 0x00ed407d88c65d1f842483aa1ae3bee4u128)))), Point::g().multiple(U256::new(0x1e18414c31f88de5d4db272e19a4ceb5u128, 0x4506fe447fd92a5b0442bc4fe27e10ebu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf6b4a00b80ef265a60c59eb11d0168b8u128, 0x9e8a7e9baff35a7e5a8c8ddcff8204bau128)), FiniteElement(U256::new(0xe7662628caa5e5ab1b6d4a838e5cf5a9u128, 0xc26b2da39c56e22b191a7d4fd5beeb96u128)))), Point::g().multiple(U256::new(0x401ff8889add00461e01d49b9a83b2a4u128, 0x94ed52fbf9e31a7a32fad23c165b31f5u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xa0e6dc283af398bd0c73cfbdebbb3c91u128, 0x51de0419534590cac4575422e32aad73u128)), FiniteElement(U256::new(0x58b6e5f3252239220f4f6e4ea2a8671du128, 0xdeacc7e9bfba321d73e56458c340bbbbu128)))), Point::g().multiple(U256::new(0x39d68b1c921e20fe5cdf643da037c18bu128, 0x73d8139b33873dd3d1ef8bd945e41e00u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3609fc6b021e429cae5c0e409083fc39u128, 0x658347bbe286c4664d719a0c846527c5u128)), FiniteElement(U256::new(0x5e982c037bf654d89e5287b348853129u128, 0x2cac2df4eb01956442ad651808473acdu128)))), Point::g().multiple(U256::new(0xc4fb0ad7270a9d6111b0e13df166bcecu128, 0xe1d0a5376c867ad81c787a6451f9e2eeu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xfc6aced404be185a10065001bdc71674u128, 0x981ac6fa7447e6ab8342a3449f5019e5u128)), FiniteElement(U256::new(0xbee5ca8a1958b64fa2af8f4a1d6a489eu128, 0x56ddc647cb63819eb34036e6688a8f7eu128)))), Point::g().multiple(U256::new(0x16bcca4a34b3d560a3fbe4f870df3ddau128, 0xe61b1c37490007d771ca8adb9d018731u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x00563dc1adac10ab05719e4defab6aacu128, 0xa7d5c8aa275d66d07c820ba8606edc46u128)), FiniteElement(U256::new(0x1b55bb9bef6886e33c0fa87b7d602216u128, 0x55455c79a941daa74ec4af52d24cf20eu128)))), Point::g().multiple(U256::new(0xfa04d1f82a54565b6617ae7793142c10u128, 0x37fe51a4e17eaa85e50ee816f676a942u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x176ee510ba9e03d3fe83dc0ff5ac8437u128, 0xa94f968672fcf578d3b9d565dd1932d9u128)), FiniteElement(U256::new(0xc39d714bb26803a80a50de4166027db0u128, 0x0f03b339d37abe17ef4397182146fd3du128)))), Point::g().multiple(U256::new(0x4a947d2e49fee2d01126431899e734a7u128, 0x877df503be86a263cffb8b0bac17d9a7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x87dcba3a0cfebc95c12845e71709aceeu128, 0xadb33eff0d1953699faee48fabb45c73u128)), FiniteElement(U256::new(0x2d6d1513a9bd9e0082457d751e517339u128, 0xaa0ff1e91c4a55b0ab60b5f4f82b69a4u128)))), Point::g().multiple(U256::new(0xd97534fd817e8bfa43d030f84efab088u128, 0xd0a281a92312e288bb49d61eb116348cu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x8fe3cfd1772e252f05af4274ed8befe7u128, 0x0c01ae4c52ae99e50e52367aca6ef05cu128)), FiniteElement(U256::new(0x6a01e3d2e13af124be5ea20f6fc2a8a7u128, 0x244314dd5d2972d51a074f4d0528465cu128)))), Point::g().multiple(U256::new(0xd83488d25d4eab0274a3fa8d5171cb2eu128, 0x05f6317b3b91f0c4757d13f742127e6fu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x301454d005f3cd10ae5cc796a720b134u128, 0x79389cf0fa24ae34890c0d8c25657407u128)), FiniteElement(U256::new(0xda1fa927f2ba23cf2bcec1c931cfc8b4u128, 0xec7e3cbae8679b6ee12d80f6da3906cau128)))), Point::g().multiple(U256::new(0x6bdae832b608a7d9b68f216e4ede455au128, 0xf75ba6724660c2d18c0e4880a22e5f0du128)));
        assert_eq!(Point((FiniteElement(U256::new(0x4f2a0aea9c648d8fb2181bd8bebcad1fu128, 0xe86ac989187d52993d54ebbbfd487d4bu128)), FiniteElement(U256::new(0x56c2997fa3e08684cbc61e14e5546d29u128, 0xf0f0d0d061621d8894d516331c73bfe2u128)))), Point::g().multiple(U256::new(0xb5c70b3a1ea31ea4876180ccecb1187eu128, 0xf7d2b0e20d2b537d3a4c79371896a4f5u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x221079979409cd5f4d9525a3554fc757u128, 0xa02c8c898e3b06e1021134fcd93e0580u128)), FiniteElement(U256::new(0xcbda6a59987b2baff9f85531a2271845u128, 0x7aa173f4e724f6d9d204abbcea66823eu128)))), Point::g().multiple(U256::new(0x17024425f7080b09bc1ed2f3f2f3106du128, 0xb51861abcc388deb3225da317e403114u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x95b80880bc851d76b89bc22aa9da40c4u128, 0xee5318073c91404e9e85bf465d3e6278u128)), FiniteElement(U256::new(0x84f82f5f5a9a3b808e5a3e0572677543u128, 0xe6ddd689784144b2c2e847be7f04f3b2u128)))), Point::g().multiple(U256::new(0x29b581f1651acac266a9d01160d4ba9au128, 0xc8e447a6da31f1892f417f70388268b7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x6d0d72c3cb004d71e44211316bf97c21u128, 0xf789124dc8a8c45c49a1f67fd730a196u128)), FiniteElement(U256::new(0x88267b71165b0582b5a41cd3ee6f5ac0u128, 0x8f30d78931e6d8209cae9ba0062b69feu128)))), Point::g().multiple(U256::new(0xc5749f4af3a8ef7e589c479b8c211cd6u128, 0x1d6fbe0445dbf851c40276ccec9c7b18u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x32202156843bd574d13686cfd39f005bu128, 0x0b6fb2dbd7f28b189f3d5da834e7dc2eu128)), FiniteElement(U256::new(0x86793cde9cc3f41e6ab49ccc53c35d44u128, 0x8402ecebe11ddb260b5d413ff7c279c3u128)))), Point::g().multiple(U256::new(0xbb41e4b6462687b31dbf9f69d30cb9fcu128, 0x5a0a10e258c5bddd0507ed913cdb28f0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xb07914d77f780ce7c32883886a0f6f4eu128, 0xaef1bfae56e191d6453200fdc63227d5u128)), FiniteElement(U256::new(0x66e8c191f97a6a9842c63f4188a85099u128, 0xc59f279de748f89d5c73104bfc9809beu128)))), Point::g().multiple(U256::new(0xce5a7f1565b8e2cbd077bf8d0d222da9u128, 0xb41a21571182a70084000f69fd91af19u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x52cc244d5e465f2fe7b38aba04cce053u128, 0xc6021a5077e69d19201f059810e0c907u128)), FiniteElement(U256::new(0x1e65050e94f872fa4ed7ff544ab31598u128, 0xc0a0983e35f121001a381fd5fe868059u128)))), Point::g().multiple(U256::new(0x538176f836fa15b82d6fea81448a1585u128, 0x81d8b9a92df87bf4a6874a31b41b079du128)));
        assert_eq!(Point((FiniteElement(U256::new(0x1a95ac5fe3209de4baa39d9284937488u128, 0x911ed877bc284b8ffd0dcd1f1a7f8ab7u128)), FiniteElement(U256::new(0x0e533e41d74e530538d6c7bdfb54cc4bu128, 0xef6a2de5c5a9afd16023eb6aade5ce8du128)))), Point::g().multiple(U256::new(0xdf16f13e60b180363689af61dbb75500u128, 0x25b5a78bca4ed7d943b058413bb811a0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xcc542aef7faac46cf51a59de0dd2d186u128, 0x25032c4b0b6c58450a77d99f167b0e3eu128)), FiniteElement(U256::new(0xa86377a9d449997ea766dc32d03175a0u128, 0x1c50b5f6efa73ff145c69b153ef2ddd0u128)))), Point::g().multiple(U256::new(0x7525a51af45e6046f8d6042ce3c241c4u128, 0x9e117c745a75b6f6dad9ab7254fc436bu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x071a39140fd77545cadd29f2e275778fu128, 0x0b136e982e0a4f26eede2ed40a9ff592u128)), FiniteElement(U256::new(0xdd11e90d4ddf1609227a066235a781deu128, 0x73186901f4ce017d5ecb0a4bf31b24f2u128)))), Point::g().multiple(U256::new(0xf691f6d148030d613e51a1c977720d60u128, 0x8a302f0588b629cdd6fa1ecca3c0851fu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xed8bfc00405daba85227a4585519fd10u128, 0xa70a7d310fc3bfe1ffc4f72582552c73u128)), FiniteElement(U256::new(0x616a91bc27610d37d5ed176a6813e3d8u128, 0x86d723e87ca1f95bf30a13a37abe328eu128)))), Point::g().multiple(U256::new(0x99b40036eda534a2a140ad8718b6f53du128, 0x052b612bcccf0fbb01604e2e2dc33207u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x29c24483317e90d77bb01e3141a8357cu128, 0x5ae0996395e3170ac8eec511d713e15fu128)), FiniteElement(U256::new(0x46fa515b3e0657165b7a8c4fbd1a6dbfu128, 0x2a7cfc43750802beae529fd0ec7648bfu128)))), Point::g().multiple(U256::new(0x213d08784a05e64f3ddd145ba7bfd2bcu128, 0x2f33df5a80fa75c42a96758f16da16aeu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3b4eb849a703af4ef43eb5af04f23a5bu128, 0x16162e7d8234164bdbcf904c4d2e8887u128)), FiniteElement(U256::new(0x1598a29f9ee77395b2cff4005f274764u128, 0x3b1456ab87438581ae77ad1204d9266bu128)))), Point::g().multiple(U256::new(0xfbc9fd303fa295caead1072c060e20f0u128, 0x628afd86224a1039ea5f2b46604d5c4du128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc9e0d297ef9dc5ab13d762f39ea79379u128, 0x190770c8822126e569c3dc44623495c1u128)), FiniteElement(U256::new(0x3c8762c9fcb92f6bd38d8cc06c2cb3b4u128, 0xc4bd7a916743a5dfc8ba2b600f752ad4u128)))), Point::g().multiple(U256::new(0x7e24fc2b79dc7e879d55ccd4d81db4d4u128, 0xb634196508c36da9af4dc9ac96112769u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x0c9e4d6fa58a6643c6715bc099610cb8u128, 0x89f235848ec3ccb8fb7d10ce528f319au128)), FiniteElement(U256::new(0x592ed2befa2be5122000b724e08b7052u128, 0x3d42361c2bb338061b604783ccb87ddcu128)))), Point::g().multiple(U256::new(0xb9164617a7e833d3e38ebb98ec8e552eu128, 0x627de5737d2ef7753f764c18190986a1u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x2d1af695204f82faa2740bfc507a1a46u128, 0xd886d1cb2a965984d81ae4b304839416u128)), FiniteElement(U256::new(0xb5f15f2062ec50e3cc7ccd93ba0fea41u128, 0x648ba7530f486b4bfff89e339aceda0eu128)))), Point::g().multiple(U256::new(0x51e8cab6f497a28397016ca66314edc1u128, 0xd0d1533da22f98fd66e6b0930fb43b40u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xfe44b098c928890f002be1c65e945b3cu128, 0xad01414f262935365b5415bdd009e531u128)), FiniteElement(U256::new(0x80f458514cc7a6c1fbbae24dbfd3efd2u128, 0x837a559b9b63f2c743a8c7d4221e90e5u128)))), Point::g().multiple(U256::new(0x304bf7747cff0f4f63168013f673bdaeu128, 0x23704aac7bcee49b23fd4db1fb3f8a11u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x020277049dbed588c6cd71a1f40bf766u128, 0xce432254851de6496d39e049ee31097au128)), FiniteElement(U256::new(0x8cad511ab1fd987612533b76a1d97adfu128, 0x536d04a43030cb956158f31fdd459ba2u128)))), Point::g().multiple(U256::new(0xb29e09a3ec948fcf45ef56e4d880f7a1u128, 0x1c4b5cccc4df5ddd9dce72cebe0bcf9du128)));
        assert_eq!(Point((FiniteElement(U256::new(0x6043fb691a8954ac0073b54b795829beu128, 0x7d96cc3d1479519fc8f9a30747f6fcb0u128)), FiniteElement(U256::new(0xc920170454c8642a36c996a398a2f53fu128, 0xbdd9ea73d58d23b7d7cf83203e3a67b2u128)))), Point::g().multiple(U256::new(0x0084b0c055d89258315a6f5f81ee1d11u128, 0xfdee36da4b093ccda668817f27d5dcddu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x5b1bfbbb86ddc45aa9ade9e555f49eabu128, 0x6f3ac4969702a54a97d464d467553fadu128)), FiniteElement(U256::new(0x5ce3c69ada78c1741bc5cf253854bfe8u128, 0x97aef2bb468f96aaa74af99c1f1e822du128)))), Point::g().multiple(U256::new(0x407baa040db913286d3b2f342979d4f7u128, 0xa1b1146209d6f7730c64cf1e36e83682u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xe677ac922a19170a0674188091a0a35eu128, 0xcb2c350967dad262d59d3e82c47bc27au128)), FiniteElement(U256::new(0x55853d1137a6abcf86e0b75e850ba182u128, 0x070ebdbe626b92c71c8bd94f42da6d6fu128)))), Point::g().multiple(U256::new(0xb11cc0cf98cb6ddd79461e12c2debc01u128, 0x5d7b28129a6d08afd451e668e1103a4du128)));
        assert_eq!(Point((FiniteElement(U256::new(0x10a8a151406473a802fdbdaa4f46986cu128, 0xf2bdb0f3ae5b0b5d0a1f7e82da51d8f8u128)), FiniteElement(U256::new(0x3f3349fcf5b9819d18a9d3793e1631efu128, 0xc3a5e2ee2121051e526d2cf819b2e2f1u128)))), Point::g().multiple(U256::new(0x9a87894ae8cb0b9dea594fd505f9e46cu128, 0xd3f57347010360653393239232a529c1u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x747d55c060b3bdae008fac3f32f71b7du128, 0x61b621c749641c67998a72e91135ad6au128)), FiniteElement(U256::new(0xba8aec457a64968ed2344b444ae248a8u128, 0x22290df904a137f1c331e6629fc86e1bu128)))), Point::g().multiple(U256::new(0x0b4e34f581b79869e6e4df20a9548616u128, 0xecc8efefd01134bb5cd52604df9e2568u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x03886cf24a223ed13db4bb824d21d959u128, 0x166316d0d1d678348eb530e63810a214u128)), FiniteElement(U256::new(0xd1a2e2b7c6b50d07ffcdc061e5774ae9u128, 0xa9898ca19ceef6f4b0d1d8ff3108e603u128)))), Point::g().multiple(U256::new(0xbfad230991ebe537d2b70fa8c5bf7168u128, 0x67cddac430056f76a112551c3368a6ccu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc39ba6cc6c9dbe7bd4f9b78fba669c3eu128, 0xa2aa889df6432745dd86126b13996c91u128)), FiniteElement(U256::new(0x8a2c375346eab7ac5e857bed5ad16627u128, 0x09e3f1cec0f695d88f961fdb52514f27u128)))), Point::g().multiple(U256::new(0x40cee6383dcd54d86aece853e94b12abu128, 0xacfbad548ec6093f0ca3c3c79988e90au128)));
        assert_eq!(Point((FiniteElement(U256::new(0x1fed972090434ee79144b3f570283eb9u128, 0xeaecd08bf88cbb71a4c348c7150cc989u128)), FiniteElement(U256::new(0xccd1339844b8555d844b9a0c8ff24539u128, 0x0e4e9685a05ca29de4635253a202e8beu128)))), Point::g().multiple(U256::new(0x50a393769c73f76525dd5250c64004bau128, 0xbf3ee49e4192e6c17a8a84c4b1e42c0cu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xaaa41ac9786d97b946e42045e03e58d8u128, 0xc5bf1bca2c513829e7e0db02130982f8u128)), FiniteElement(U256::new(0x6472337cf347c8de2446cda7126fab76u128, 0x90109a9bf72a4e13d9e71d9b21089e83u128)))), Point::g().multiple(U256::new(0xd02d39b28f02232b67253762ed4345b8u128, 0x19038b93c8f7334a7b3af910dca5cdddu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x52ca34be671ed77792cede0029371eaau128, 0x965146645d77e9011f8401864f3fec9eu128)), FiniteElement(U256::new(0x62ab445cf5fef128b07280ecf5d4ed7du128, 0xd912352c76c87f2c8486064ddfb94349u128)))), Point::g().multiple(U256::new(0xdf29f92811841f6ed6b6d75ed4851723u128, 0xefcd6e084253b20f421be2ff52006b84u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x5ca977648664067c90459c4c70bb82d2u128, 0xcc725e5217e3654c3783f308d123751cu128)), FiniteElement(U256::new(0xb8d478a76a6d37509a97d43d9ebc6e27u128, 0x44e1816c3bfd555b9e6130a8978ae3c7u128)))), Point::g().multiple(U256::new(0x1632f3cfa2764c231bf259cd4f39d006u128, 0xbfe73e9482d4c2493fb7ca1a7fb8a7d3u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x0061aa684730a8963161d843b9d59c67u128, 0xeceda43e1185bd05d93c74851b669dd7u128)), FiniteElement(U256::new(0x1f23b85ecf6ba0a30fed8936ad771ab1u128, 0xa1754a14042eac6e5e2dfcab4c92a6a0u128)))), Point::g().multiple(U256::new(0xed7bf3c1b9d62dd3d1a9e9b7065b1e74u128, 0xcc69717591f5cb4e6e7d235ccb417a3au128)));
        assert_eq!(Point((FiniteElement(U256::new(0x63020ad420e3af23d10c664596164a92u128, 0x6af78dc7e7b6937b0466d46205fac7abu128)), FiniteElement(U256::new(0xfe021de413bca0103017c137aa543827u128, 0x9540122916f0f6c99c5ccd7981029738u128)))), Point::g().multiple(U256::new(0x6a7bf211f3833d71a624952e04026e73u128, 0xbecc9e565c7454f65e0d57627427d1d0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x401da951600fb05411c02969575e05a8u128, 0x7310041492d5199ce30defa18a9f0768u128)), FiniteElement(U256::new(0xef7ab571770a351e40a52f664c9af912u128, 0xb4ad2c9ecc1c3893f06cb2c16680d890u128)))), Point::g().multiple(U256::new(0x874c5cceffcca2d2005489e7fce9cfb7u128, 0x8646af092c50f75fc3f0ee118629859bu128)));
        assert_eq!(Point((FiniteElement(U256::new(0xdb05c2557f5ef92d967b049d326e64dbu128, 0x572381703469b3ec9f040bfeb9c04572u128)), FiniteElement(U256::new(0x60c3fe9b3de0c8dd676a515893cc33ffu128, 0x015250be5def749832af94786e35dcf3u128)))), Point::g().multiple(U256::new(0xa052769eba171058b840264f375624fcu128, 0xb863175021f3fb50ed1cf414ebe07a06u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xb94ad7840e39ef9e648d6f162832dd57u128, 0x118eed02afd7a520749f77f759cbdcc2u128)), FiniteElement(U256::new(0x9edf71c935bda288bc36c47e33820eabu128, 0x5a63770bda06d3a91f285b4f51c1a4e8u128)))), Point::g().multiple(U256::new(0x7c360e09020155428fe4bd9935343e36u128, 0x9077c38aeddee71cb08e69108855a2a2u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xd0ab1a0e2bacc507ad13fe3c8fbceb78u128, 0xc337918074eda651a937990154274174u128)), FiniteElement(U256::new(0x525ba81780815709fa4dd6e8081dbac8u128, 0xa367841a664761feae4fa63abac36e9bu128)))), Point::g().multiple(U256::new(0x9fe95e7d34e9fcc1634f8c79ded5189cu128, 0x83050f346decae7c18589a69408a59a9u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf7e949b365439bc072bb8ad61339d2f9u128, 0x03ad3b61ea7c5bb4f1330cbf8f4ff793u128)), FiniteElement(U256::new(0x7aaa7b7bd4eda34ca5b19c4fb3596495u128, 0x029dac667cd3680a26cdd223d9a67e69u128)))), Point::g().multiple(U256::new(0x69767cfd8e3b3285a40eb3ea59608825u128, 0x0dab00b6c5a4646cb4b307e8438184f7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf0217f328a2528cbac0190b3fed5961cu128, 0x2aee752a83804fd864f4e9e350125c6au128)), FiniteElement(U256::new(0x7ca512130a6aba2a0bc34e4c6af23004u128, 0x0eb11bfea50d847405c64a5f59f60a3au128)))), Point::g().multiple(U256::new(0x035b695d1ab55f9c8a3c0241dfeabdb0u128, 0x962dd2395e9aa5579028f834d10815e7u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xc7e27f498d92187e056cdf26d804b86du128, 0xd8d92d0cb935d1405f30404becb57a45u128)), FiniteElement(U256::new(0x69adc6cbf85c46afdd6857a6654d4273u128, 0xf6f9c2562b96982cb1fcb4b653596b32u128)))), Point::g().multiple(U256::new(0x66c50c97ca53a69adeaaed4e489e35c8u128, 0x688f0c53b535a4444eae60f22afc1ecbu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x453173be5d908c7a9ef8122220cd0d7fu128, 0xa63dadd50753cc134d3bf72eadbcc1b9u128)), FiniteElement(U256::new(0xdeacdb1e5b6df38943931432bec95c06u128, 0x9dfd276dc03a0846581279e5dda969c1u128)))), Point::g().multiple(U256::new(0xb707d30e3e5ca817c574933e0949c43cu128, 0xa12b7bc379ca99de6f9edbb0e1d331edu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x2fba7b519c48d7a129a6fafb9f621a1fu128, 0x79b4ad2e76b2c3295d856c5880b4709eu128)), FiniteElement(U256::new(0xb0484935d32fb71b0223659f5feb650fu128, 0x41713bf4815ef4a37a471bbf47b0692bu128)))), Point::g().multiple(U256::new(0xcb0062701bb442137076bcd7e15b9615u128, 0x9453a10b7739c9dc4d9f74979e8fdec0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xb99469f3150aff146c5de130130ae59eu128, 0xbd8d4380eb2a2680696a8bc200b7d356u128)), FiniteElement(U256::new(0xac53be223ca6f93928121f7d99c092f4u128, 0x822c59cb1b88e3a50ed9e3014060968eu128)))), Point::g().multiple(U256::new(0x1e4293b94a97eb2910f7aa75723899c4u128, 0xde1ec08a74cfb5e3ad9ce6262f538f06u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf877f51750849b4d8ecfb049f8341918u128, 0xaa2457d733490052773e1f9c4280dc1cu128)), FiniteElement(U256::new(0xc70ba1d51d4cc522e4b0b4c54236de01u128, 0xfac5f0b690be3f6d67a81bd01b15021au128)))), Point::g().multiple(U256::new(0xc437ce15f0068287b7ab7363e9208844u128, 0x082599b623d60f74df349f47f92a7a18u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xd46b5f96b1f0c9b377b57e3e4ed6367fu128, 0xc13f1664890554f998526c615e96824eu128)), FiniteElement(U256::new(0x3410e93020e3f3a8dbe32ddc98444939u128, 0xb738e8151daa849118b0aa4078f073c7u128)))), Point::g().multiple(U256::new(0xeff5af800363b68b6e394299b313bb2cu128, 0xc36aff4d0e3fbf12f870075798306727u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xbdc8ce8705de2067c7af847de6b93369u128, 0x8c537881fb4dc4d7940115e7c3aaef1au128)), FiniteElement(U256::new(0x0e7672167b6c40c81cecefa562ff1862u128, 0x47135bccc5c78c06d800f03ae08beadfu128)))), Point::g().multiple(U256::new(0x209a06a780642149e59eb39d829e2166u128, 0x1f3e55d59a4f41285eee0aa3b8181ebfu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x43c43d242d5160661425a24692c66b5cu128, 0xaba8b3b02e0db989ebe5c820daaa7acbu128)), FiniteElement(U256::new(0xcf738d0404135d9b90111d319bbd397du128, 0xf58e5332920a65b28580d3cb42ae9d47u128)))), Point::g().multiple(U256::new(0xbfedd93d3db59fa0db9e187e41b3bf3eu128, 0x5f85b9bb4cddab200535cfae1ff1bed1u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x0de02134655a5a1321a21681cd5b1baeu128, 0x84c2083f7e6a671e7d38327cdf3bd98fu128)), FiniteElement(U256::new(0xbb290afa365c69d5f91551282bfeb387u128, 0x30a1bdf8cb68e8caed1b7b89d5c316aau128)))), Point::g().multiple(U256::new(0x600ab3f9ac16602226d33426864d5647u128, 0x5608f86a40a5d5d3a001bb29b10016a3u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x6116073e11fbb938c2b14e873a7432bfu128, 0x0a6e80eb3e1296c5fda7aa3b6e2a8971u128)), FiniteElement(U256::new(0xe86c2f7e821b47b8da51b65b32b4cbd0u128, 0x826855ef7be0be3336c6dad5e19c0ca1u128)))), Point::g().multiple(U256::new(0xc6808d6c4f019d95c00718f94aca33d0u128, 0xfa67554df8fac7d8cf7f26ac63361cdfu128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3da41d0250c5a6aeb70edad4c35a7f85u128, 0xf10cddf7d10a4d19a010bdc1955babc5u128)), FiniteElement(U256::new(0x118ccb4ccd3baf9c12b45a97663bae5cu128, 0xd0f7f2148be5c94b5c274008c078cd16u128)))), Point::g().multiple(U256::new(0x06a797eba6848ee4ba50a836bfc2a781u128, 0x2d71cfe2ed3c7ce8954e32b8b1a00c25u128)));
        assert_eq!(Point((FiniteElement(U256::new(0x3c24ee32683d82aba6dbee38095eb725u128, 0x766013afe685ae136481090296a8adf9u128)), FiniteElement(U256::new(0x3d4ea69ef5c2c340a97a283e9b56d37cu128, 0x164ad4b56357d8f00fef7c9a13dc00c6u128)))), Point::g().multiple(U256::new(0x9d4e7e21db16acb105918d9d41f2e588u128, 0xcebb6be29be823f8caed56caa39f76e0u128)));
        assert_eq!(Point((FiniteElement(U256::new(0xf3519a30e8f5927b2845172ee004d193u128, 0x2bf8417d9252a7b7bf5a157c685a0401u128)), FiniteElement(U256::new(0xdb93df11721eafe76343abf983e3f53cu128, 0xac68cf056d532f282ea743eb25737e61u128)))), Point::g().multiple(U256::new(0x3e7c6f2c27b7eeadf1f7f31c87d4ecd1u128, 0x46d388c4893318a8517e94f39b8f02d2u128)));
    }
    
    #[test]
    fn calculate_public_key() {
        let result = Point((FiniteElement(U256::new(0xcd5cd78e17f6faf3bd045f1b71ad9053u128, 0xc5f13f6d79a28ee1deff1e2c0852a771u128)), FiniteElement(U256::new(0x0c91336c9d739dc9840755404441f2beu128, 0xb596b7322202828d4d14b28c78acbee1u128)))).calculate_public_key();
        let correct = [0x04u8, 0xcdu8, 0x5cu8, 0xd7u8, 0x8eu8, 0x17u8, 0xf6u8, 0xfau8, 0xf3u8, 0xbdu8, 0x04u8, 0x5fu8, 0x1bu8, 0x71u8, 0xadu8, 0x90u8, 0x53u8, 0xc5u8, 0xf1u8, 0x3fu8, 0x6du8, 0x79u8, 0xa2u8, 0x8eu8, 0xe1u8, 0xdeu8, 0xffu8, 0x1eu8, 0x2cu8, 0x08u8, 0x52u8, 0xa7u8, 0x71u8, 0x0cu8, 0x91u8, 0x33u8, 0x6cu8, 0x9du8, 0x73u8, 0x9du8, 0xc9u8, 0x84u8, 0x07u8, 0x55u8, 0x40u8, 0x44u8, 0x41u8, 0xf2u8, 0xbeu8, 0xb5u8, 0x96u8, 0xb7u8, 0x32u8, 0x22u8, 0x02u8, 0x82u8, 0x8du8, 0x4du8, 0x14u8, 0xb2u8, 0x8cu8, 0x78u8, 0xacu8, 0xbeu8, 0xe1u8];
        assert!(result.iter().zip(correct.iter()).all(|(a,b)| a == b), "Arrays are not equal");
    } 
*/
}