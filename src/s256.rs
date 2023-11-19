

use core::ops::{Add, Sub, Mul, Div};
use crate::u256::U256;

#[repr(C)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct S256((U256, bool));

impl S256 {
    pub fn new(value: U256, sign: bool) -> Self {
        S256((value, sign))
    }

    pub fn absolute_value(self) -> U256 {
        self.0.0
    }

    pub fn get_sign(self) -> bool {
        self.0.1
    }
}

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
