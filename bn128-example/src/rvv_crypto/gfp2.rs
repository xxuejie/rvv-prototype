// extern crate alloc;
// use alloc::format;
// use ckb_std::syscalls::debug;

use super::gfp::{self, Gfp};
use core::ops::{Add, Mul, Neg, Sub};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp2(pub [Gfp; 2]);

impl Gfp2 {
    pub fn x(&self) -> &Gfp {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp {
        &self.0[1]
    }

    pub fn mont_decode(&mut self) {
        gfp::mont_decode(&mut self.0);
    }

    pub fn set(&mut self, a: &Gfp2) {
        self.0[0].set(&a.0[0]);
        self.0[1].set(&a.0[1]);
    }

    pub fn set_zero(&mut self) {
        self.0[0] = gfp::ZERO;
        self.0[1] = gfp::ZERO;
    }

    pub fn set_one(&mut self) {
        self.0[0] = gfp::ZERO;
        self.0[1] = gfp::ONE;
    }

    pub fn is_zero(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ZERO
    }

    pub fn is_one(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ONE
    }

    pub fn conjugate(&mut self, a: &Gfp2) {
        self.set(a);
        gfp::neg(&mut self.0[0..1])
    }

    pub fn neg_ref(&mut self) {
        gfp::neg(&mut self.0)
    }

    pub fn add_ref(&mut self, b: &Gfp2) {
        gfp::add_mov(&mut self.0, &b.0)
    }

    pub fn sub_ref(&mut self, b: &Gfp2) {
        gfp::sub_mov(&mut self.0, &b.0)
    }

    pub fn mul_ref(&mut self, b: &Gfp2) {
        let mut tx_t = [self.0[1].clone(), self.0[0].clone()];
        gfp::mul_mov(&mut tx_t, &b.0);
        gfp::mul_mov(&mut self.0, &b.0);

        self.0[1] -= self.0[0].clone();
        let [tx1, tx2] = tx_t;
        self.0[0] = tx1 + tx2;
    }

    pub fn mul_scalar(&mut self, b: &Gfp) {
        gfp::mul_mov_scalar(&mut self.0, b);
    }

    pub fn mul_xi(&mut self) {
        let orig = self.clone();
        gfp::add_mov(&mut self.0, &orig.0);
        gfp::add_mov(&mut self.0, &orig.0);
        let [x, y] = orig.0;
        self.0[0] += y;
        self.0[1] -= x;
    }
}

impl Add for Gfp2 {
    type Output = Gfp2;

    fn add(mut self, a: Gfp2) -> Gfp2 {
        self.add_ref(&a);
        self
    }
}

impl Add<&Gfp2> for Gfp2 {
    type Output = Gfp2;

    fn add(mut self, a: &Gfp2) -> Gfp2 {
        self.add_ref(a);
        self
    }
}

impl Add for &Gfp2 {
    type Output = Gfp2;

    fn add(self, a: &Gfp2) -> Gfp2 {
        let mut r = self.clone();
        r.add_ref(a);
        r
    }
}

impl Mul for Gfp2 {
    type Output = Gfp2;

    fn mul(mut self, a: Gfp2) -> Gfp2 {
        self.mul_ref(&a);
        self
    }
}

impl Mul<&Gfp2> for Gfp2 {
    type Output = Gfp2;

    fn mul(mut self, a: &Gfp2) -> Gfp2 {
        self.mul_ref(a);
        self
    }
}

impl Mul for &Gfp2 {
    type Output = Gfp2;

    fn mul(self, a: &Gfp2) -> Gfp2 {
        let mut r = self.clone();
        r.mul_ref(a);
        r
    }
}

impl Neg for Gfp2 {
    type Output = Gfp2;

    fn neg(mut self) -> Gfp2 {
        self.neg_ref();
        self
    }
}

impl Neg for &Gfp2 {
    type Output = Gfp2;

    fn neg(self) -> Gfp2 {
        let mut r = self.clone();
        r.neg_ref();
        r
    }
}

impl Sub for Gfp2 {
    type Output = Gfp2;

    fn sub(mut self, a: Gfp2) -> Gfp2 {
        self.sub_ref(&a);
        self
    }
}

impl Sub<&Gfp2> for Gfp2 {
    type Output = Gfp2;

    fn sub(mut self, a: &Gfp2) -> Gfp2 {
        self.sub_ref(a);
        self
    }
}

impl Sub for &Gfp2 {
    type Output = Gfp2;

    fn sub(self, a: &Gfp2) -> Gfp2 {
        let mut r = self.clone();
        r.sub_ref(a);
        r
    }
}
