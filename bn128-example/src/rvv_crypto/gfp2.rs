// extern crate alloc;
// use alloc::format;
// use ckb_std::syscalls::debug;

use super::gfp::{self, Gfp};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp2(pub [Gfp; 2]);

impl Gfp2 {
    pub fn x(&self) -> &Gfp {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp {
        &self.0[1]
    }

    pub fn x_slice(&self) -> &[Gfp] {
        &self.0[0..1]
    }

    pub fn y_slice(&self) -> &[Gfp] {
        &self.0[1..2]
    }

    pub fn x_slice_mut(&mut self) -> &mut [Gfp] {
        &mut self.0[0..1]
    }

    pub fn y_slice_mut(&mut self) -> &mut [Gfp] {
        &mut self.0[1..2]
    }

    pub fn set_x(&mut self, x: &Gfp) {
        self.0[0].set(x);
    }

    pub fn set_y(&mut self, y: &Gfp) {
        self.0[1].set(y);
    }

    pub fn mont_decode(&mut self) {
        gfp::mont_decode(&mut self.0);
    }

    pub fn set(&mut self, a: &Gfp2) {
        self.set_x(a.x());
        self.set_y(a.y());
    }

    pub fn set_zero(&mut self) {
        self.set_x(&gfp::ZERO);
        self.set_y(&gfp::ZERO);
    }

    pub fn set_one(&mut self) {
        self.set_x(&gfp::ZERO);
        self.set_y(&gfp::ONE);
    }

    pub fn is_zero(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ZERO
    }

    pub fn is_one(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ONE
    }

    pub fn conjugate(&mut self) {
        gfp::neg(self.x_slice_mut());
    }

    pub fn neg_ref(&mut self) {
        gfp::neg(&mut self.0);
    }

    pub fn add_ref(&mut self, b: &Gfp2) {
        gfp::add_mov(&mut self.0, &b.0);
    }

    pub fn sub_ref(&mut self, b: &Gfp2) {
        gfp::sub_mov(&mut self.0, &b.0);
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

    pub fn square(&mut self) {
        // tx = y
        let mut tx = [self.y().clone()];
        // ty = x
        let mut ty = [self.x().clone()];
        // tx = y - x
        gfp::sub_mov(&mut tx, self.x_slice());
        // ty = x + y
        gfp::add_mov(&mut ty, self.y_slice());
        // ty = (y - x)(x + y)
        gfp::mul_mov(&mut ty, &tx);
        // tx = x * y
        gfp::mul(self.x_slice(), self.y_slice(), &mut tx);
        // tx = 2 * x * y
        gfp::double(&mut tx);
        self.set_x(&tx[0]);
        self.set_y(&ty[0]);
    }

    pub fn invert(&mut self) {
        let mut t = self.clone();
        gfp::square(&mut t.0);
        let [mut t1, t2] = t.0;
        t1 = t1 + t2;
        t1.invert();

        gfp::neg(self.x_slice_mut());
        gfp::mul_mov_scalar(&mut self.0, &t1);
    }
}
