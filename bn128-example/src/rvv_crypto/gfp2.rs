use super::{
    gfp::{self, Gfp},
    macros::gfp_ops_impl,
};
use core::mem::MaybeUninit;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

const MUL_A_INDEX: [u8; 4] = [0, 32, 32, 0];
const MUL_B_INDEX: [u8; 4] = [32, 0, 32, 0];

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

    pub fn mont_decode(&mut self) -> &mut Self {
        gfp::mont_decode(&mut self.0);
        self
    }

    pub fn set(&mut self, a: &Gfp2) -> &mut Self {
        self.set_x(a.x());
        self.set_y(a.y());
        self
    }

    pub fn set_zero(&mut self) -> &mut Self {
        self.set_x(&gfp::ZERO);
        self.set_y(&gfp::ZERO);
        self
    }

    pub fn set_one(&mut self) -> &mut Self {
        self.set_x(&gfp::ZERO);
        self.set_y(&gfp::ONE);
        self
    }

    pub fn is_zero(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ZERO
    }

    pub fn is_one(&self) -> bool {
        self.x() == &gfp::ZERO && self.y() == &gfp::ONE
    }

    pub fn conjugate(&mut self) -> &mut Self {
        gfp::neg(self.x_slice_mut());
        self
    }

    pub fn neg_ref(&mut self) -> &mut Self {
        gfp::neg(&mut self.0);
        self
    }

    pub fn add_ref(&mut self, b: &Gfp2) -> &mut Self {
        gfp::add_mov(&mut self.0, &b.0);
        self
    }

    pub fn add_to(a: &Gfp2, b: &Gfp2) -> Self {
        let mut r: Gfp2 = unsafe { MaybeUninit::uninit().assume_init() };
        gfp::add(&a.0, &b.0, &mut r.0);
        r
    }

    pub fn sub_ref(&mut self, b: &Gfp2) -> &mut Self {
        gfp::sub_mov(&mut self.0, &b.0);
        self
    }

    pub fn sub_to(a: &Gfp2, b: &Gfp2) -> Self {
        let mut r: Gfp2 = unsafe { MaybeUninit::uninit().assume_init() };
        gfp::sub(&a.0, &b.0, &mut r.0);
        r
    }

    pub fn mul_ref(&mut self, b: &Gfp2) -> &mut Self {
        // mul_by_byte_index below will fill in all the data
        let mut tx_t1_ty_t2: [Gfp; 4] = unsafe { MaybeUninit::uninit().assume_init() };
        gfp::mul_by_byte_index(&self.0, &b.0, &MUL_A_INDEX, &MUL_B_INDEX, &mut tx_t1_ty_t2);

        gfp::add(&tx_t1_ty_t2[0..1], &tx_t1_ty_t2[1..2], &mut self.0[0..1]);
        gfp::sub(&tx_t1_ty_t2[2..3], &tx_t1_ty_t2[3..4], &mut self.0[1..2]);
        self
    }

    pub fn mul_to(a: &Gfp2, b: &Gfp2) -> Self {
        let mut tx_t1_ty_t2: [Gfp; 4] = unsafe { MaybeUninit::uninit().assume_init() };
        gfp::mul_by_byte_index(&a.0, &b.0, &MUL_A_INDEX, &MUL_B_INDEX, &mut tx_t1_ty_t2);

        let mut r: Gfp2 = unsafe { MaybeUninit::uninit().assume_init() };
        gfp::add(&tx_t1_ty_t2[0..1], &tx_t1_ty_t2[1..2], &mut r.0[0..1]);
        gfp::sub(&tx_t1_ty_t2[2..3], &tx_t1_ty_t2[3..4], &mut r.0[1..2]);
        r
    }

    pub fn mul_scalar(&mut self, b: &Gfp) -> &mut Self {
        gfp::mul_mov_scalar(&mut self.0, b);
        self
    }

    pub fn mul_xi(&mut self) -> &mut Self {
        // tx is kept in self, a is kept in orig
        let orig = self.clone();
        gfp::add_mov(&mut self.0, &orig.0);
        gfp::double(&mut self.0);
        gfp::double(&mut self.0);
        gfp::add_mov(&mut self.0, &orig.0);
        let [x, y] = orig.0;
        self.0[0] += y;
        self.0[1] -= x;
        self
    }

    pub fn square(&mut self) -> &mut Self {
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
        self
    }

    pub fn invert(&mut self) -> &mut Self {
        let mut t = self.clone();
        gfp::square(&mut t.0);
        let [mut t1, t2] = t.0;
        t1 = t1 + t2;
        t1.invert();

        gfp::neg(self.x_slice_mut());
        gfp::mul_mov_scalar(&mut self.0, &t1);
        self
    }
}

gfp_ops_impl!(Gfp2);
