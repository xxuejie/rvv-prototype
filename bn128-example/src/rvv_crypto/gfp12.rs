use super::{constants::*, gfp::Gfp, gfp6::Gfp6, macros::gfp_ops_impl};
use crate::arith::U256;
use core::mem::MaybeUninit;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

fn bits(a: &U256) -> usize {
    256 - a.bits().take_while(|b| !b).count()
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp12(pub [Gfp6; 2]);

impl Gfp12 {
    pub fn one() -> Self {
        let mut a = Gfp12::default();
        a.set_one();
        a
    }

    pub fn x(&self) -> &Gfp6 {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp6 {
        &self.0[1]
    }

    pub fn x_mut(&mut self) -> &mut Gfp6 {
        &mut self.0[0]
    }

    pub fn y_mut(&mut self) -> &mut Gfp6 {
        &mut self.0[1]
    }

    pub fn set_x(&mut self, x: &Gfp6) -> &mut Self {
        self.0[0].set(x);
        self
    }

    pub fn set_y(&mut self, y: &Gfp6) -> &mut Self {
        self.0[1].set(y);
        self
    }

    pub fn set(&mut self, other: &Gfp12) -> &mut Self {
        self.set_x(other.x());
        self.set_y(other.y());
        self
    }

    pub fn set_zero(&mut self) -> &mut Self {
        self.x_mut().set_zero();
        self.y_mut().set_zero();
        self
    }

    pub fn set_one(&mut self) -> &mut Self {
        self.x_mut().set_zero();
        self.y_mut().set_one();
        self
    }

    pub fn is_zero(&self) -> bool {
        self.x().is_zero() && self.y().is_zero()
    }

    pub fn is_one(&self) -> bool {
        self.x().is_zero() && self.y().is_one()
    }

    pub fn conjugate(&mut self) -> &mut Self {
        self.x_mut().neg_ref();
        self
    }

    pub fn neg_ref(&mut self) -> &mut Self {
        self.x_mut().neg_ref();
        self.y_mut().neg_ref();
        self
    }

    pub fn frobenius(&mut self) -> &mut Self {
        self.x_mut()
            .frobenius()
            .mul_scalar(&constant_to_gfp2(&XI_TO_P_MINUS1_OVER6));
        self.y_mut().frobenius();
        self
    }

    pub fn frobenius_p2(&mut self) -> &mut Self {
        self.x_mut()
            .frobenius_p2()
            .mul_gfp(&Gfp(XI_TO_P_SQUARED_MINUS1_OVER6));
        self.y_mut().frobenius_p2();
        self
    }

    pub fn frobenius_p4(&mut self) -> &mut Self {
        self.x_mut()
            .frobenius_p4()
            .mul_gfp(&Gfp(XI_TO_P_SQUARED_MINUS1_OVER3));
        self.y_mut().frobenius_p4();
        self
    }

    pub fn add_ref(&mut self, b: &Gfp12) -> &mut Self {
        self.x_mut().add_ref(&b.x());
        self.y_mut().add_ref(&b.y());
        self
    }

    pub fn add_to(a: &Gfp12, b: &Gfp12) -> Self {
        let mut r: Gfp12 = unsafe { MaybeUninit::uninit().assume_init() };
        r.0[0] = a.x() + b.x();
        r.0[1] = a.y() + b.y();
        r
    }

    pub fn sub_ref(&mut self, b: &Gfp12) -> &mut Self {
        self.x_mut().sub_ref(&b.x());
        self.y_mut().sub_ref(&b.y());
        self
    }

    pub fn sub_to(a: &Gfp12, b: &Gfp12) -> Self {
        let mut r: Gfp12 = unsafe { MaybeUninit::uninit().assume_init() };
        r.0[0] = a.x() - b.x();
        r.0[1] = a.y() - b.y();
        r
    }

    pub fn mul_ref(&mut self, b: &Gfp12) -> &mut Self {
        let mut tx = self.x().clone();
        tx.mul_ref(b.y());
        let mut t = b.x().clone();
        t.mul_ref(self.y());
        tx.add_ref(&t);

        let mut ty = self.y().clone();
        ty.mul_ref(b.y());
        t.set(self.x()).mul_ref(b.x()).mul_tau();

        self.0[0].set(&tx);
        self.0[1].set(&ty);
        self.0[1].add_ref(&t);
        self
    }

    pub fn mul_to(a: &Gfp12, b: &Gfp12) -> Self {
        let mut tx = a.x().clone();
        tx.mul_ref(b.y());
        let mut t = b.x().clone();
        t.mul_ref(a.y());
        tx.add_ref(&t);

        let mut ty = a.y().clone();
        ty.mul_ref(b.y());
        t.set(a.x()).mul_ref(b.x()).mul_tau();

        let mut r: Gfp12 = unsafe { MaybeUninit::uninit().assume_init() };
        r.0[0] = tx;
        r.0[1] = &ty + &t;
        r
    }

    pub fn mul_scalar(&mut self, b: &Gfp6) -> &mut Self {
        self.x_mut().mul_ref(b);
        self.y_mut().mul_ref(b);
        self
    }

    pub fn exp(&mut self, power: &U256) -> &mut Self {
        let mut sum = Gfp12::default();
        sum.set_one();
        let mut t = Gfp12::default();

        for i in (0..bits(power)).rev() {
            t.set(&sum).square();
            if power.get_bit(i).unwrap_or(false) {
                sum.set(&t).mul_ref(self);
            } else {
                sum.set(&t);
            }
        }

        self.set(&sum);
        self
    }

    pub fn square(&mut self) -> &mut Self {
        let v0 = self.x() * self.y();

        let mut t = self.x().clone();
        t.mul_tau();
        t.add_ref(self.y());
        let mut ty = self.x() + self.y();
        ty.mul_ref(&t).sub_ref(&v0);
        t.set(&v0).mul_tau();
        ty.sub_ref(&t);

        self.set_x(&v0);
        self.x_mut().add_ref(&v0);
        self.set_y(&ty);
        self
    }

    pub fn invert(&mut self) -> &mut Self {
        let mut t1 = self.x().clone();
        t1.square();
        let mut t2 = self.y().clone();
        t2.square();

        t1.mul_tau();
        t2.sub_ref(&t1);
        t2.invert();

        self.x_mut().neg_ref();
        self.mul_scalar(&t2);
        self
    }

    pub fn final_exponentiation(&mut self) -> &mut Self {
        // p^6-Frobenus
        let mut t1 = self.clone();
        t1.x_mut().neg_ref();

        let mut inv = self.clone();
        inv.invert();
        t1.mul_ref(&inv);

        let mut t2 = t1.clone();
        t2.frobenius_p2();
        t1.mul_ref(&t2);

        let mut fp = t1.clone();
        fp.frobenius();
        let mut fp2 = t1.clone();
        fp2.frobenius_p2();
        let mut fp3 = fp2.clone();
        fp3.frobenius();

        let mut fu = t1.clone();
        fu.exp(&U.into());
        let mut fu2 = fu.clone();
        fu2.exp(&U.into());
        let mut fu3 = fu2.clone();
        fu3.exp(&U.into());

        let mut y3 = fu.clone();
        y3.frobenius();
        let mut fu2p = fu2.clone();
        fu2p.frobenius();
        let mut fu3p = fu3.clone();
        fu3p.frobenius();
        let mut y2 = fu2.clone();
        y2.frobenius_p2();

        let mut y0 = fp.clone();
        y0.mul_ref(&fp2).mul_ref(&fp3);

        let mut y1 = t1.clone();
        y1.conjugate();
        let mut y5 = fu2.clone();
        y5.conjugate();
        y3.conjugate();
        let mut y4 = fu.clone();
        y4.mul_ref(&fu2p);
        y4.conjugate();

        let mut y6 = fu3.clone();
        y6.mul_ref(&fu3p);
        y6.conjugate();

        let mut t0 = y6.clone();
        t0.square();
        t0.mul_ref(&y4).mul_ref(&y5);
        t1.set(&y3).mul_ref(&y5).mul_ref(&t0);
        t0.mul_ref(&y2);
        t1.square().mul_ref(&t0).square();
        t0.set(&t1).mul_ref(&y1);
        t1.mul_ref(&y0);
        t0.square().mul_ref(&t1);

        *self = t0;
        self
    }
}

gfp_ops_impl!(Gfp12);
