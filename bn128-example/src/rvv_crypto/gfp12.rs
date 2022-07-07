use super::{constants::*, gfp::Gfp, gfp6::Gfp6};
use crate::arith::U256;

fn bits(a: &U256) -> usize {
    256 - a.bits().take_while(|b| !b).count()
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp12(pub [Gfp6; 2]);

impl Gfp12 {
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

    pub fn sub_ref(&mut self, b: &Gfp12) -> &mut Self {
        self.x_mut().sub_ref(&b.x());
        self.y_mut().sub_ref(&b.y());
        self
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

    pub fn final_exponentiation(&mut self) {
        unimplemented!()
    }
}
