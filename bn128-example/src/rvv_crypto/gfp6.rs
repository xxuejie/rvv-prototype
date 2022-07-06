use super::{constants::*, gfp::Gfp, gfp2::Gfp2};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp6(pub [Gfp2; 3]);

fn constant_to_gfp2(a: &[[u64; 4]; 2]) -> Gfp2 {
    Gfp2([Gfp(a[0]), Gfp(a[1])])
}

impl Gfp6 {
    pub fn x(&self) -> &Gfp2 {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp2 {
        &self.0[1]
    }

    pub fn z(&self) -> &Gfp2 {
        &self.0[2]
    }

    pub fn set(&mut self, other: &Gfp6) {
        self.0[0].set(&other.0[0]);
        self.0[1].set(&other.0[1]);
        self.0[2].set(&other.0[2]);
    }

    pub fn frobenius(&mut self) {
        self.0[0].conjugate();
        self.0[1].conjugate();
        self.0[2].conjugate();

        self.0[0].mul_ref(&constant_to_gfp2(&XI_TO_2P_MINUS2_OVER3));
        self.0[1].mul_ref(&constant_to_gfp2(&XI_TO_P_MINUS1_OVER3));
    }

    pub fn mul_ref(&mut self, b: &Gfp6) {
        let v0 = self.z() * b.z();
        let v1 = self.y() * b.y();
        let v2 = self.x() * b.x();

        let mut t0 = self.x() + self.y();
        let mut t1 = b.x() + b.y();
        let mut tz = (&t0) * (&t1);
        tz -= &v1;
        tz -= &v2;
        tz.mul_xi();
        tz += &v0;

        t0.set(self.y());
        t0 += self.z();
        t1.set(b.y());
        t1 += b.z();
        let mut ty = (&t0) * (&t1);
        t0.set(&v2);
        t0.mul_xi();
        ty -= &v0;
        ty -= &v1;
        ty += &t0;

        t0.set(self.x());
        t0 += self.z();
        t1.set(b.x());
        t1 += b.z();
        let mut tx = (&t0) * (&t1);
        tx -= &v0;
        tx += &v1;
        tx -= &v2;

        self.0[0].set(&tx);
        self.0[1].set(&ty);
        self.0[2].set(&tz);
    }

    pub fn add_ref(&mut self, b: &Gfp6) {
        self.0[0] += &b.0[0];
        self.0[1] += &b.0[1];
        self.0[2] += &b.0[2];
    }

    pub fn mul_tau(&mut self) {
        let mut tz = self.x().clone();
        tz.mul_xi();
        self.0[0].set(&self.y().clone());
        self.0[1].set(&self.z().clone());
        self.0[2].set(&tz);
    }
}
