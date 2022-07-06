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

    pub fn frobenius(&mut self) {
        self.0[0].conjugate();
        self.0[1].conjugate();
        self.0[2].conjugate();

        self.0[0].mul_ref(&constant_to_gfp2(&XI_TO_2P_MINUS2_OVER3));
        self.0[1].mul_ref(&constant_to_gfp2(&XI_TO_P_MINUS1_OVER3));
    }

    pub fn mul(&mut self, b: &Gfp6) {
        let mut v0 = self.z().clone(); v0.mul_ref(b.z());
        let mut v1 = self.y().clone(); v1.mul_ref(b.y());
        let mut v2 = self.x().clone(); v2.mul_ref(b.x());

        let mut t0 = self.x().clone(); t0.add_ref(self.y());
        let mut t1 = b.x().clone(); t1.add_ref(b.y());
        let mut tz = t0.clone(); tz.mul_ref(&t1);
        tz.sub_ref(&v1); tz.sub_ref(&v2); tz.mul_xi(); tz.add_ref(&v0);

        t0.set(self.y()); t0.add_ref(self.z());
        t1.set(b.y()); t1.add_ref(b.z());
        let mut ty = t0.clone(); ty.mul_ref(&t1);
        t0.set(&v2); t0.mul_xi();
        ty.sub_ref(&v0); ty.sub_ref(&v1); ty.add_ref(&t0);

        t0.set(self.x()); t0.add_ref(self.z());
        t1.set(b.x()); t1.add_ref(b.z());
        let mut tx = t0.clone(); tx.mul_ref(&t1);
        tx.sub_ref(&v0); tx.add_ref(&v1); tx.sub_ref(&v2);

        self.0[0].set(&tx);
        self.0[1].set(&ty);
        self.0[2].set(&tz);
    }
}
