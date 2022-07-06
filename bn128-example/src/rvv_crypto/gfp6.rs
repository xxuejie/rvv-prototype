use super::{constants::*, gfp2::Gfp2, gfp::Gfp};

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
}
