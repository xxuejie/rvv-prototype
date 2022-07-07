use super::{
    gfp::{self, Gfp},
    gfp2::Gfp2,
    Error,
};
use core::convert::{TryFrom, TryInto};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct TwistPoint(pub [Gfp2; 4]);

impl TryFrom<&[u8]> for TwistPoint {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let mut xx_xy_yx_yy: [Gfp; 4] = [
            value[0..32].try_into()?,
            value[32..64].try_into()?,
            value[64..96].try_into()?,
            value[96..128].try_into()?,
        ];
        gfp::mont_encode(&mut xx_xy_yx_yy);
        let [xx, xy, yx, yy] = xx_xy_yx_yy;
        let mut point = TwistPoint([
            Gfp2([xx, xy]),
            Gfp2([yx, yy]),
            Gfp2::default(),
            Gfp2::default(),
        ]);

        if point.x().is_zero() && point.y().is_zero() {
            point.y_mut().set_one();
            point.z_mut().set_zero();
            point.t_mut().set_zero();
        } else {
            point.z_mut().set_one();
            point.t_mut().set_one();

            if !point.is_on_curve() {
                return Err("malformed point!".into());
            }
        }
        Ok(point)
    }
}

pub const TWIST_B: Gfp2 = Gfp2([
    Gfp([
        0x75046774386b8d71,
        0x5bd0854a46d36cf8,
        0x664327a1d41c8414,
        0x96c9abb932eeb2f,
    ]),
    Gfp([
        0xb94f760fb4c5ee14,
        0xdae9f8f24c3b6eb4,
        0x77a675d2e52f4fe4,
        0x736f31b09116c66b,
    ]),
]);

pub const TWIST_GEN: TwistPoint = TwistPoint([
    Gfp2([
        Gfp([
            0x402c4ab7139e1404,
            0xce1c368a183d85a4,
            0xd67cf9a6cb8d3983,
            0x3cf246bbc2a9fbe8,
        ]),
        Gfp([
            0x88f9f11da7cdc184,
            0x18293f95d69509d3,
            0xb5ce0c55a735d5a1,
            0x15134189bfd45a0,
        ]),
    ]),
    Gfp2([
        Gfp([
            0xbfac7d731e9e87a2,
            0xa50bb8007962e441,
            0xafe910a4e8270556,
            0x5075c5429d69159a,
        ]),
        Gfp([
            0xc2e07c1463ea9e56,
            0xee4442052072ebd2,
            0x561a519486036937,
            0x5bd9394cc0d2cce,
        ]),
    ]),
    Gfp2([
        // Gfp::new_from_int64(0)
        Gfp([0, 0, 0, 0]),
        // Gfp::new_from_int64(1)
        Gfp([
            16691276537507834265,
            1271272038023711329,
            6165449088192685022,
            8091559079779792902,
        ]),
    ]),
    Gfp2([
        // Gfp::new_from_int64(0)
        Gfp([0, 0, 0, 0]),
        // Gfp::new_from_int64(1)
        Gfp([
            16691276537507834265,
            1271272038023711329,
            6165449088192685022,
            8091559079779792902,
        ]),
    ]),
]);

impl TwistPoint {
    pub fn x(&self) -> &Gfp2 {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp2 {
        &self.0[1]
    }

    pub fn z(&self) -> &Gfp2 {
        &self.0[2]
    }

    pub fn t(&self) -> &Gfp2 {
        &self.0[3]
    }

    pub fn x_slice(&self) -> &[Gfp2] {
        &self.0[0..1]
    }

    pub fn y_slice(&self) -> &[Gfp2] {
        &self.0[1..2]
    }

    pub fn z_slice(&self) -> &[Gfp2] {
        &self.0[2..3]
    }

    pub fn t_slice(&self) -> &[Gfp2] {
        &self.0[3..4]
    }

    pub fn x_slice_mut(&mut self) -> &mut [Gfp2] {
        &mut self.0[0..1]
    }

    pub fn y_slice_mut(&mut self) -> &mut [Gfp2] {
        &mut self.0[1..2]
    }

    pub fn z_slice_mut(&mut self) -> &mut [Gfp2] {
        &mut self.0[2..3]
    }

    pub fn t_slice_mut(&mut self) -> &mut [Gfp2] {
        &mut self.0[3..4]
    }

    pub fn x_mut(&mut self) -> &mut Gfp2 {
        &mut self.0[0]
    }

    pub fn y_mut(&mut self) -> &mut Gfp2 {
        &mut self.0[1]
    }

    pub fn z_mut(&mut self) -> &mut Gfp2 {
        &mut self.0[2]
    }

    pub fn t_mut(&mut self) -> &mut Gfp2 {
        &mut self.0[3]
    }

    pub fn set_x(&mut self, x: &Gfp2) -> &mut Self {
        self.0[0].set(x);
        self
    }

    pub fn set_y(&mut self, y: &Gfp2) -> &mut Self {
        self.0[1].set(y);
        self
    }

    pub fn set_z(&mut self, z: &Gfp2) -> &mut Self {
        self.0[2].set(z);
        self
    }

    pub fn set_t(&mut self, t: &Gfp2) -> &mut Self {
        self.0[3].set(t);
        self
    }

    pub fn set(&mut self, other: &TwistPoint) -> &mut Self {
        self.set_x(other.x());
        self.set_y(other.y());
        self.set_z(other.z());
        self.set_t(other.t());
        self
    }

    pub fn is_on_curve(&mut self) -> bool {
        self.make_affine();
        if self.is_infinity() {
            return true;
        }

        let mut y2 = self.y().clone();
        y2.square();
        let mut x3 = self.x().clone();
        x3.square().mul_ref(self.x()).add_ref(&TWIST_B);

        y2 == x3
    }

    pub fn set_infinity(&mut self) -> &mut Self {
        self.x_mut().set_zero();
        self.y_mut().set_one();
        self.z_mut().set_zero();
        self.t_mut().set_zero();
        self
    }

    pub fn is_infinity(&self) -> bool {
        self.z().is_zero()
    }

    pub fn make_affine(&mut self) -> &mut Self {
        if self.z().is_one() {
            return self;
        } else if self.z().is_zero() {
            self.x_mut().set_zero();
            self.y_mut().set_one();
            self.t_mut().set_zero();
            return self;
        }

        let mut z_inv = self.z().clone();
        z_inv.invert();
        let mut t = self.y().clone();
        t.mul_ref(&z_inv);
        let mut z_inv2 = z_inv.clone();
        z_inv2.square();
        self.y_mut().set(&t).mul_ref(&z_inv2);
        t.set(self.x()).mul_ref(&z_inv2);
        self.x_mut().set(&t);
        self.z_mut().set_one();
        self.t_mut().set_one();
        self
    }

    pub fn neg_ref(&mut self) -> &mut Self {
        self.y_mut().neg_ref();
        self.t_mut().set_zero();
        self
    }
}

pub fn double(a: &TwistPoint, c: &mut TwistPoint) {
    let mut aa = a.x().clone();
    aa.square();
    let mut bb = a.y().clone();
    bb.square();
    let mut cc = bb.clone();
    cc.square();

    let mut t = a.x() + &bb;
    let mut t2 = t.clone();
    t2.square();
    t.set(&t2).sub_ref(&aa);
    t2.set(&t).sub_ref(&cc);
    let d = (&t2) + (&t2);
    t = (&aa) + (&aa);
    let e = (&t) + (&aa);
    let mut f = e.clone();
    f.square();

    t = (&d) + (&d);
    c.x_mut().set(&f).sub_ref(&t);

    let cz = a.y() * a.z();
    c.z_mut().set(&cz).add_ref(&cz);

    t = (&cc) + (&cc);
    t2 = (&t) + (&t);
    t = (&t2) + (&t2);
    let cy = (&d) - c.x();
    t2 = (&e) * (&cy);
    c.y_mut().set(&t2).sub_ref(&t);
}

pub fn add(a: &TwistPoint, b: &TwistPoint, c: &mut TwistPoint) {
    if a.is_infinity() {
        c.set(b);
        return;
    }
    if b.is_infinity() {
        c.set(a);
        return;
    }

    let mut z12 = a.z().clone();
    z12.square();
    let mut z22 = b.z().clone();
    z22.square();
    let u1 = a.x() * &z22;
    let u2 = b.x() * &z12;

    let mut t = b.z() * &z22;
    let s1 = a.y() * &t;

    t = a.z() * &z12;
    let s2 = b.y() * &t;

    let h = &u2 - &u1;
    let x_equal = h.is_zero();

    t = &h + &h;
    let mut i = t.clone();
    i.square();
    let j = &h * &i;

    t = &s2 - &s1;
    let y_equal = t.is_zero();
    if x_equal && y_equal {
        double(a, c);
        return;
    }
    let r = &t + &t;

    let v = &u1 * &i;

    let mut t4 = r.clone();
    t4.square();
    t = &v + &v;
    let mut t6 = &t4 - &j;
    c.x_mut().set(&t6).sub_ref(&t);

    t = &v - c.x();
    t4 = &s1 * &j;
    t6 = &t4 + &t4;
    t4 = &r * &t;
    c.y_mut().set(&t4).sub_ref(&t6);

    t = a.z() + b.z();
    t4 = t.clone();
    t4.square();
    t = &t4 - &z12;
    t4 = t - &z22;
    c.z_mut().set(&t4).mul_ref(&h);
}
