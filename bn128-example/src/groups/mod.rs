use crate::arith::U256;
use crate::fields::{const_fq, fq2_nonresidue, FieldElement, Fq, Fq12, Fq2, Fr};
use core::{
    fmt,
    ops::{Add, Mul, Neg, Sub},
};

// This is the NAF version of ate_loop_count. Entries are all mod 4, so 3 = -1
// n.b. ate_loop_count = 0x19d797039be763ba8
//                     = 11001110101111001011100000011100110111110011101100011101110101000
//       (naf version) = 11010003030003010300300000100301003000030100030300100030030101000
// We skip the first element (1) as we would need to skip over it in the main loop
const ATE_LOOP_COUNT_NAF: [u8; 64] = [
    1, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 0, 3, 0, 1, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 1, 0,
    0, 3, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 3, 0, 3, 0, 0, 1, 0, 0, 0, 3, 0, 0, 3, 0, 1, 0, 1, 0, 0, 0,
];

pub trait GroupElement:
    Sized
    + Copy
    + Clone
    + PartialEq
    + Eq
    + fmt::Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Neg<Output = Self>
    + Mul<Fr, Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
    fn double(&self) -> Self;
}

pub trait GroupParams: Sized + fmt::Debug {
    type Base: FieldElement;

    fn name() -> &'static str;
    fn one() -> G<Self>;
    fn coeff_b() -> Self::Base;
    fn check_order() -> bool {
        false
    }
}

#[repr(C)]
#[derive(Default)]
pub struct G<P: GroupParams> {
    x: P::Base,
    y: P::Base,
    z: P::Base,
}

impl<P: GroupParams> G<P> {
    pub fn new(x: P::Base, y: P::Base, z: P::Base) -> Self {
        G { x: x, y: y, z: z }
    }

    pub fn x(&self) -> &P::Base {
        &self.x
    }

    pub fn x_mut(&mut self) -> &mut P::Base {
        &mut self.x
    }

    pub fn y(&self) -> &P::Base {
        &self.y
    }

    pub fn y_mut(&mut self) -> &mut P::Base {
        &mut self.y
    }

    pub fn z(&self) -> &P::Base {
        &self.z
    }

    pub fn z_mut(&mut self) -> &mut P::Base {
        &mut self.z
    }
}

#[derive(Debug, Default)]
pub struct AffineG<P: GroupParams> {
    x: P::Base,
    y: P::Base,
}

#[derive(Debug)]
pub enum Error {
    NotOnCurve,
    NotInSubgroup,
}

impl<P: GroupParams> AffineG<P> {
    pub fn new(x: P::Base, y: P::Base) -> Result<Self, Error> {
        if y.squared() == (x.squared() * x) + P::coeff_b() {
            if P::check_order() {
                let p: G<P> = G {
                    x: x,
                    y: y,
                    z: P::Base::one(),
                };

                if (p * (-Fr::one())) + p != G::zero() {
                    return Err(Error::NotInSubgroup);
                }
            }

            Ok(AffineG { x: x, y: y })
        } else {
            Err(Error::NotOnCurve)
        }
    }

    pub fn x(&self) -> &P::Base {
        &self.x
    }

    pub fn x_mut(&mut self) -> &mut P::Base {
        &mut self.x
    }

    pub fn y(&self) -> &P::Base {
        &self.y
    }

    pub fn y_mut(&mut self) -> &mut P::Base {
        &mut self.y
    }
}

impl<P: GroupParams> PartialEq for AffineG<P> {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<P: GroupParams> Eq for AffineG<P> {}

impl<P: GroupParams> fmt::Debug for G<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({:?}, {:?}, {:?})", P::name(), self.x, self.y, self.z)
    }
}

impl<P: GroupParams> Clone for G<P> {
    fn clone(&self) -> Self {
        G {
            x: self.x,
            y: self.y,
            z: self.z,
        }
    }
}

impl<P: GroupParams> Copy for G<P> {}

impl<P: GroupParams> Clone for AffineG<P> {
    fn clone(&self) -> Self {
        AffineG {
            x: self.x,
            y: self.y,
        }
    }
}

impl<P: GroupParams> Copy for AffineG<P> {}

impl<P: GroupParams> PartialEq for G<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        let z1_squared = self.z.squared();
        let z2_squared = other.z.squared();

        if self.x * z2_squared != other.x * z1_squared {
            return false;
        }

        let z1_cubed = self.z * z1_squared;
        let z2_cubed = other.z * z2_squared;

        if self.y * z2_cubed != other.y * z1_cubed {
            return false;
        }

        return true;
    }
}
impl<P: GroupParams> Eq for G<P> {}

impl<P: GroupParams> G<P> {
    pub fn to_affine(&self) -> Option<AffineG<P>> {
        if self.z.is_zero() {
            None
        } else if self.z == P::Base::one() {
            Some(AffineG {
                x: self.x,
                y: self.y,
            })
        } else {
            let zinv = self.z.inverse().unwrap();
            let zinv_squared = zinv.squared();

            Some(AffineG {
                x: self.x * zinv_squared,
                y: self.y * (zinv_squared * zinv),
            })
        }
    }
}

impl<P: GroupParams> AffineG<P> {
    pub fn to_jacobian(&self) -> G<P> {
        G {
            x: self.x,
            y: self.y,
            z: P::Base::one(),
        }
    }
}

impl<P: GroupParams> GroupElement for G<P> {
    fn zero() -> Self {
        G {
            x: P::Base::zero(),
            y: P::Base::one(),
            z: P::Base::zero(),
        }
    }

    fn one() -> Self {
        P::one()
    }

    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }

    fn double(&self) -> Self {
        let a = self.x.squared();
        let b = self.y.squared();
        let c = b.squared();
        let mut d = (self.x + b).squared() - a - c;
        d = d + d;
        let e = a + a + a;
        let f = e.squared();
        let x3 = f - (d + d);
        let mut eight_c = c + c;
        eight_c = eight_c + eight_c;
        eight_c = eight_c + eight_c;
        let y1z1 = self.y * self.z;

        G {
            x: x3,
            y: e * (d - x3) - eight_c,
            z: y1z1 + y1z1,
        }
    }
}

impl<P: GroupParams> Mul<Fr> for G<P> {
    type Output = G<P>;

    fn mul(self, other: Fr) -> G<P> {
        let mut res = G::zero();
        let mut found_one = false;

        for i in U256::from(other).bits() {
            if found_one {
                res = res.double();
            }

            if i {
                found_one = true;
                res = res + self;
            }
        }

        res
    }
}

impl<P: GroupParams> Add<G<P>> for G<P> {
    type Output = G<P>;

    fn add(self, other: G<P>) -> G<P> {
        if self.is_zero() {
            return other;
        }

        if other.is_zero() {
            return self;
        }

        let z1_squared = self.z.squared();
        let z2_squared = other.z.squared();
        let u1 = self.x * z2_squared;
        let u2 = other.x * z1_squared;
        let z1_cubed = self.z * z1_squared;
        let z2_cubed = other.z * z2_squared;
        let s1 = self.y * z2_cubed;
        let s2 = other.y * z1_cubed;

        if u1 == u2 && s1 == s2 {
            self.double()
        } else {
            let h = u2 - u1;
            let s2_minus_s1 = s2 - s1;
            let i = (h + h).squared();
            let j = h * i;
            let r = s2_minus_s1 + s2_minus_s1;
            let v = u1 * i;
            let s1_j = s1 * j;
            let x3 = r.squared() - j - (v + v);

            G {
                x: x3,
                y: r * (v - x3) - (s1_j + s1_j),
                z: ((self.z + other.z).squared() - z1_squared - z2_squared) * h,
            }
        }
    }
}

impl<P: GroupParams> Neg for G<P> {
    type Output = G<P>;

    fn neg(self) -> G<P> {
        if self.is_zero() {
            self
        } else {
            G {
                x: self.x,
                y: -self.y,
                z: self.z,
            }
        }
    }
}

impl<P: GroupParams> Neg for AffineG<P> {
    type Output = AffineG<P>;

    fn neg(self) -> AffineG<P> {
        AffineG {
            x: self.x,
            y: -self.y,
        }
    }
}

impl<P: GroupParams> Sub<G<P>> for G<P> {
    type Output = G<P>;

    fn sub(self, other: G<P>) -> G<P> {
        self + (-other)
    }
}

#[derive(Debug, Default)]
pub struct G1Params;

impl GroupParams for G1Params {
    type Base = Fq;

    fn name() -> &'static str {
        "G1"
    }

    fn one() -> G<Self> {
        G {
            x: Fq::one(),
            y: const_fq([
                0xa6ba871b8b1e1b3a,
                0x14f1d651eb8e167b,
                0xccdd46def0f28c58,
                0x1c14ef83340fbe5e,
            ]),
            z: Fq::one(),
        }
    }

    fn coeff_b() -> Fq {
        const_fq([
            0x7a17caa950ad28d7,
            0x1f6ac17ae15521b9,
            0x334bea4e696bd284,
            0x2a1f6744ce179d8e,
        ])
    }
}

pub type G1 = G<G1Params>;

pub type AffineG1 = AffineG<G1Params>;

#[derive(Debug, Default)]
pub struct G2Params;

impl GroupParams for G2Params {
    type Base = Fq2;

    fn name() -> &'static str {
        "G2"
    }

    fn one() -> G<Self> {
        G {
            x: Fq2::new(
                const_fq([
                    0x8e83b5d102bc2026,
                    0xdceb1935497b0172,
                    0xfbb8264797811adf,
                    0x19573841af96503b,
                ]),
                const_fq([
                    0xafb4737da84c6140,
                    0x6043dd5a5802d8c4,
                    0x09e950fc52a02f86,
                    0x14fef0833aea7b6b,
                ]),
            ),
            y: Fq2::new(
                const_fq([
                    0x619dfa9d886be9f6,
                    0xfe7fd297f59e9b78,
                    0xff9e1a62231b7dfe,
                    0x28fd7eebae9e4206,
                ]),
                const_fq([
                    0x64095b56c71856ee,
                    0xdc57f922327d3cbb,
                    0x55f935be33351076,
                    0x0da4a0e693fd6482,
                ]),
            ),
            z: Fq2::one(),
        }
    }

    fn coeff_b() -> Fq2 {
        Fq2::new(
            const_fq([
                0x3bf938e377b802a8,
                0x020b1b273633535d,
                0x26b7edf049755260,
                0x2514c6324384a86d,
            ]),
            const_fq([
                0x38e7ecccd1dcff67,
                0x65f0b37d93ce0d3e,
                0xd749d0dd22ac00aa,
                0x0141b9ce4a688d4d,
            ]),
        )
    }

    fn check_order() -> bool {
        true
    }
}

pub type G2 = G<G2Params>;

pub type AffineG2 = AffineG<G2Params>;

#[inline]
fn twist() -> Fq2 {
    fq2_nonresidue()
}

#[inline]
fn two_inv() -> Fq {
    const_fq([
        9781510331150239090,
        15059239858463337189,
        10331104244869713732,
        2249375503248834476,
    ])
}

#[inline]
fn twist_mul_by_q_x() -> Fq2 {
    Fq2::new(
        const_fq([
            13075984984163199792,
            3782902503040509012,
            8791150885551868305,
            1825854335138010348,
        ]),
        const_fq([
            7963664994991228759,
            12257807996192067905,
            13179524609921305146,
            2767831111890561987,
        ]),
    )
}

#[inline]
fn twist_mul_by_q_y() -> Fq2 {
    Fq2::new(
        const_fq([
            16482010305593259561,
            13488546290961988299,
            3578621962720924518,
            2681173117283399901,
        ]),
        const_fq([
            11661927080404088775,
            553939530661941723,
            7860678177968807019,
            3208568454732775116,
        ]),
    )
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct EllCoeffs {
    pub ell_0: Fq2,
    pub ell_vw: Fq2,
    pub ell_vv: Fq2,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct G2Precomp {
    pub q: AffineG<G2Params>,
    pub coeffs: [EllCoeffs; 102],
}

impl Default for G2Precomp {
    fn default() -> Self {
        G2Precomp {
            q: AffineG::default(),
            coeffs: [EllCoeffs::default(); 102],
        }
    }
}

impl G2Precomp {
    pub fn miller_loop(&self, g1: &AffineG<G1Params>) -> Fq12 {
        let mut f = Fq12::one();

        let mut idx = 0;

        for i in ATE_LOOP_COUNT_NAF.iter() {
            let c = &self.coeffs[idx];
            idx += 1;
            f = f
                .squared()
                .mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));

            if *i != 0 {
                let c = &self.coeffs[idx];
                idx += 1;
                f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));
            }
        }

        let c = &self.coeffs[idx];
        idx += 1;
        f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));

        let c = &self.coeffs[idx];
        f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));

        f
    }
}

pub fn miller_loop_batch(g2_precomputes: &[G2Precomp], g1_vec: &[AffineG<G1Params>]) -> Fq12 {
    let mut f = Fq12::one();

    let mut idx = 0;

    for i in ATE_LOOP_COUNT_NAF.iter() {
        f = f.squared();
        for (g2_precompute, g1) in g2_precomputes.iter().zip(g1_vec.iter()) {
            let c = &g2_precompute.coeffs[idx];
            f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));
        }
        idx += 1;
        if *i != 0 {
            for (g2_precompute, g1) in g2_precomputes.iter().zip(g1_vec.iter()) {
                let c = &g2_precompute.coeffs[idx];
                f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));
            }
            idx += 1;
        }
    }

    for (g2_precompute, g1) in g2_precomputes.iter().zip(g1_vec.iter()) {
        let c = &g2_precompute.coeffs[idx];
        f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));
    }
    idx += 1;
    for (g2_precompute, g1) in g2_precomputes.iter().zip(g1_vec.iter()) {
        let c = &g2_precompute.coeffs[idx];
        f = f.mul_by_024(c.ell_0, c.ell_vw.scale(g1.y), c.ell_vv.scale(g1.x));
    }
    f
}

impl AffineG<G2Params> {
    fn mul_by_q(&self) -> Self {
        AffineG {
            x: twist_mul_by_q_x() * self.x.frobenius_map(1),
            y: twist_mul_by_q_y() * self.y.frobenius_map(1),
        }
    }

    pub fn precompute(&self) -> G2Precomp {
        let mut r = self.to_jacobian();

        let mut coeffs: [EllCoeffs; 102] = [EllCoeffs {
            ell_0: Fq2::zero(),
            ell_vv: Fq2::zero(),
            ell_vw: Fq2::zero(),
        }; 102];
        let mut idx = 0;

        let q_neg = self.neg();
        for i in ATE_LOOP_COUNT_NAF.iter() {
            coeffs[idx] = r.doubling_step_for_flipped_miller_loop();
            idx += 1;

            if *i == 1 {
                coeffs[idx] = r.mixed_addition_step_for_flipped_miller_loop(self);
                idx += 1;
            }
            if *i == 3 {
                coeffs[idx] = r.mixed_addition_step_for_flipped_miller_loop(&q_neg);
                idx += 1;
            }
        }
        let q1 = self.mul_by_q();
        let q2 = -(q1.mul_by_q());

        coeffs[idx] = r.mixed_addition_step_for_flipped_miller_loop(&q1);
        idx += 1;
        coeffs[idx] = r.mixed_addition_step_for_flipped_miller_loop(&q2);

        G2Precomp {
            q: *self,
            coeffs: coeffs,
        }
    }
}

impl G2 {
    fn mixed_addition_step_for_flipped_miller_loop(
        &mut self,
        base: &AffineG<G2Params>,
    ) -> EllCoeffs {
        let d = self.x - self.z * base.x;
        let e = self.y - self.z * base.y;
        let f = d.squared();
        let g = e.squared();
        let h = d * f;
        let i = self.x * f;
        let j = self.z * g + h - (i + i);

        self.x = d * j;
        self.y = e * (i - j) - h * self.y;
        self.z = self.z * h;

        EllCoeffs {
            ell_0: twist() * (e * base.x - d * base.y),
            ell_vv: e.neg(),
            ell_vw: d,
        }
    }

    fn doubling_step_for_flipped_miller_loop(&mut self) -> EllCoeffs {
        let a = (self.x * self.y).scale(two_inv());
        let b = self.y.squared();
        let c = self.z.squared();
        let d = c + c + c;
        let e = G2Params::coeff_b() * d;
        let f = e + e + e;
        let g = (b + f).scale(two_inv());
        let h = (self.y + self.z).squared() - (b + c);
        let i = e - b;
        let j = self.x.squared();
        let e_sq = e.squared();

        self.x = a * (b - f);
        self.y = g.squared() - (e_sq + e_sq + e_sq);
        self.z = b * h;

        EllCoeffs {
            ell_0: twist() * i,
            ell_vw: h.neg(),
            ell_vv: j + j + j,
        }
    }
}

pub fn pairing(p: &G1, q: &G2) -> Fq12 {
    match (p.to_affine(), q.to_affine()) {
        (None, _) | (_, None) => Fq12::one(),
        (Some(p), Some(q)) => q
            .precompute()
            .miller_loop(&p)
            .final_exponentiation()
            .expect("miller loop cannot produce zero"),
    }
}

pub fn pairing_batch(ps: &[G1], qs: &[G2]) -> Fq12 {
    let mut p_affines = [AffineG::default(); 16];
    let mut q_precomputes = [G2Precomp::default(); 16];
    let mut idx = 0;

    for (p, q) in ps.iter().zip(qs.iter()) {
        let p_affine = p.to_affine();
        let q_affine = q.to_affine();
        let exists = match (p_affine, q_affine) {
            (None, _) | (_, None) => false,
            (Some(_p_affine), Some(_q_affine)) => true,
        };

        if exists {
            p_affines[idx] = p.to_affine().unwrap();
            q_precomputes[idx] = q.to_affine().unwrap().precompute();
            idx += 1;
        }
    }
    if q_precomputes.len() == 0 {
        return Fq12::one();
    }
    miller_loop_batch(&q_precomputes[0..idx], &p_affines[0..idx])
        .final_exponentiation()
        .expect("miller loop cannot produce zero")
}
