use crate::arith::{U256, U512};
use crate::fields::FieldElement;
use core::ops::{Add, Mul, Neg, Sub};

macro_rules! field_impl {
    ($name:ident, $modulus:expr, $rsquared:expr, $rcubed:expr, $one:expr, $inv:expr) => {
        #[derive(Copy, Clone, Default, PartialEq, Eq, Debug)]
        #[repr(C)]
        pub struct $name(U256);

        impl From<$name> for U256 {
            #[inline]
            fn from(mut a: $name) -> Self {
                a.0.mul(&U256::one(), &U256($modulus), $inv);

                a.0
            }
        }

        impl $name {
            pub fn from_str(s: &str) -> Option<Self> {
                let mut ints = [Self::zero(); 11];
                for i in 1..11 {
                    ints[i] = ints[i - 1] + Self::one();
                }
                let mut res = Self::zero();
                for c in s.chars() {
                    match c.to_digit(10) {
                        Some(d) => {
                            res = res * ints[10];
                            res = res + ints[d as usize];
                        }
                        None => {
                            return None;
                        }
                    }
                }

                Some(res)
            }

            /// Converts a U256 to an Fp so long as it's below the modulus.
            pub fn new(mut a: U256) -> Option<Self> {
                if a < U256($modulus) {
                    a.mul(&U256($rsquared), &U256($modulus), $inv);

                    Some($name(a))
                } else {
                    None
                }
            }

            /// Converts a U256 to an Fr regardless of modulus.
            pub fn new_mul_factor(mut a: U256) -> Self {
                a.mul(&U256($rsquared), &U256($modulus), $inv);
                $name(a)
            }

            pub fn interpret(buf: &[u8; 64]) -> Self {
                $name::new(U512::interpret(buf).divrem(&U256($modulus)).1).unwrap()
            }

            /// Returns the modulus
            #[inline]
            #[allow(dead_code)]
            pub fn modulus() -> U256 {
                U256($modulus)
            }

            #[inline]
            #[allow(dead_code)]
            pub fn inv(&self) -> u128 {
                $inv
            }

            pub fn raw(&self) -> &U256 {
                &self.0
            }

            pub fn set_bit(&mut self, bit: usize, to: bool) {
                self.0.set_bit(bit, to);
            }
        }

        impl FieldElement for $name {
            #[inline]
            fn zero() -> Self {
                $name(U256([0, 0]))
            }

            #[inline]
            fn one() -> Self {
                $name(U256($one))
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.0.is_zero()
            }

            fn inverse(mut self) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    self.0.invert(&U256($modulus));
                    self.0.mul(&U256($rcubed), &U256($modulus), $inv);

                    Some(self)
                }
            }
        }

        impl Add for $name {
            type Output = $name;

            #[inline]
            fn add(mut self, other: $name) -> $name {
                self.0.add(&other.0, &U256($modulus));

                self
            }
        }

        impl Sub for $name {
            type Output = $name;

            #[inline]
            fn sub(mut self, other: $name) -> $name {
                self.0.sub(&other.0, &U256($modulus));

                self
            }
        }

        impl Mul for $name {
            type Output = $name;

            #[inline]
            fn mul(mut self, other: $name) -> $name {
                self.0.mul(&other.0, &U256($modulus), $inv);

                self
            }
        }

        impl Neg for $name {
            type Output = $name;

            #[inline]
            fn neg(mut self) -> $name {
                self.0.neg(&U256($modulus));
                self
            }
        }
    };
}

field_impl!(
    Fr,
    [
        0x2833e84879b9709143e1f593f0000001,
        0x30644e72e131a029b85045b68181585d
    ],
    [
        0x53fe3ab1e35c59e31bb8e645ae216da7,
        0x0216d0b17f4e44a58c49833d53bb8085
    ],
    [
        0x2a489cbe1cfbb6b85e94d8e1b4bf0040,
        0x0cf8594b7fcc657c893cc664a19fcfed
    ],
    [
        0x36fc76959f60cd29ac96341c4ffffffb,
        0x0e0a77c19a07df2f666ea36f7879462e
    ],
    0x6586864b4c6911b3c2e1f593efffffff
);

field_impl!(
    Fq,
    [
        0x97816a916871ca8d3c208c16d87cfd47,
        0x30644e72e131a029b85045b68181585d
    ],
    [
        0xb5e71911d44501fbf32cfc5b538afa89,
        0x06d89f71cab8351f47ab1eff0a417ff6
    ],
    [
        0x62f210e6a7283db6b1cd6dafda1530df,
        0x20fd6e902d592544ef7f0b0c0ada0afb
    ],
    [
        0x0a78eb28f5c70b3dd35d438dc58f0d9d,
        0x0e0a77c19a07df2f666ea36f7879462c
    ],
    0x9ede7d651eca6ac987d20782e4866389
);

lazy_static::lazy_static! {

    static ref FQ: U256 = U256([
        0x97816a916871ca8d3c208c16d87cfd47,
        0x30644e72e131a029b85045b68181585d
    ]);

    pub static ref FQ_MINUS3_DIV4: Fq =
        Fq::new(3.into()).expect("3 is a valid field element and static; qed").neg() *
        Fq::new(4.into()).expect("4 is a valid field element and static; qed").inverse()
            .expect("4 has inverse in Fq and is static; qed");

    static ref FQ_MINUS1_DIV2: Fq =
        Fq::new(1.into()).expect("1 is a valid field element and static; qed").neg() *
        Fq::new(2.into()).expect("2 is a valid field element and static; qed").inverse()
            .expect("2 has inverse in Fq and is static; qed");

}

impl Fq {
    pub fn sqrt(&self) -> Option<Self> {
        let a1 = self.pow(*FQ_MINUS3_DIV4);
        let a1a = a1 * *self;
        let a0 = a1 * (a1a);

        let mut am1 = *FQ;
        am1.sub(&1.into(), &*FQ);

        if a0 == Fq::new(am1).unwrap() {
            None
        } else {
            Some(a1a)
        }
    }
}

#[inline]
pub fn const_fq(i: [u64; 4]) -> Fq {
    Fq(U256::from(i))
}
