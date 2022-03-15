#![allow(dead_code)]
extern crate alloc;

use crate::signed_integer::SignedInteger;
use alloc::rc::Rc;
use core::cell::RefCell;
use core::ops::{Add, Mul, Sub};
use rvv::rvv_vector;
use rvv_asm::rvv_asm;

use rvv_simulator_runtime::Uint;

pub type U256 = Uint<4>;
pub type U512 = Uint<8>;

#[macro_export]
macro_rules! U256 {
    ($e: expr) => {
        Uint::<4>($e)
    };
}

#[macro_export]
macro_rules! U512 {
    ($e: expr) => {
        Uint::<8>($e)
    };
}

#[macro_export]
macro_rules! U {
    ($n:expr) => {
        U256::from($n)
    };
}

pub type I512 = SignedInteger<U512>;

impl From<U256> for I512 {
    fn from(n: U256) -> Self {
        Self::new(true, n.into())
    }
}

impl From<u32> for I512 {
    fn from(n: u32) -> Self {
        Self::new(true, U512::from(n))
    }
}

// Extended Euclidean algorithm
// https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
pub fn egcd(a: I512, b: I512) -> (I512, I512, I512) {
    assert!(a < b);
    let zero = I512::from(0);
    let one = I512::from(1);
    if a == zero {
        (b, zero, one)
    } else {
        let (g, x, y) = egcd(b % a, a);
        (g, y - (b / a) * x, x)
    }
}

#[derive(Clone)]
pub struct Mont {
    pub np1: U256,
    pub r: U512,
    pub n: U256,
    pub bits: usize,
    pub init: bool,
}

impl Mont {
    pub fn new(n: U256) -> Self {
        let bits = 256;
        let base = U512::from(2);
        let r = base.pow(bits.into());
        Mont {
            r,
            n,
            np1: U!(0),
            bits,
            init: false,
        }
    }

    pub fn precompute(&mut self) {
        let one = I512::from(1);
        let zero = I512::from(0);

        let r: I512 = self.r.into();
        let n: I512 = self.n.into();
        let (gcd, np, rp) = egcd(n, r);
        assert_eq!(gcd, one);

        let rp1 = rp + self.n.into();
        assert!(rp1 >= zero);

        let np1 = I512::from(self.r) - np;
        assert!(np1 >= zero);
        self.np1 = np1.num.into(); // can be truncated

        let r = I512::from(self.r) * rp1;
        let n = I512::from(self.n) * np1;
        assert_eq!(n + one, r);

        self.init = true;
    }
    // m = T*Np1 mod R
    // U = (T + m * N) / R
    // The overall process delivers T · R−1 mod N without an expensive division operation!
    pub fn reduce(&self, t: U512) -> U256 {
        if cfg!(feature = "use_rvv_vector") {
            mont_reduce(self.np1, self.n, t, self.bits)
        } else if cfg!(feature = "use_rvv_asm") {
            mont_reduce_asm(&[self.np1][..], &[self.n][..], &[t][..], self.bits)[0]
        } else {
            assert!(self.init);
            let t0: U512 = U!(t).into(); // low part of `t`, same as `% self.r`, avoid overflow
            let m: U512 = U!(t0 * U512::from(self.np1)).into(); // `% self.r`
            let u = (t + m * U512::from(self.n)) >> self.bits; // `/ self.r`
            if u >= U512::from(self.n) {
                U!(u - self.n)
            } else {
                U!(u)
            }
        }
    }

    pub fn to_mont(&self, x: U256) -> U256 {
        if cfg!(feature = "use_rvv_vector") {
            mont_to_mont(self.n, self.r, x)
        } else if cfg!(feature = "use_rvv_asm") {
            mont_to_mont_asm(&[self.n][..], &[self.r][..], &[x][..])[0]
        } else {
            assert!(self.init);
            let x2: U512 = x.into();
            let res = (x2 * self.r) % self.n;
            U!(res)
        }
    }
    pub fn multi(&self, x: U256, y: U256) -> U256 {
        if cfg!(feature = "use_rvv_vector") {
            mont_multi(self.np1, self.n, x, y, self.bits)
        } else if cfg!(feature = "use_rvv_asm") {
            mont_multi_asm(
                &[self.np1][..],
                &[self.n][..],
                &[x][..],
                &[y][..],
                self.bits,
            )[0]
        } else {
            let xy = U512::from(x) * U512::from(y);
            self.reduce(xy)
        }
    }

    pub fn pow(&self, x: U256, y: U256) -> U256 {
        let mut base = x;
        let one = U!(1);
        let mut res = U!(0);
        let mut first_time: bool = true;

        for index in 0..self.bits {
            // at most self.bits(256 here) multiplications
            if ((y >> index) & one) == one {
                if first_time {
                    // note:
                    // `res = self.multi(1, base)` is not same
                    // as res = base;
                    res = base;
                    first_time = false;
                } else {
                    res = self.multi(res, base);
                }
            }
            base = self.multi(base, base); // at most self.bits(256 here) multiplications
        }
        res
    }
}

use alloc::vec::Vec;

#[inline(never)]
pub fn mont_reduce_asm(np1: &[U256], n: &[U256], t: &[U512], bits: usize) -> Vec<U256> {
    assert!(np1.len() == n.len());
    assert!(n.len() == t.len());
    let len = np1.len();
    if np1.len() == 0 {
        return Vec::new();
    }

    let mut m_256: Vec<U256> = Vec::with_capacity(len);
    let t_256 = t.iter().cloned().map(U256::from).collect::<Vec<_>>();
    unsafe {
        rvv_asm!(
            "mv {tmp0}, t0",
            "mv {tmp1}, t1",
            "mv {tmp2}, t2",
            // vset
            "mv t1, {len}",
            "1:",
            // t2 = vl
            "vsetvli t2, t1, e256, m4",

            // load t0
            "mv t0, {value_t}",
            "vle256.v v2, (t0)", // v2..v6
            // load np1
            "mv t0, {value_np1}",
            "vle256.v v6, (t0)", // v6..v10
            // t0 * np1
            "vmul.vv v2, v2, v6",
            // store result to buffer
            "mv t0, {buf}",
            "vse256.v v2, (t0)",

            // len -= vl;
            "sub t1, t1, t2",
            "slli t2, t2, 5",
            // value_t += 32 * vl;
            "add {value_t}, {value_t}, t2",
            // value_np1 += 32 * vl;
            "add {value_np1}, {value_np1}, t2",
            // buf += 32 * vl;
            "add {buf}, {buf}, t2",

            "bnez t1, 1b",

            "mv t0, {tmp0}",
            "mv t1, {tmp1}",
            "mv t2, {tmp2}",
            tmp0 = out(reg) _,
            tmp1 = out(reg) _,
            tmp2 = out(reg) _,
            len = in(reg) len,
            // low part of `t`, same as `% self.r`, avoid overflow
            value_t = inout(reg) t_256.as_ptr() => _,
            value_np1 = inout(reg) np1.as_ptr() => _,
            buf = inout(reg) m_256.as_mut_ptr() => _,
        );
        m_256.set_len(len);
    };
    let m_512 = m_256.into_iter().map(U512::from).collect::<Vec<_>>();
    let n_512 = n.iter().cloned().map(U512::from).collect::<Vec<_>>();
    let mut result_512: Vec<U512> = Vec::with_capacity(len);
    unsafe {
        rvv_asm!(
            "mv {tmp0}, t0",
            "mv {tmp1}, t1",
            "mv {tmp2}, t2",
            // vset
            "mv t1, {len}",
            "2:",
            "vsetvli t2, t1, e512, m8",

            // load t
            "mv t0, {value_t}",
            "vle512.v v2, (t0)", // v2..v10
            // load m
            "mv t0, {value_m}",
            "vle512.v v10, (t0)", // v10..v18
            // load n
            "mv t0, {value_n}",
            "vle512.v v18, (t0)", // v18..v26
            // m = m * n
            "vmul.vv v10, v10, v18",
            // t = t + m
            "vadd.vv v2, v2, v10",
            // load bits
            "mv t0, {bits}",
            // u = t >> bits
            "vsrl.vx v2, v2, t0",
            // if u >= n {}
            "vmsleu.vv v0, v18, v2",
            // u = u - n
            "vsub.vv v2, v2, v18, v0.t",
            // store u
            "mv t0, {buf}",
            "vse512.v v2, (t0)",

            // len -= vl;
            "sub t1, t1, t2",
            "slli t2, t2, 6",
            // value_t += 64 * vl;
            "add {value_t}, {value_t}, t2",
            // value_m += 64 * vl;
            "add {value_m}, {value_m}, t2",
            // value_n += 64 * vl;
            "add {value_n}, {value_n}, t2",
            // buf += 64 * vl;
            "add {buf}, {buf}, t2",

            "bnez t1, 2b",

            "mv t0, {tmp0}",
            "mv t1, {tmp1}",
            "mv t2, {tmp2}",
            tmp0 = out(reg) _,
            tmp1 = out(reg) _,
            tmp2 = out(reg) _,
            len = in(reg) len,
            bits = in(reg) bits,
            value_t = inout(reg) t.as_ptr() => _,
            value_m = inout(reg) m_512.as_ptr() => _,
            value_n = inout(reg) n_512.as_ptr() => _,
            buf = inout(reg) result_512.as_mut_ptr() => _,
        );
        result_512.set_len(len);
    };
    result_512.into_iter().map(U256::from).collect()
}
#[inline(never)]
pub fn mont_to_mont_asm(n: &[U256], r: &[U512], x: &[U256]) -> Vec<U256> {
    assert!(n.len() == r.len());
    assert!(r.len() == x.len());
    let len = n.len();
    if len == 0 {
        return Vec::new();
    }
    let n_512 = n.iter().cloned().map(U256::from).collect::<Vec<_>>();
    let x_512 = x.iter().cloned().map(U256::from).collect::<Vec<_>>();
    let mut res_512: Vec<U512> = Vec::with_capacity(len);
    unsafe {
        rvv_asm!(
            "mv {tmp0}, t0",
            "mv {tmp1}, t1",
            "mv {tmp2}, t2",

            "mv t1, {len}",
            "1:",
            "vsetvli t2, t1, e512, m8",

            // load x
            "mv t0, {value_x}",
            "vle512.v v2, (t0)", // v2..v10
            // load r
            "mv t0, {value_r}",
            "vle512.v v10, (t0)", // v10..v18
            // load n
            "mv t0, {value_n}",
            "vle512.v v18, (t0)", // v18..v26

            // x = x * r;
            "vmul.vv v2, v2, v10",
            // x = x % n;
            "vremu.vv v2, v2, v18",
            // store x
            "mv t0, {buf}",
            "vse512.v v2, (t0)",

            // len -= vl;
            "sub t1, t1, t2",
            "slli t2, t2, 6",
            // value_x += 64 * vl;
            "add {value_x}, {value_x}, t2",
            // value_r += 64 * vl;
            "add {value_r}, {value_r}, t2",
            // value_n += 64 * vl;
            "add {value_n}, {value_n}, t2",
            // buf += 64 * vl;
            "add {buf}, {buf}, t2",

            "bnez t1, 1b",

            "mv t0, {tmp0}",
            "mv t1, {tmp1}",
            "mv t2, {tmp2}",
            tmp0 = out(reg) _,
            tmp1 = out(reg) _,
            tmp2 = out(reg) _,
            len = in(reg) len,
            value_x = inout(reg) x_512.as_ptr() => _,
            value_r = inout(reg) r.as_ptr() => _,
            value_n = inout(reg) n_512.as_ptr() => _,
            buf = inout(reg) res_512.as_mut_ptr() => _,
        );
        res_512.set_len(len);
    };
    res_512.into_iter().map(U256::from).collect()
}
#[inline(never)]
pub fn mont_multi_asm(np1: &[U256], n: &[U256], x: &[U256], y: &[U256], bits: usize) -> Vec<U256> {
    assert_eq!(np1.len(), n.len());
    assert_eq!(n.len(), x.len());
    assert_eq!(x.len(), y.len());
    let len = np1.len();
    if len == 0 {
        return Vec::new();
    }
    let x_512 = x.iter().cloned().map(U512::from).collect::<Vec<_>>();
    let y_512 = y.iter().cloned().map(U512::from).collect::<Vec<_>>();
    let mut xy: Vec<U512> = Vec::with_capacity(len);
    unsafe {
        rvv_asm!(
            "mv {tmp0}, t0",
            "mv {tmp1}, t1",
            "mv {tmp2}, t2",

            "mv t1, {len}",
            "1:",
            "vsetvli t2, t1, e512, m8",

            // load x
            "mv t0, {value_x}",
            "vle512.v v2, (t0)", // v2..v10
            // load y
            "mv t0, {value_y}",
            "vle512.v v10, (t0)", // v10..v18
            // xy = x * y;
            "vmul.vv v2, v2, v10",
            // store x
            "mv t0, {buf}",
            "vse512.v v2, (t0)",

            // len -= vl;
            "sub t1, t1, t2",
            "slli t2, t2, 6",
            // value_x += 64 * vl;
            "add {value_x}, {value_x}, t2",
            // value_y += 64 * vl;
            "add {value_y}, {value_y}, t2",
            // buf += 64 * vl;
            "add {buf}, {buf}, t2",

            "bnez t1, 1b",

            "mv t0, {tmp0}",
            "mv t1, {tmp1}",
            "mv t2, {tmp2}",
            tmp0 = out(reg) _,
            tmp1 = out(reg) _,
            tmp2 = out(reg) _,
            len = in(reg) len,
            value_x = inout(reg) x_512.as_ptr() => _,
            value_y = inout(reg) y_512.as_ptr() => _,
            buf = inout(reg) xy.as_mut_ptr() => _,
        );
        xy.set_len(len);
    };
    mont_reduce_asm(np1, n, &xy, bits)
}
// implemented by rvv_vector
#[rvv_vector]
pub fn mont_reduce(np1: U256, n: U256, t: U512, bits: usize) -> U256 {
    let t0: U512 = U256::from(t).into(); // low part of `t`, same as `% self.r`, avoid overflow
    let np1_512: U512 = U512::from(np1);
    let n_512: U512 = U512::from(n);
    let bits_512: U512 = U512::from(bits);
    let m_256: U256 = U256::from(t0 * np1_512);
    let m_512: U512 = m_256.into(); // `% self.r`
    let u: U512 = (t + m_512 * n_512) >> bits_512; // `/ self.r`
    if u >= n_512 {
        U256::from(u - n_512)
    } else {
        U256::from(u)
    }
}

#[rvv_vector]
pub fn mont_to_mont(n: U256, r: U512, x: U256) -> U256 {
    let x_512: U512 = x.into();
    let n_512: U512 = n.into();
    let res = (x_512 * r) % n_512;
    U256::from(res)
}

#[rvv_vector]
pub fn mont_multi(np1: U256, n: U256, x: U256, y: U256, bits: usize) -> U256 {
    let x_512: U512 = x.into();
    let y_512: U512 = y.into();

    let xy: U512 = x_512 * y_512;
    mont_reduce(np1, n, xy, bits)
}

#[derive(Clone)]
pub struct MontForm {
    pub mont: Rc<RefCell<Mont>>,
    pub num: U256,
}

impl MontForm {
    // it's not possible to implement `From<U256>` for `MontForm` because it requires extra `mont`
    pub fn from_u256(num: U256, mont: Mont) -> Self {
        let num = mont.to_mont(num);
        MontForm {
            mont: Rc::new(RefCell::new(mont)),
            num,
        }
    }
    pub fn derive_from_u256(&self, num: U256) -> Self {
        let num = self.mont.borrow().to_mont(num);
        MontForm {
            mont: self.mont.clone(),
            num,
        }
    }

    pub fn new(num: U256, mont: Mont) -> Self {
        MontForm {
            mont: Rc::new(RefCell::new(mont)),
            num,
        }
    }
    pub fn derive(&self, num: U256) -> Self {
        MontForm {
            mont: self.mont.clone(),
            num,
        }
    }

    pub fn pow(&self, pow: U256) -> Self {
        let num = self.mont.borrow().pow(self.num, pow);
        self.derive(num)
    }
}

impl From<MontForm> for U256 {
    fn from(m: MontForm) -> Self {
        m.mont.borrow().reduce(m.num.into())
    }
}

impl Add for MontForm {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.num + rhs.num;
        let sum = if sum > self.mont.borrow().n {
            sum - self.mont.borrow().n
        } else {
            sum
        };
        self.derive(sum)
    }
}

impl<'a> Add<&'a MontForm> for MontForm {
    type Output = Self;
    fn add(self, rhs: &'a Self) -> Self::Output {
        let sum = self.num + rhs.num;
        let sum = if sum > self.mont.borrow().n {
            sum - self.mont.borrow().n
        } else {
            sum
        };
        self.derive(sum)
    }
}

impl<'a> Add<&'a MontForm> for &'a MontForm {
    type Output = MontForm;
    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.num + rhs.num;
        let sum = if sum > self.mont.borrow().n {
            sum - self.mont.borrow().n
        } else {
            sum
        };
        self.derive(sum)
    }
}

impl Sub for MontForm {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let sub = if self.num >= rhs.num {
            self.num - rhs.num
        } else {
            self.num + self.mont.borrow().n - rhs.num
        };
        self.derive(sub)
    }
}

impl<'a> Sub<&'a MontForm> for MontForm {
    type Output = Self;
    fn sub(self, rhs: &'a Self) -> Self::Output {
        let sub = if self.num >= rhs.num {
            self.num - rhs.num
        } else {
            self.num + self.mont.borrow().n - rhs.num
        };
        self.derive(sub)
    }
}

impl<'a> Sub<&'a MontForm> for &'a MontForm {
    type Output = MontForm;
    fn sub(self, rhs: Self) -> Self::Output {
        let sub = if self.num >= rhs.num {
            self.num - rhs.num
        } else {
            self.num + self.mont.borrow().n - rhs.num
        };
        self.derive(sub)
    }
}

impl Mul for MontForm {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mul = self.mont.borrow().multi(self.num, rhs.num);
        self.derive(mul)
    }
}

impl<'a> Mul<&'a MontForm> for MontForm {
    type Output = Self;
    fn mul(self, rhs: &'a Self) -> Self::Output {
        let mul = self.mont.borrow().multi(self.num, rhs.num);
        self.derive(mul)
    }
}

impl<'a> Mul<&'a MontForm> for &'a MontForm {
    type Output = MontForm;
    fn mul(self, rhs: Self) -> Self::Output {
        let mul = self.mont.borrow().multi(self.num, rhs.num);
        self.derive(mul)
    }
}
