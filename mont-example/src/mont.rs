// based on https://research.nccgroup.com/2021/06/09/optimizing-pairing-based-cryptography-montgomery-arithmetic-in-rust/
#![allow(dead_code)]

use crate::U256;

use ckb_std::debug;

extern crate rvv;
use rvv::rvv_vector;

// Extended Euclidean algorithm
// https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
pub fn egcd(a: i64, b: i64) -> (i64, i64, i64) {
    assert!(a < b);
    if a == 0 {
        (b, 0, 1)
    } else {
        let (g, x, y) = egcd(b % a, a);
        (g, y - (b / a) * x, x)
    }
}

struct Mont {
    pub rp1: U256,
    pub np1: U256,
    pub r: U256,
    pub n: U256,
    pub bits: usize,
}

impl Mont {
    pub fn new(n: u64) -> Self {
        let r = 2u64.pow(32);
        Mont {
            r: r.into(),
            n: n.into(),
            rp1: 0u64.into(),
            np1: 0u64.into(),
            bits: 32,
        }
    }

    pub fn precompute(&mut self) {
        let r: u64 = self.r.clone().into();
        let n: u64 = self.n.clone().into();

        let r = r as i64;
        let n = n as i64;
        let (gcd, np, rp) = egcd(n, r);
        assert_eq!(gcd, 1);

        let rp1 = rp + n;
        assert!(rp1 >= 0);
        self.rp1 = (rp1 as u64).into();

        let np1 = r - np;
        assert!(np1 >= 0);
        self.np1 = (np1 as u64).into();
    }
}

// m = T*Np1 mod R
// U = (T + m * N) / R
// The overall process delivers T · R−1 mod N without an expensive division operation!

#[rvv_vector]
#[no_mangle]
pub fn reduce(np1: U256, n: U256, t: U256) -> U256 {
    let t0 = U256::from(u32::from(t));
    let m = U256::from(u32::from(t0 * np1));
    let lit_bits = U256::from(32u32);
    let u = (t + m * n) >> lit_bits;

    let u2 = if u >= n { u - n } else { u };
    U256::from(u32::from(u2))
}

#[rvv_vector]
#[no_mangle]
pub fn to_mont(r: U256, n: U256, x: U256) -> U256 {
    let result = (x * r) % n;
    U256::from(u32::from(result))
}

#[rvv_vector]
#[no_mangle]
pub fn multi(np1: U256, n: U256, x: U256, y: U256) -> U256 {
    let xy = x * y;
    let res = reduce(np1, n, xy);
    res
}

pub fn mont_main() {
    let mut mont = Mont::new(17);
    mont.precompute();

    let x: u64 = 100;
    let y: u64 = 200;

    // into montgomery form
    debug!(
        "r = {:?}, n = {:?}, x = {:?}, y = {:?}",
        mont.r, mont.n, x, y
    );

    let x2 = to_mont(mont.r.clone(), mont.n.clone(), x.into());
    let y2 = to_mont(mont.r.clone(), mont.n.clone(), y.into());
    debug!("x2 = {:?}, y2 = {:?}", x2, y2);

    // do multiplication operation
    debug!(
        "np1 = {:?}, n = {:?}, x = {:?}, y = {:?}",
        mont.np1, mont.n, x2, y2
    );
    let xy2 = multi(mont.np1.clone(), mont.n.clone(), x2, y2);
    debug!("xy2 = {:?}", xy2);

    let mont_n: u64 = mont.n.clone().into();
    let xy2: u64 = xy2.into();
    // into normal form
    let xy = reduce(mont.np1.clone(), mont.n.clone(), xy2.into());
    debug!("xy = {:?}", xy);

    let xy: u64 = xy.into();
    // workaround
    // the result should be same
    assert_eq!(xy, (x * y) % mont_n);
}
