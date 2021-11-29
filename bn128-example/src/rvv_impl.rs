use rvv::rvv_vector;
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

// implemented by rvv_vector
#[rvv_vector]
pub fn mont_reduce(np1: U256, n: U256, t: U512, bits: usize) -> U256 {
    let t0: U512 = U256::from(t).into(); // low part of `t`, same as `% self.r`, avoid overflow
    let np1_512: U512 = U512::from(np1);
    let m_512: U512 = U256::from(t0 * np1_512).into(); // `% self.r`
    let n_512: U512 = U512::from(n);
    let bits_512: U512 = U512::from(bits);
    let u: U512 = (t + m_512 * n_512) >> bits_512; // `/ self.r`
    if u >= n_512 {
        U256::from(u - n_512)
    } else {
        U256::from(u)
    }
}

#[rvv_vector]
pub fn mont_multi(np1: U256, n: U256, x: U256, y: U256, bits: usize) -> U256 {
    let x_512: U512 = x.into();
    let y_512: U512 = y.into();

    let xy: U512 = x_512 * y_512;
    mont_reduce(np1, n, xy, bits)
}

#[inline(always)]
fn from_u128pair(n: &[u128; 2]) -> U256 {
    let mut buf = [0u8; 32];
    buf[0..16].copy_from_slice(&n[0].to_le_bytes());
    buf[16..32].copy_from_slice(&n[1].to_le_bytes());
    U256::from_little_endian(&buf)
}

pub fn mul_reduce_internal(
    this: &mut [u128; 2],
    by: &[u128; 2],
    modulus: &[u128; 2],
    inv: u128,
    inv_high: u128,
) {
    let x: U256 = from_u128pair(this);
    let y: U256 = from_u128pair(by);
    let n: U256 = from_u128pair(modulus);
    let np1: U256 = U256::from(inv_high) << 128 | U256::from(inv);
    let Uint::<4>(ref result) = mont_multi(np1, n, x, y, 256);
    this[0] = result[0] as u128 | (result[1] as u128) << 64;
    this[1] = result[2] as u128 | (result[3] as u128) << 64;
}
