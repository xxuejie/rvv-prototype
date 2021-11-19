use core::{convert::TryInto, str::FromStr, u64::MAX};
use rvv_simulator_runtime::{overflowing, FromDecStrErr, Uint};

type U256 = Uint<4>;
type U512 = Uint<8>;

macro_rules! U256 {
    ($e: expr) => {
        Uint::<4>($e)
    };
}

macro_rules! U512 {
    ($e: expr) => {
        Uint::<8>($e)
    };
}

#[cfg(feature = "std")]
#[test]
fn hash_impl_is_the_same_as_for_a_slice() {
    use core::hash::{Hash, Hasher as _};
    use std::collections::hash_map::DefaultHasher;

    let uint_hash = {
        let mut h = DefaultHasher::new();
        let uint = U256::from(123u64);
        Hash::hash(&uint, &mut h);
        h.finish()
    };
    let slice_hash = {
        let mut h = DefaultHasher::new();
        Hash::hash(&[123u64, 0, 0, 0], &mut h);
        h.finish()
    };
    assert_eq!(uint_hash, slice_hash);
}

// https://github.com/paritytech/parity-common/issues/420
#[test]
fn const_matching_works() {
    const ONE: U256 = U256!([1, 0, 0, 0]);
    match U256::zero() {
        ONE => unreachable!(),
        _ => {}
    }
}

#[test]
fn u128_conversions() {
    let mut a = U256::from(u128::MAX);
    assert_eq!(a.low_u128(), u128::MAX);
    a += 2u128.into();
    assert_eq!(a.low_u128(), 1u128);
    a -= 3u128.into();
    assert_eq!(a.low_u128(), u128::MAX - 1);
}

#[test]
fn uint256_checked_ops() {
    let z = U256::from(0);
    let a = U256::from(10);
    let b = !U256::from(1);

    assert_eq!(
        U256::from(10).checked_pow(U256::from(0)),
        Some(U256::from(1))
    );
    assert_eq!(
        U256::from(10).checked_pow(U256::from(1)),
        Some(U256::from(10))
    );
    assert_eq!(
        U256::from(10).checked_pow(U256::from(2)),
        Some(U256::from(100))
    );
    assert_eq!(
        U256::from(10).checked_pow(U256::from(3)),
        Some(U256::from(1000))
    );
    assert_eq!(
        U256::from(10).checked_pow(U256::from(20)),
        Some(U256::exp10(20))
    );
    assert_eq!(U256::from(2).checked_pow(U256::from(0x100)), None);
    assert_eq!(U256::max_value().checked_pow(U256::from(2)), None);

    assert_eq!(a.checked_add(b), None);
    assert_eq!(a.checked_add(a), Some(20.into()));

    assert_eq!(a.checked_sub(b), None);
    assert_eq!(a.checked_sub(a), Some(0.into()));

    assert_eq!(a.checked_mul(b), None);
    assert_eq!(a.checked_mul(a), Some(100.into()));

    assert_eq!(a.checked_div(z), None);
    assert_eq!(a.checked_div(a), Some(1.into()));

    assert_eq!(a.checked_rem(z), None);
    assert_eq!(a.checked_rem(a), Some(0.into()));

    assert_eq!(a.checked_neg(), None);
    assert_eq!(z.checked_neg(), Some(z));
}

#[test]
fn uint256_from() {
    let e = U256!([10, 0, 0, 0]);

    // test unsigned initialization
    let ua = U256::from(10u8);
    let ub = U256::from(10u16);
    let uc = U256::from(10u32);
    let ud = U256::from(10u64);
    assert_eq!(e, ua);
    assert_eq!(e, ub);
    assert_eq!(e, uc);
    assert_eq!(e, ud);

    // test initialization from bytes
    let va = U256::from(&[10u8][..]);
    assert_eq!(e, va);

    // more tests for initialization from bytes
    assert_eq!(U256!([0x1010, 0, 0, 0]), U256::from(&[0x10u8, 0x10][..]));
    assert_eq!(U256!([0x12f0, 0, 0, 0]), U256::from(&[0x12u8, 0xf0][..]));
    assert_eq!(U256!([0x12f0, 0, 0, 0]), U256::from(&[0, 0x12u8, 0xf0][..]));
    assert_eq!(
        U256!([0x12f0, 0, 0, 0]),
        U256::from(&[0, 0, 0, 0, 0, 0, 0, 0x12u8, 0xf0][..])
    );
    assert_eq!(
        U256!([0x12f0, 1, 0, 0]),
        U256::from(&[1, 0, 0, 0, 0, 0, 0, 0x12u8, 0xf0][..])
    );
    assert_eq!(
        U256!([0x12f0, 1, 0x0910203040506077, 0x8090a0b0c0d0e0f0]),
        U256::from(
            &[
                0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0, 0x09, 0x10, 0x20, 0x30, 0x40, 0x50,
                0x60, 0x77, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0x12u8, 0xf0
            ][..]
        )
    );
    assert_eq!(
        U256!([0x00192437100019fa, 0x243710, 0, 0]),
        U256::from(&[0x24u8, 0x37, 0x10, 0, 0x19, 0x24, 0x37, 0x10, 0, 0x19, 0xfa][..])
    );

    // test initializtion from string
    let sa = U256::from_str("0a").unwrap();
    let sa2 = U256::from_str("0x0a").unwrap();
    assert_eq!(sa2, sa);
    assert_eq!(e, sa);
    assert_eq!(U256!([0, 0, 0, 0]), U256::from_str("").unwrap());
    assert_eq!(U256!([0x1, 0, 0, 0]), U256::from_str("1").unwrap());
    assert_eq!(U256!([0x101, 0, 0, 0]), U256::from_str("101").unwrap());
    assert_eq!(U256!([0x1010, 0, 0, 0]), U256::from_str("1010").unwrap());
    assert_eq!(U256!([0x12f0, 0, 0, 0]), U256::from_str("12f0").unwrap());
    assert_eq!(
        U256!([0x12f0, 0, 0, 0]),
        U256::from_str("0000000012f0").unwrap()
    );
    assert_eq!(
        U256!([0x12f0, 1, 0, 0]),
        U256::from_str("0100000000000012f0").unwrap()
    );
    assert_eq!(
        U256!([0x12f0, 1, 0x0910203040506077, 0x8090a0b0c0d0e0f0]),
        U256::from_str("8090a0b0c0d0e0f00910203040506077000000000000000100000000000012f0").unwrap()
    );

    // This string contains more bits than what fits in a U256.
    // TODO
    // assert!(U256::from_str("000000000000000000000000000000000000000000000000000000000000000000").is_err());
    // assert!(U256::from_str("100000000000000000000000000000000000000000000000000000000000000000").is_err());
}
