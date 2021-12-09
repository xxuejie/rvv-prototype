use rvv::rvv_vector;

use super::{print_assert_eq, U256};

pub fn run_all_test_cases() {
    test_simple_mixed_ops();
    test_add();
    test_sub();
    test_mul();
    test_div();
    test_rem();
}

#[rvv_vector(show_asm)]
#[inline(always)]
#[no_mangle]
fn simple_mixed_ops(mut a: U256, b: U256, c: U256) -> U256 {
    if b > a && b >= c {
        a = a * (c + b);
    }
    a = (a + b) * c;
    a
}

fn simple_mixed_ops_raw(mut a: U256, b: U256, c: U256) -> U256 {
    if b > a && b >= c {
        a = a.wrapping_mul(c.wrapping_add(b));
    }
    a = (a.wrapping_add(b)).wrapping_mul(c);
    a
}

pub fn test_simple_mixed_ops() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    let c = U256!([0xaa, 0xbb, 0xcc, 0xdd]);
    print_assert_eq!(
        simple_mixed_ops_raw(a, b, c),
        simple_mixed_ops(a, b, c),
        Uint
    );
}

// ==== test cases for core::ops::*  ====
//  - Just test for common case for now
//  - TODO use `proptest` to improve the tests

#[rvv_vector(show_asm)]
fn op_add(a: U256, b: U256) -> U256 {
    a + b
}
#[rvv_vector(show_asm)]
fn method_wrapping_add(a: U256, b: U256) -> U256 {
    a.wrapping_add(b)
}
#[rvv_vector(show_asm)]
fn method_overflowing_add(a: U256, b: U256) -> U256 {
    a.overflowing_add(b).0
}
#[rvv_vector(show_asm)]
fn method_checked_add(a: U256, b: U256) -> U256 {
    a.checked_add(b).unwrap()
}
// FIXME: waiting ckb-vm to support this instruction
// #[rvv_vector(show_asm)]
// fn method_saturating_add(a: U256, b: U256) -> U256 {
//     a.saturating_add(b)
// }
fn op_add_raw(a: U256, b: U256) -> U256 {
    a.wrapping_add(b)
}
pub fn test_add() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    print_assert_eq!(op_add_raw(a, b), op_add(a, b), Uint);
    print_assert_eq!(op_add_raw(a, b), method_wrapping_add(a, b), Uint);
    print_assert_eq!(op_add_raw(a, b), method_overflowing_add(a, b), Uint);
    print_assert_eq!(op_add_raw(a, b), method_checked_add(a, b), Uint);
    // print_assert_eq!(op_add_raw(a, b), method_saturating_add(a, b), Uint);
}

#[rvv_vector(show_asm)]
fn op_sub(a: U256, b: U256) -> U256 {
    a - b
}
#[rvv_vector(show_asm)]
fn method_wrapping_sub(a: U256, b: U256) -> U256 {
    a.wrapping_sub(b)
}
#[rvv_vector(show_asm)]
fn method_overflowing_sub(a: U256, b: U256) -> U256 {
    a.overflowing_sub(b).0
}
#[rvv_vector(show_asm)]
fn method_checked_sub(a: U256, b: U256) -> Option<U256> {
    a.checked_sub(b)
}

fn op_sub_raw(a: U256, b: U256) -> U256 {
    a.wrapping_sub(b)
}
pub fn test_sub() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    print_assert_eq!(op_sub_raw(a, b), op_sub(a, b), Uint);
    print_assert_eq!(op_sub_raw(a, b), method_wrapping_sub(a, b), Uint);
    print_assert_eq!(op_sub_raw(a, b), method_overflowing_sub(a, b), Uint);
    print_assert_eq!(a.checked_sub(b), method_checked_sub(a, b));
}

#[rvv_vector(show_asm)]
fn op_mul(a: U256, b: U256) -> U256 {
    a * b
}
#[rvv_vector(show_asm)]
fn method_wrapping_mul(a: U256, b: U256) -> U256 {
    a.wrapping_mul(b)
}
#[rvv_vector(show_asm)]
fn method_overflowing_mul(a: U256, b: U256) -> U256 {
    a.overflowing_mul(b).0
}
#[rvv_vector(show_asm)]
fn method_checked_mul(a: U256, b: U256) -> Option<U256> {
    a.checked_mul(b)
}
fn op_mul_raw(a: U256, b: U256) -> U256 {
    a.wrapping_mul(b)
}
pub fn test_mul() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    print_assert_eq!(op_mul_raw(a, b), op_mul(a, b), Uint);
    print_assert_eq!(op_mul_raw(a, b), method_wrapping_mul(a, b), Uint);
    print_assert_eq!(op_mul_raw(a, b), method_overflowing_mul(a, b), Uint);
    print_assert_eq!(a.checked_mul(b), method_checked_mul(a, b));
}

#[rvv_vector(show_asm)]
fn op_div(a: U256, b: U256) -> U256 {
    a / b
}
// TODO: support this in `simulator`
// #[rvv_vector(show_asm)]
// fn method_wrapping_div(a: U256, b: U256) -> U256 {
//     a.wrapping_div(b)
// }
#[rvv_vector(show_asm)]
fn method_div(a: U256, b: U256) -> U256 {
    a.checked_div(b).unwrap_or_else(U256::max_value)
}
fn op_div_raw(a: U256, b: U256) -> U256 {
    a.checked_div(b).unwrap_or_else(U256::max_value)
}
pub fn test_div() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    print_assert_eq!(op_div_raw(a, b), op_div(a, b), Uint);
    // print_assert_eq!(op_div_raw(a, b), method_wrapping_div(a, b), Uint);
    print_assert_eq!(op_div_raw(a, b), method_div(a, b), Uint);
}

#[rvv_vector(show_asm)]
fn op_rem(a: U256, b: U256) -> U256 {
    a % b
}
// TODO: support this in `simulator`
// #[rvv_vector(show_asm)]
// fn method_wrapping_rem(a: U256, b: U256) -> U256 {
//     a.wrapping_rem(b)
// }
#[rvv_vector(show_asm)]
fn method_rem(a: U256, b: U256) -> U256 {
    a.checked_rem(b).unwrap_or_else(U256::zero)
}
fn op_rem_raw(a: U256, b: U256) -> U256 {
    a.checked_rem(b).unwrap_or_else(U256::zero)
}
pub fn test_rem() {
    let a = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let b = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    print_assert_eq!(op_rem_raw(a, b), op_rem(a, b), Uint);
    // print_assert_eq!(op_rem_raw(a, b), method_wrapping_rem(a, b), Uint);
    print_assert_eq!(op_rem_raw(a, b), method_rem(a, b), Uint);
}
