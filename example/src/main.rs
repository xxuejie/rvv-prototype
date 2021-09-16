#![feature(asm)]

extern crate rvv;
use rvv::rvv_vector;

use numext_fixed_uint::{u256, U256};

#[rvv_vector]
fn foo(a: U256, b: U256, c: U256, d: U256) -> U256 {
    let e = a + b * c;
    e - d
}

fn main() {
    let a = u256!("0x1");
    let b = u256!("0x2");
    let c = u256!("0x3");
    let d = u256!("0x4");

    let f = foo(a, b, c, d);

    if f.bit(0).unwrap_or(false) {
        println!("Hello, world!");
    }
}
