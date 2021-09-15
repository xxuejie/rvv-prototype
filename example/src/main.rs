#![feature(asm)]

extern crate rvv;
use rvv::rvv_vector;

use std::ops::{Add, Sub, Mul};

pub struct U256(u8);

impl Add for U256 {
    type Output = Self;

    fn add(self, _other: Self) -> Self {
        unimplemented!()
    }
}

impl Sub for U256 {
    type Output = Self;

    fn sub(self, _other: Self) -> Self {
        unimplemented!()
    }
}

impl Mul for U256 {
    type Output = Self;

    fn mul(self, _other: Self) -> Self {
        unimplemented!()
    }
}

#[rvv_vector]
fn foo(a: U256, b: U256, c: U256) -> U256 {
    a + b * c
}

fn main() {
    let a = U256(1);
    let b = U256(2);
    let c = U256(3);

    let d = foo(a, b, c);

    if d.0 > 0 {
        println!("Hello, world!");
    }
}
