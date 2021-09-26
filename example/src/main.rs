#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

extern crate rvv;
use rvv::rvv_vector;
use ckb_std::{
    default_alloc,
};
ckb_std::entry!(program_entry);
 default_alloc!();
// use numext_fixed_uint::{u256, U256};

#[derive(Debug, Default)]
pub struct U256([u64; 4]);

impl U256 {
    pub fn to_le_bytes(&self) -> [u8; 32] {
        let mut buf = [0u8; 32];
        for i in 0..4 {
            buf[i*8..(i+1)*8].copy_from_slice(&self.0[i].to_le_bytes()[..]);
        }
        buf
    }

    pub fn from_le_bytes(bytes: &[u8; 32]) -> U256 {
        let mut inner = [0u64; 4];
        for i in 0..4 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[i*8..(i+1)*8]);
            inner[i] = u64::from_le_bytes(buf);
        }
        U256(inner)
    }
}

macro_rules! u256 {
    ($expression:expr) => {
        U256([$expression, 0, 0, 0])
    };
}

#[rvv_vector]
fn foo(a: U256, b: U256, c: U256, d: U256) -> U256 {
    // let e = a + b * c;
    // d * e
    a * b
}

fn program_entry() -> i8 {
    let a = u256!(0x1);
    let b = u256!(0x2);
    let c = u256!(0x3);
    let d = u256!(0x4);

    let f = foo(a, b, c, d);
    0
}
