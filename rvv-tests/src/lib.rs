#![no_std]
#![feature(asm)]

extern crate alloc;

#[cfg(feature = "use_rvv_vector")]
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

#[macro_export]
macro_rules! print {
    ($fmt:literal) => {
        ckb_std::syscalls::debug(alloc::format!($fmt));
    };
    ($fmt:literal, $($args:expr),+) => {
        ckb_std::syscalls::debug(alloc::format!($fmt, $($args), +));
    };
}

#[cfg(feature = "use_rvv_vector")]
#[rvv_vector(show_asm)]
#[inline(always)]
#[no_mangle]
pub fn simple_ops(mut ax: U256, bx: U256, cx: U256) -> U256 {
    if ax > bx && bx == cx {
        ax = ax * (cx + bx);
    }
    ax = (ax + bx) * cx;
    ax
}

#[cfg(not(feature = "use_rvv_vector"))]
pub fn simple_ops(mut ax: U256, bx: U256, cx: U256) -> U256 {
    if ax > bx && bx == cx {
        ax = ax.wrapping_mul(cx.wrapping_add(bx));
    }
    ax = (ax.wrapping_add(bx)).wrapping_mul(cx);
    ax
}
