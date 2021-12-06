#![no_std]
#![feature(asm)]

extern crate alloc;

pub mod cases;

pub type U256 = rvv_simulator_runtime::Uint<4>;
pub type U512 = rvv_simulator_runtime::Uint<8>;

#[macro_export]
macro_rules! U256 {
    ($e: expr) => {
        rvv_simulator_runtime::Uint::<4>($e)
    };
}
#[macro_export]
macro_rules! U512 {
    ($e: expr) => {
        rvv_simulator_runtime::Uint::<8>($e)
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

#[macro_export]
macro_rules! print_assert_eq {
    ($left:expr, $right:expr, Uint) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                print_assert_eq!(left_val.0, right_val.0);
            }
        }
    };
    ($left:expr, $right:expr) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    $crate::print!("{}:{}:{}", file!(), line!(), column!());
                    $crate::print!(" left: {:?}", left_val);
                    $crate::print!("right: {:?}", right_val);
                }
                assert_eq!(left_val, right_val);
            }
        }
    };
}
