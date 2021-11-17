#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

extern crate rvv;
use ckb_std::{debug, default_alloc};
ckb_std::entry!(program_entry);
default_alloc!();

fn main() {
    // alt_bn128::ethereum::ut::test_alt_bn128_add();
    // debug!("test_alt_bn128_add     pass");
    // alt_bn128::ethereum::ut::test_alt_bn128_mul();
    // debug!("test_alt_bn128_mul     pass");
    alt_bn128::ethereum::ut::test_alt_bn128_pairing();
    debug!("test_alt_bn128_pairing pass");
}

pub fn program_entry() -> i8 {
    main();
    return 0;
}
