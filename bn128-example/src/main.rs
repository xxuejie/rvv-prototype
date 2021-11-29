#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

extern crate rvv;
use alloc::format;
use ckb_std::{default_alloc, syscalls::debug};
ckb_std::entry!(program_entry);
default_alloc!();

fn main() {
    // alt_bn128::ethereum::ut::test_alt_bn128_add();
    // debug!("test_alt_bn128_add     pass");
    // alt_bn128::ethereum::ut::test_alt_bn128_mul();
    // debug!("test_alt_bn128_mul     pass");
    if cfg!(feature = "use_rvv_vector") {
        debug(format!("feature = use_rvv_vector"));
    } else {
        debug(format!("feature != use_rvv_vector"));
    }
    if cfg!(feature = "simulator") {
        debug(format!("feature = simulator"));
    } else {
        debug(format!("feature != simulator"))
    }
    debug(format!("start test_alt_bn128_pairing ..."));
    alt_bn128_example::ethereum::ut::test_alt_bn128_pairing();
    debug(format!("test_alt_bn128_pairing pass"));
}

pub fn program_entry() -> i8 {
    main();
    return 0;
}
