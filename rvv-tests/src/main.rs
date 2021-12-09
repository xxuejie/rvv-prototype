#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

use ckb_std::default_alloc;

ckb_std::entry!(program_entry);
default_alloc!();

fn program_entry() -> i8 {
    rvv_tests::cases::run_all_test_cases();
    0
}
