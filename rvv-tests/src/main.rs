#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

use ckb_std::{default_alloc};

ckb_std::entry!(program_entry);
default_alloc!();

use rvv_simulator_runtime::Uint;
use rvv_tests::{bn256_add, U256, print};

fn program_entry() -> i8 {
    let ax = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let bx = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    let cx = U256!([0xaa, 0xbb, 0xcc, 0xdd]);

    print!("ax: {:?}, bx: {:?}, cx: {:?}", ax, bx, cx);
    let f = bn256_add(ax, bx, cx);
    print!("f: {:?}", f.0);
    assert_eq!(f, U256!([1537820, 4714882, 10422462, 18140649]));
    0
}
