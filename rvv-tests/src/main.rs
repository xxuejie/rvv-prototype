#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

use ckb_std::default_alloc;

ckb_std::entry!(program_entry);
default_alloc!();

use rvv_simulator_runtime::Uint;
use rvv_tests::U256;

fn test_simple_ops() {
    let ax = U256!([0x1122, 0x2233, 0x3344, 0x4455]);
    let bx = U256!([0x1234, 0x2345, 0x4567, 0x5678]);
    let cx = U256!([0xaa, 0xbb, 0xcc, 0xdd]);

    let f = rvv_tests::simple_ops(ax, bx, cx);
    assert_eq!(f, U256!([1537820, 4714882, 10422462, 18140649]));
}

fn program_entry() -> i8 {
    test_simple_ops();
    0
}
