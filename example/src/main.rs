#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

extern crate rvv;
use ckb_std::{debug, default_alloc};
use rvv::{rvv_vector, rvv_vector2};
ckb_std::entry!(program_entry);
default_alloc!();
// use numext_fixed_uint::{u256, U256};

#[derive(Clone, Debug, Default, Ord, PartialOrd, PartialEq, Eq)]
pub struct U256([u64; 4]);

impl U256 {
    pub fn from_u64(value: u64) -> U256 {
        U256([value, 0, 0, 0])
    }

    pub fn to_le_bytes(&self) -> [u8; 32] {
        let mut buf = [0u8; 32];
        for i in 0..4 {
            buf[i * 8..(i + 1) * 8].copy_from_slice(&self.0[i].to_le_bytes()[..]);
        }
        buf
    }

    pub fn from_le_bytes(bytes: &[u8; 32]) -> U256 {
        let mut inner = [0u64; 4];
        for i in 0..4 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
            inner[i] = u64::from_le_bytes(buf);
        }
        U256(inner)
    }
}

#[rvv_vector2]
#[no_mangle]
fn bn256_add(
    mut ax: U256,
    // mut ay: U256,
    // mut az: U256,
    bx: U256,
    // mut by: U256,
    // mut bz: U256,
    cx: U256,
    // mut cy: U256,
    // mut cz: U256,
) -> U256 {
    ax = ax + bx * cx; // case.1: complex ops, with temporary variable
                       // let x = d * c;     // case.2: simple op, with temporary variable
                       // let y = ax >= by;  // case.3: compare, with temporary variable
                       // a += c;            // case.4: simple op, then assgin to exists variable
                       // let dx = bx - ax;
                       // bx = bx >> cx;
                       // ax = bx + cx; // case.5: simple mod op
                       //               // -c                 // TODO case.6: return nagetive value
                       // ax = ax % dx;
    ax
    // return;            // TODO case.7: early return
    // if y {             // TODO case.8: if else
    //     c
    // } else {
    //     d
    // }
    // loop {             // TODO case.9: loop + if + break + continue
    //     a += c;
    //     if a > b {
    //         break;
    //     }
    //     if a < b {
    //         continue;
    //     }
    // }
}

fn program_entry() -> i8 {
    let ax = U256([0x1122, 0x2233, 0x3344, 0x4455]);
    // let ay = U256::from_u64(0x2);
    // let az = U256::from_u64(0x3);
    let bx = U256([0x1234, 0x2345, 0x4567, 0x5678]);
    // let by = U256::from_u64(0x5);
    // let bz = U256::from_u64(0x6);
    let cx = U256([0xaa, 0xbb, 0xcc, 0xdd]);
    // let cy = U256::from_u64(0x8);
    // let cz = U256::from_u64(0x9);

    let f = bn256_add(
        ax, // ay, az,
        bx, // by, bz,
        cx, // cy, cz
    );
    assert_eq!(f, U256([204914, 1819081, 18446744073705256681u64, 2953]));
    // assert_eq!(f, U256([750280, 2317561, 4780776, 8205460]));
    0
}
