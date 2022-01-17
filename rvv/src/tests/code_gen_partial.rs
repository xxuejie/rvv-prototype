use quote::quote;

use super::run_rvv_test;

#[test]
fn test_u256_ops_add() {
    let input1 = quote! {
        fn ops_add(a: U256, b: U256) -> U256 {
            a + b
        }
    };
    let input2 = quote! {
        fn ops_add(a: U256, b: U256) -> U256 {
            a.wrapping_add(b)
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_add(a: U256, b: U256) -> U256 {
            a.wrapping_add(b)
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_add(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vadd.vv v3, v1, v2 - 34669015";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x02") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input1, expected_output.clone());
    run_rvv_test(input2, expected_output);
}

#[test]
fn test_u256_ops_mul() {
    let input1 = quote! {
        fn ops_mul(a: U256, b: U256) -> U256 {
            a * b
        }
    };
    let input2 = quote! {
        fn ops_mul(a: U256, b: U256) -> U256 {
            a.wrapping_mul(b)
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_mul(a: U256, b: U256) -> U256 {
            a.wrapping_mul(b)
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_mul(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmul.vv v3, v1, v2 - 2517705175";
                unsafe { asm!(".byte 0xd7, 0x21, 0x11, 0x96") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input1, expected_output.clone());
    run_rvv_test(input2, expected_output);
}

#[test]
fn test_u256_ops_div() {
    let input1 = quote! {
        fn ops_div(a: U256, b: U256) -> U256 {
            a / b
        }
    };
    let input2 = quote! {
        fn ops_div(a: U256, b: U256) -> U256 {
            a.wrapping_div(b)
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_div(a: U256, b: U256) -> U256 {
            a.checked_div(b).unwrap_or_else(|| U256::max_value())
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_div(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vdivu.vv v3, v1, v2 - 2182160855";
                unsafe { asm!(".byte 0xd7, 0x21, 0x11, 0x82") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input1, expected_output.clone());
    // FIXME: fix simulator codegen
    #[cfg(not(feature = "simulator"))]
    {
        run_rvv_test(input2, expected_output);
    }
}

#[test]
fn test_u256_ops_rem() {
    let input1 = quote! {
        fn ops_rem(a: U256, b: U256) -> U256 {
            a % b
        }
    };
    let input2 = quote! {
        fn ops_rem(a: U256, b: U256) -> U256 {
            a.wrapping_rem(b)
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_rem(a: U256, b: U256) -> U256 {
            a % b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_rem(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vremu.vv v3, v1, v2 - 2316378583";
                unsafe { asm!(".byte 0xd7, 0x21, 0x11, 0x8a") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input1, expected_output.clone());
    // FIXME: fix simulator codegen
    #[cfg(not(feature = "simulator"))]
    {
        run_rvv_test(input2, expected_output);
    }
}

#[test]
fn test_u256_ops_bitxor() {
    let input = quote! {
        fn ops_bitxor(a: U256, b: U256) -> U256 {
            a ^ b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitxor(a: U256, b: U256) -> U256 {
            a ^ b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitxor(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vxor.vv v3, v1, v2 - 772866519";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x2e") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_shl() {
    let input = quote! {
        fn ops_shl(a: U256, b: U256) -> U256 {
            a << b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_shl(a: U256, b: U256) -> U256 {
            a << b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_shl(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vsll.vv v3, v1, v2 - 2517696983";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x96") }
                let _ = "vse256.v v3, (t0) - 302174631";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0xa7, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_add_assign() {
    let input = quote! {
        fn ops_add_assign(mut a: U256, b: U256) {
            a += b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_add_assign(mut a: U256, b: U256) {
            a = a.wrapping_add(b);
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_add_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0", "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0", "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vadd.vv v1, v1, v2 - 34668759";
            unsafe { asm!(".byte 0xd7, 0x00, 0x11, 0x02") };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_mul_assign() {
    let input = quote! {
        fn ops_mul_assign(mut a: U256, b: U256) {
            a *= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_mul_assign(mut a: U256, b: U256) {
            a = a.wrapping_mul(b);
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_mul_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vmul.vv v1, v1, v2 - 2517704919";
            unsafe { asm!(".byte 0xd7, 0x20, 0x11, 0x96") };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_div_assign() {
    let input = quote! {
        fn ops_div_assign(mut a: U256, b: U256) {
            a /= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_div_assign(mut a: U256, b: U256) {
            a = a.checked_div(b).unwrap_or_else(|| U256::max_value());
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_div_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vdivu.vv v1, v1, v2 - 2182160599";
            unsafe { asm!(".byte 0xd7, 0x20, 0x11, 0x82") };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_rem_assign() {
    let input = quote! {
        fn ops_rem_assign(mut a: U256, b: U256) {
            a %= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_rem_assign(mut a: U256, b: U256) {
            a %= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_rem_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vremu.vv v1, v1, v2 - 2316378327";
            unsafe { asm!(".byte 0xd7, 0x20, 0x11, 0x8a") };
        }

    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_bitxor_assign() {
    let input = quote! {
        fn ops_bitxor_assign(mut a: U256, b: U256) {
            a ^= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitxor_assign(mut a: U256, b: U256) {
            a ^= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitxor_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vxor.vv v1, v1, v2 - 772866263";
            unsafe { asm!(".byte 0xd7, 0x00, 0x11, 0x2e") };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_shl_assign() {
    let input = quote! {
        fn ops_shl_assign(mut a: U256, b: U256) {
            a <<= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_shl_assign(mut a: U256, b: U256) {
            a <<= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_shl_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vsll.vv v1, v1, v2 - 2517696727";
            unsafe { asm!(".byte 0xd7, 0x00, 0x11, 0x96") };
        }
    };
    run_rvv_test(input, expected_output);
}

// ==== `bool = T op T` ====
#[test]
fn test_u256_ops_eq() {
    let input = quote! {
        fn ops_eq(a: U256, b: U256) -> bool {
            a == b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_eq(a: U256, b: U256) -> bool {
            a == b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_eq(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmseq.vv v3, v1, v2 - 1645281751";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x62") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }

    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_lt() {
    let input = quote! {
        fn ops_lt(a: U256, b: U256) -> bool {
            a < b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_lt(a: U256, b: U256) -> bool {
            a < b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_lt(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmsltu.vv v3, v1, v2 - 1779499479";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x6a") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_le() {
    let input = quote! {
        fn ops_le(a: U256, b: U256) -> bool {
            a <= b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_le(a: U256, b: U256) -> bool {
            a <= b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_le(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmsleu.vv v3, v1, v2 - 1913717207";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x72") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_ne() {
    let input = quote! {
        fn ops_ne(a: U256, b: U256) -> bool {
            a != b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_ne(a: U256, b: U256) -> bool {
            a != b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_ne(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmsne.vv v3, v1, v2 - 1712390615";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x66") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_ge() {
    let input = quote! {
        fn ops_ge(a: U256, b: U256) -> bool {
            a >= b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_ge(a: U256, b: U256) -> bool {
            a >= b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_ge(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmsleu.vv v3, v2, v1 - 1914733015";
                unsafe { asm!(".byte 0xd7, 0x81, 0x20, 0x72") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_gt() {
    let input = quote! {
        fn ops_gt(a: U256, b: U256) -> bool {
            a > b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_gt(a: U256, b: U256) -> bool {
            a > b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_gt(a: U256, b: U256) -> bool {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            {
                let _ = "vmsltu.vv v3, v2, v1 - 1780515287";
                unsafe { asm!(".byte 0xd7, 0x81, 0x20, 0x6a") }
                let _ = "vfirst.m t0, v3 - 1111007959";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x38, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}
