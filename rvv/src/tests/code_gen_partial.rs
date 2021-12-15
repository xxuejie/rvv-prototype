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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vadd.vv v3, v1, v2 - 1114583";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 0u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input1, expected_output.clone());
    run_rvv_test(input2, expected_output);
}

#[test]
fn test_u256_ops_sub() {
    let input1 = quote! {
        fn ops_sub(a: U256, b: U256) -> U256 {
            a - b
        }
    };
    let input2 = quote! {
        fn ops_sub(a: U256, b: U256) -> U256 {
            a.wrapping_sub(b)
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_sub(a: U256, b: U256) -> U256 {
            a.wrapping_sub(b)
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_sub(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vsub.vv v3, v1, v2 - 135332311";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 8u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmul.vv v3, v1, v2 - 2484150743";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 17u8 , const 148u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vdivu.vv v3, v1, v2 - 2148606423";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 17u8 , const 128u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vremu.vv v3, v1, v2 - 2282824151";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 17u8 , const 136u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vxor.vv v3, v1, v2 - 739312087";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 44u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_bitand() {
    let input = quote! {
        fn ops_bitand(a: U256, b: U256) -> U256 {
            a & b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitand(a: U256, b: U256) -> U256 {
            a & b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitand(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vand.vv v3, v1, v2 - 605094359";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 36u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_bitor() {
    let input = quote! {
        fn ops_bitor(a: U256, b: U256) -> U256 {
            a | b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitor(a: U256, b: U256) -> U256 {
            a | b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitor(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vor.vv v3, v1, v2 - 672203223";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 40u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vsll.vv v3, v1, v2 - 2484142551";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 148u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
            }
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_shr() {
    let input = quote! {
        fn ops_shr(a: U256, b: U256) -> U256 {
            a >> b
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_shr(a: U256, b: U256) -> U256 {
            a >> b
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_shr(a: U256, b: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vsrl.vv v3, v1, v2 - 2685469143";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 160u8 ,)
                }
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vadd.vv v1, v1, v2 - 1114327";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 0u8 ,)
            };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_sub_assign() {
    let input = quote! {
        fn ops_sub_assign(mut a: U256, b: U256) {
            a -= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_sub_assign(mut a: U256, b: U256) {
            a = a.wrapping_sub(b);
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_sub_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vsub.vv v1, v1, v2 - 135332055";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 8u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vmul.vv v1, v1, v2 - 2484150487";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 32u8 , const 17u8 , const 148u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vdivu.vv v1, v1, v2 - 2148606167";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 32u8 , const 17u8 , const 128u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vremu.vv v1, v1, v2 - 2282823895";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 32u8 , const 17u8 , const 136u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vxor.vv v1, v1, v2 - 739311831";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 44u8 ,)
            };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_bitand_assign() {
    let input = quote! {
        fn ops_bitand_assign(mut a: U256, b: U256) {
            a &= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitand_assign(mut a: U256, b: U256) {
            a &= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitand_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vand.vv v1, v1, v2 - 605094103";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 36u8 ,)
            };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_bitor_assign() {
    let input = quote! {
        fn ops_bitor_assign(mut a: U256, b: U256) {
            a |= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_bitor_assign(mut a: U256, b: U256) {
            a |= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_bitor_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vor.vv v1, v1, v2 - 672202967";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 40u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vsll.vv v1, v1, v2 - 2484142295";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 148u8 ,)
            };
        }
    };
    run_rvv_test(input, expected_output);
}

#[test]
fn test_u256_ops_shr_assign() {
    let input = quote! {
        fn ops_shr_assign(mut a: U256, b: U256) {
            a >>= b;
        }
    };
    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn ops_shr_assign(mut a: U256, b: U256) {
            a >>= b;
        }
    };
    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn ops_shr_assign(mut a: U256, b: U256) {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vsrl.vv v1, v1, v2 - 2685468887";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 0u8 , const 17u8 , const 160u8 ,)
            };
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmseq.vv v3, v1, v2 - 1611727319";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 96u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmsltu.vv v3, v1, v2 - 1745945047";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 104u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmsleu.vv v3, v1, v2 - 1880162775";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 112u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmsne.vv v3, v1, v2 - 1678836183";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 100u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmsleu.vv v3, v2, v1 - 1881178583";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 129u8 , const 32u8 , const 112u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
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
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "vle256.v v1, (t0) - 268619911";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vle256.v v2, (t0) - 268620039";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            {
                let _ = "vmsltu.vv v3, v2, v1 - 1746960855";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 129u8 , const 32u8 , const 104u8 ,)
                }
                let _ = "vfirst.m t0, v3 - 1077453527";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 56u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            }
        }
    };
    run_rvv_test(input, expected_output);
}
