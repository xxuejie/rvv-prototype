use quote::quote;

use super::rvv_codegen;

#[test]
fn test_simple() {
    let input = quote! {
        fn simple(x: u32, mut y: u64, z: &mut u64, w: u16) -> u128 {
            let qqq: bool = false;
            let jjj: () = {
                y += 3;
            };
            *z += 3;
            if z > 5 {
                y = y * 6;
            } else {
                y = y * 3;
            }
            y = (y >> 1) + 3;
            for i in 0..6u32 {
                if i == 3 {
                    continue;
                }
                z += 1;
                if z > 6 {
                    break;
                }
            }
            let rv = if z > 6 {
                (x as u64) + y + *z
            } else {
                (x as u64) * y + *z
            };
            (rv + 3) as u128
        }
    };
    let input_string = input.to_string();
    println!("[input ]: {}", input_string);
    let output = rvv_codegen(input, false).unwrap();
    let output_string = output.to_string();
    println!("[otuput]: {}", output_string);
    assert_eq!(input_string, output_string);
}

#[test]
fn test_u256_mixed() {
    let input = quote! {
        fn comp_u256(x: U256, y: U256, mut z: U256, w: U256) -> U256 {
            let x_bytes = x.to_le_bytes();
            let j = x + (z * y / w);
            if x > y && y == z {
                z = x & (z | y);
            }
            z = (x - y) * x;
            let abc = 3456;
            z = (y + j * (y - x));
            z = z + z;
            z -= y;
            z *= y;
            z += y;
            z %= y;
            z >>= y;
            let zero = U256::zero();
            z /= zero;
            z
        }
    };
    println!("[input ]: {}", input);
    let output = rvv_codegen(input, true).unwrap();
    println!("[otuput]: {}", output);

    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn comp_u256(x: U256, y: U256, mut z: U256, w: U256) -> U256 {
            let x_bytes = x.to_le_bytes();
            let j = x.wrapping_add(
                (z.wrapping_mul(y)
                 .checked_div(w)
                 .unwrap_or_else(|| U256::max_value())));
            if x > y && y == z {
                z = x & (z | y);
            }
            z = (x.wrapping_sub(y)).wrapping_mul(x);
            let abc = 3456;
            z = (y.wrapping_add(j.wrapping_mul((y.wrapping_sub(x)))));
            z = z.wrapping_add(z);
            z = z.wrapping_sub(y);
            z = z.wrapping_mul(y);
            z = z.wrapping_add(y);
            z %= y;
            z >>= y;
            let zero = U256::zero();
            z = z.checked_div(zero).unwrap_or_else(|| U256::max_value());
            z
        }
    };

    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn comp_u256(x: U256, y: U256, mut z: U256, w: U256) -> U256 {
            let _ = "vsetvl zero, t0, e256, m1, ta, ma - 243462231";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0e",) }
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) x . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v2, (t0) - 302174471";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) y . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v3, (t0) - 302174599";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) z . as_ref () . as_ptr () ,)
            }
            let _ = "vle256.v v4, (t0) - 302174727";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd2, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) w . as_ref () . as_ptr () ,)
            }
            let x_bytes = x.to_le_bytes();
            let j = {
                let _ = "vmul.vv v5, v3, v2 - 2519802583";
                unsafe { asm!(".byte 0xd7, 0x22, 0x31, 0x96") }
                let _ = "vdivu.vv v6, v5, v4 - 2186421079";
                unsafe { asm!(".byte 0x57, 0x23, 0x52, 0x82") }
                let _ = "vadd.vv v4, v1, v6 - 34800215";
                unsafe { asm!(".byte 0x57, 0x02, 0x13, 0x02") }
                let _ = "vse256.v v4, (t0) - 302174759";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 32usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x27, 0xd2, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U256>(tmp_rvv_vector_buf) }
            };
            if {
                let _ = "vmsltu.vv v4, v2, v1 - 1780515415";
                unsafe { asm!(".byte 0x57, 0x82, 0x20, 0x6a") }
                let _ = "vfirst.m t0, v4 - 1112056535";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x48, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            } && {
                let _ = "vmseq.vv v4, v2, v3 - 1646363223";
                unsafe { asm!(".byte 0x57, 0x82, 0x21, 0x62") }
                let _ = "vfirst.m t0, v4 - 1112056535";
                let _tmp_t0_saved: i64;
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa2, 0x48, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            } {
                let _ = "vor.vv v4, v3, v2 - 707854935";
                unsafe { asm!(".byte 0x57, 0x02, 0x31, 0x2a") }
                let _ = "vand.vv v3, v1, v4 - 638714327";
                unsafe { asm!(".byte 0xd7, 0x01, 0x12, 0x26") };
            }
            let _ = "vsub.vv v4, v1, v2 - 168886871";
            unsafe { asm!(".byte 0x57, 0x02, 0x11, 0x0a") }
            let _ = "vmul.vv v3, v4, v1 - 2520818135";
            unsafe { asm!(".byte 0xd7, 0xa1, 0x40, 0x96") };
            let abc = 3456;
            let _ = "vle256.v v4, (t0) - 302174727";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xd2, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) j . as_ref () . as_ptr () ,)
            }
            let _ = "vsub.vv v5, v2, v1 - 169902807";
            unsafe { asm!(".byte 0xd7, 0x82, 0x20, 0x0a") }
            let _ = "vmul.vv v1, v4, v5 - 2520948951";
            unsafe { asm!(".byte 0xd7, 0xa0, 0x42, 0x96") }
            let _ = "vadd.vv v3, v2, v1 - 35684823";
            unsafe { asm!(".byte 0xd7, 0x81, 0x20, 0x02") };
            let _ = "vadd.vv v3, v3, v3 - 36798935";
            unsafe { asm!(".byte 0xd7, 0x81, 0x31, 0x02") };
            let _ = "vsub.vv v3, v3, v2 - 170983895";
            unsafe { asm!(".byte 0xd7, 0x01, 0x31, 0x0a") };
            let _ = "vmul.vv v3, v3, v2 - 2519802327";
            unsafe { asm!(".byte 0xd7, 0x21, 0x31, 0x96") };
            let _ = "vadd.vv v3, v3, v2 - 36766167";
            unsafe { asm!(".byte 0xd7, 0x01, 0x31, 0x02") };
            let _ = "vremu.vv v3, v3, v2 - 2318475735";
            unsafe { asm!(".byte 0xd7, 0x21, 0x31, 0x8a") };
            let _ = "vsrl.vv v3, v3, v2 - 2721120727";
            unsafe { asm!(".byte 0xd7, 0x01, 0x31, 0xa2") };
            let zero = U256::zero();
            let _ = "vle256.v v1, (t0) - 302174343";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xd0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) zero . as_ref () . as_ptr () ,)
            }
            let _ = "vdivu.vv v3, v3, v1 - 2184225239";
            unsafe { asm!(".byte 0xd7, 0xa1, 0x30, 0x82") };
            {
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
    assert_eq!(output.to_string(), expected_output.to_string());
}

#[test]
fn test_u1024() {
    let input = quote! {
        #[inline(always)]
        #[no_mangle]
        fn comp_u1024(x: U1024, y: U1024) -> U1024 {
            let z = (x + y) * x;
            z
        }
    };
    println!("[input ]: {}", input);
    let output = rvv_codegen(input, true).unwrap();
    println!("[otuput]: {}", output);

    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        #[inline(always)]
        #[no_mangle]
        fn comp_u1024(x: U1024, y: U1024) -> U1024 {
            let z = (x.wrapping_add(y)).wrapping_mul(x);
            z
        }
    };

    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        #[inline(always)]
        #[no_mangle]
        fn comp_u1024(x: U1024, y: U1024) -> U1024 {
            let _ = "vsetvl zero, t0, e1024, m1, ta, ma - 260239447";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0f",) }
            let _ = "vle1024.v v1, (t0) - 302182535";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xf0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) x . as_ref () . as_ptr () ,)
            }
            let _ = "vle1024.v v2, (t0) - 302182663";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xf1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) y . as_ref () . as_ptr () ,)
            }
            let z = {
                let _ = "vadd.vv v3, v1, v2 - 34669015";
                unsafe { asm!(".byte 0xd7, 0x01, 0x11, 0x02") }
                let _ = "vmul.vv v2, v3, v1 - 2519769431";
                unsafe { asm!(".byte 0x57, 0xa1, 0x30, 0x96") }
                let _ = "vse1024.v v2, (t0) - 302182695";
                let _tmp_t0_saved: i64;
                let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 128usize]> =
                    core::mem::MaybeUninit::uninit();
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x27, 0xf1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                }
                unsafe { core::mem::transmute::<_, U1024>(tmp_rvv_vector_buf) }
            };
            z
        }
    };
    assert_eq!(output.to_string(), expected_output.to_string());
}

#[test]
fn test_method_call() {
    let input = quote! {
        fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
            let x_tuple = a.wrapping_add(b).overflowing_mul(c);
            let x = x_tuple.0;
            let z_opt = x.checked_div(d);
            let z: U1024 = z.unwrap();
            // let z = x.overflowing_add(y);
            // let z = x.checked_add(y).unwrap();
            // let z = x.saturating_add(y);
            z
        }
    };
    println!("[input ]: {}", input);
    let output = rvv_codegen(input, true).unwrap();
    println!("[otuput]: {}", output);

    #[cfg(feature = "simulator")]
    let expected_output = quote! {
        fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
            let x_tuple = a.wrapping_add(b).overflowing_mul(c);
            let x = x_tuple.0 ;
            let z_opt = x.checked_div(d) ;
            let z : U1024 = z.unwrap() ;
            z
        }
    };

    #[cfg(not(feature = "simulator"))]
    let expected_output = quote! {
        fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
            let _ = "vsetvl zero, t0, e1024, m1, ta, ma - 260239447";
            unsafe { asm!("li t0, 1", ".byte 0x57, 0xf0, 0x82, 0x0f",) }
            let _ = "vle1024.v v1, (t0) - 302182535";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xf0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) a . as_ref () . as_ptr () ,)
            }
            let _ = "vle1024.v v2, (t0) - 302182663";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xf1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) b . as_ref () . as_ptr () ,)
            }
            let _ = "vle1024.v v3, (t0) - 302182791";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xf1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) c . as_ref () . as_ptr () ,)
            }
            let _ = "vle1024.v v4, (t0) - 302182919";
            let _tmp_t0_saved: i64;
            unsafe {
                asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x07, 0xf2, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) d . as_ref () . as_ptr () ,)
            }
            let x_tuple = {
                let _ = "vadd.vv v5, v1, v2 - 34669271";
                unsafe { asm!(".byte 0xd7, 0x02, 0x11, 0x02") }
                {
                    let _ = "vmul.vv v1, v5, v3 - 2521931991";
                    let _ = "vmsne.vi v2, v1, 0 - 1712337239";
                    let _ = "vfirst.m t0, v2 - 1109959383";
                    let _ = "vse1024.v v1, (t0) - 302182567";
                    let mut _tmp_t0_saved: i64;
                    let mut tmp_bool_t0: i64;
                    let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 128usize]> =
                        core::mem::MaybeUninit::uninit();
                    unsafe {
                        asm ! ("mv {0}, t0" , ".byte 0xd7, 0xa0, 0x51, 0x96" , ".byte 0x57, 0x31, 0x10, 0x66" , ".byte 0xd7, 0xa2, 0x28, 0x42" , "mv {1}, t0" , "mv t0, {2}" , ".byte 0xa7, 0xf0, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                    }
                    let tmp_uint_rv = unsafe { core::mem::transmute::<_, U1024>(tmp_rvv_vector_buf) };
                    let _ = "vdivu.vv v2, v1, v5 - 2182259031";
                    let _ = "vmsne.vv v2, v2, v3 - 1713471831";
                    let _ = "vfirst.m t0, v2 - 1109959383";
                    if tmp_bool_t0 == 0 {
                        unsafe {
                            asm ! ("mv {0}, t0" , ".byte 0x57, 0xa1, 0x12, 0x82" , ".byte 0x57, 0x81, 0x21, 0x66" , ".byte 0xd7, 0xa2, 0x28, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                        }
                        (tmp_uint_rv, tmp_bool_t0 == 0)
                    } else {
                        (tmp_uint_rv, false)
                    }
                }
            };
            let x = x_tuple.0;
            let z_opt = {
                let _ = "vle1024.v v3, (t0) - 302182791";
                let _tmp_t0_saved: i64;
                unsafe {
                    asm ! ("mv {0}, t0" , "mv t0, {1}" , ".byte 0x87, 0xf1, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) x . as_ref () . as_ptr () ,)
                }
                {
                    let _ = "vmseq.vi v6, v4, 0 - 1648374615";
                    let _ = "vfirst.m t0, v6 - 1114153687";
                    let _ = "vdivu.vv v5, v3, v4 - 2184323799";
                    let _ = "vse1024.v v5, (t0) - 302183079";
                    let mut _tmp_t0_saved: i64;
                    let tmp_bool_t0: i64;
                    unsafe {
                        asm ! ("mv {0}, t0" , ".byte 0x57, 0x33, 0x40, 0x62" , ".byte 0xd7, 0xa2, 0x68, 0x42" , "mv {1}, t0" , "mv t0, {0}" , out (reg) _tmp_t0_saved , out (reg) tmp_bool_t0 ,)
                    }
                    if tmp_bool_t0 == 0 {
                        None
                    } else {
                        let mut tmp_rvv_vector_buf: core::mem::MaybeUninit<[u8; 128usize]> =
                            core::mem::MaybeUninit::uninit();
                        unsafe {
                            asm ! ("mv {0}, t0" , ".byte 0xd7, 0x22, 0x32, 0x82" , "mv t0, {1}" , ".byte 0xa7, 0xf2, 0x02, 0x12" , "mv t0, {0}" , out (reg) _tmp_t0_saved , in (reg) tmp_rvv_vector_buf . as_mut_ptr () ,)
                        }
                        Some(unsafe { core::mem::transmute::<_, U1024>(tmp_rvv_vector_buf) })
                    }
                }
            };
            let z: U1024 = z.unwrap();
            z
        }
    };
    assert_eq!(output.to_string(), expected_output.to_string());
}
