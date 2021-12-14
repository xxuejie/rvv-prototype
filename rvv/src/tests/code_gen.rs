use quote::quote;

use super::rvv_test;

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
    let output = rvv_test(input, false).unwrap();
    let output_string = output.to_string();
    println!("[otuput]: {}", output_string);
    assert_eq!(input_string, output_string);
}

#[test]
fn test_u256() {
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
    let output = rvv_test(input, true).unwrap();
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
            let _ = "li t0, 1";
            let _ = "243462231 - vsetvl zero, t0, e256, m1, ta, ma";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
            }
            let _ = "268619911 - vle256.v v1, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268620039 - vle256.v v2, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) y . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268620167 - vle256.v v3, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) z . as_ref () . as_ptr () , const 135u8 , const 209u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268620295 - vle256.v v4, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) w . as_ref () . as_ptr () , const 7u8 , const 210u8 , const 2u8 , const 16u8 ,)
            }
            let x_bytes = x.to_le_bytes();
            let j = {
                let _ = "vmul.vv v5, v3, v2 - 2486248151";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 34u8 , const 49u8 , const 148u8 ,)
                }
                let _ = "vdivu.vv v6, v5, v4 - 2152866647";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 35u8 , const 82u8 , const 128u8 ,)
                }
                let _ = "vadd.vv v4, v1, v6 - 1245783";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 2u8 , const 19u8 , const 0u8 ,)
                }
                let _ = "vse256.v v4, (t0) - 268620327";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 210u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
            };
            if {
                let _ = "vmsgtu.vv v4, v1, v2 - 1746960983";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 130u8 , const 32u8 , const 104u8 ,)
                }
                let _ = "vfirst.m t0, v4 - 1078502103";
                let _ = "mv {tmp_bool_t0}, t0";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 72u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            } && {
                let _ = "vmseq.vv v4, v2, v3 - 1612808791";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 130u8 , const 33u8 , const 96u8 ,)
                }
                let _ = "vfirst.m t0, v4 - 1078502103";
                let _ = "mv {tmp_bool_t0}, t0";
                let tmp_bool_t0: i64;
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 72u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
                }
                tmp_bool_t0 == 0
            } {
                let _ = "vor.vv v4, v3, v2 - 674300503";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 2u8 , const 49u8 , const 40u8 ,)
                }
                let _ = "vand.vv v3, v1, v4 - 605159895";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 18u8 , const 36u8 ,)
                };
            }
            let _ = "vsub.vv v4, v1, v2 - 135332439";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 2u8 , const 17u8 , const 8u8 ,)
            }
            let _ = "vmul.vv v3, v4, v1 - 2487263703";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 161u8 , const 64u8 , const 148u8 ,)
            };
            let abc = 3456;
            let _ = "268620295 - vle256.v v4, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) j . as_ref () . as_ptr () , const 7u8 , const 210u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vsub.vv v5, v2, v1 - 136348375";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 130u8 , const 32u8 , const 8u8 ,)
            }
            let _ = "vmul.vv v1, v4, v5 - 2487394519";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 160u8 , const 66u8 , const 148u8 ,)
            }
            let _ = "vadd.vv v3, v2, v1 - 2130391";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 129u8 , const 32u8 , const 0u8 ,)
            };
            let _ = "vadd.vv v3, v3, v3 - 3244503";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 129u8 , const 49u8 , const 0u8 ,)
            };
            let _ = "vsub.vv v3, v3, v2 - 137429463";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 49u8 , const 8u8 ,)
            };
            let _ = "vmul.vv v3, v3, v2 - 2486247895";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 49u8 , const 148u8 ,)
            };
            let _ = "vadd.vv v3, v3, v2 - 3211735";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 49u8 , const 0u8 ,)
            };
            let _ = "vremu.vv v3, v3, v2 - 2284921303";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 49u8 , const 136u8 ,)
            };
            let _ = "vsrl.vv v3, v3, v2 - 2687566295";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 49u8 , const 160u8 ,)
            };
            let zero = U256::zero();
            let _ = "268619911 - vle256.v v1, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) zero . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "vdivu.vv v3, v3, v1 - 2150670807";
            unsafe {
                asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 161u8 , const 48u8 , const 128u8 ,)
            };
            {
                let _ = "vse256.v v3, (t0) - 268620199";
                let mut tmp_rvv_vector_buf = [0u8; 32usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 209u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
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
    let output = rvv_test(input, true).unwrap();
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
            let _ = "li t0, 1";
            let _ = "260239447 - vsetvl zero, t0, e1024, m1, ta, ma";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 15u8 ,)
            }
            let _ = "268628103 - vle1024.v v1, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 135u8 , const 240u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268628231 - vle1024.v v2, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) y . as_ref () . as_ptr () , const 7u8 , const 241u8 , const 2u8 , const 16u8 ,)
            }
            let z = {
                let _ = "vadd.vv v3, v1, v2 - 1114583";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 1u8 , const 17u8 , const 0u8 ,)
                }
                let _ = "vmul.vv v2, v3, v1 - 2486214999";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 161u8 , const 48u8 , const 148u8 ,)
                }
                let _ = "vse1024.v v2, (t0) - 268628263";
                let mut tmp_rvv_vector_buf = [0u8; 128usize];
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 241u8 , const 2u8 , const 16u8 ,)
                }
                unsafe { core::mem::transmute::<[u8; 128usize], U1024>(tmp_rvv_vector_buf) }
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
    let output = rvv_test(input, true).unwrap();
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
            let _ = "li t0, 1";
            let _ = "260239447 - vsetvl zero, t0, e1024, m1, ta, ma";
            unsafe {
                asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 15u8 ,)
            }
            let _ = "268628103 - vle1024.v v1, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 135u8 , const 240u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268628231 - vle1024.v v2, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 7u8 , const 241u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268628359 - vle1024.v v3, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) c . as_ref () . as_ptr () , const 135u8 , const 241u8 , const 2u8 , const 16u8 ,)
            }
            let _ = "268628487 - vle1024.v v4, (t0)";
            unsafe {
                asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) d . as_ref () . as_ptr () , const 7u8 , const 242u8 , const 2u8 , const 16u8 ,)
            }
            let x_tuple = {
                let _ = "vadd.vv v5, v1, v2 - 1114839";
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 2u8 , const 17u8 , const 0u8 ,)
                }
                {
                    let _ = "vmul.vv v1, v5, v3 - 2488377559";
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 160u8 , const 81u8 , const 148u8 ,)
                    }
                    let _ = "vmsne.vi v2, v1, 0 - 1678782807";
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 49u8 , const 16u8 , const 100u8 ,)
                    }
                    let _ = "vfirst.m t0, v2 - 1076404951";
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 162u8 , const 40u8 , const 64u8 ,)
                    }
                    let _ = "mv {tmp_bool_t0}, t0";
                    let _ = "mv t2, {tmp_rvv_vector_buf}";
                    let _ = "268693671 - vse1024.v v1, (t2)";
                    let tmp_bool_t0: i64;
                    let mut tmp_rvv_vector_buf = [0u8; 128usize];
                    unsafe {
                        asm ! ("mv {0}, t0" , "mv t2, {1}" , ".byte {2}, {3}, {4}, {5}" , out (reg) tmp_bool_t0 , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 240u8 , const 3u8 , const 16u8 ,)
                    }
                    let tmp_uint_rv =
                        unsafe { core::mem::transmute::<[u8; 128usize], U1024>(tmp_rvv_vector_buf) };
                    let _ = "2148704599 - vdivu.vv v2, v1, v5";
                    let _ = "1679917399 - vmsne.vv v2, v2, v3";
                    let _ = "1076405079 - vfirst.m t1, v2";
                    let _ = "mv {tmp_bool_t1}, t1";
                    if tmp_bool_t0 == 0 {
                        let tmp_bool_t1: i64;
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , ".byte {4}, {5}, {6}, {7}" , ".byte {8}, {9}, {10}, {11}" , "mv {12}, t1" , const 87u8 , const 161u8 , const 18u8 , const 128u8 , const 87u8 , const 129u8 , const 33u8 , const 100u8 , const 87u8 , const 163u8 , const 40u8 , const 64u8 , out (reg) tmp_bool_t1 ,)
                        }
                        (tmp_uint_rv, tmp_bool_t1 == 0)
                    } else {
                        (tmp_uint_rv, false)
                    }
                }
            };
            let x = x_tuple.0;
            let z_opt = {
                let _ = "268628359 - vle1024.v v3, (t0)";
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 135u8 , const 241u8 , const 2u8 , const 16u8 ,)
                }
                {
                    let _ = "vmseq.vi v6, v4, 0 - 1614820183";
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 51u8 , const 64u8 , const 96u8 ,)
                    }
                    let _ = "vfirst.m t0, v6 - 1080599255";
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 162u8 , const 104u8 , const 64u8 ,)
                    }
                    let _ = "mv {tmp_bool_var}, t0";
                    let _ = "2150769367 - vdivu.vv v5, v3, v4";
                    let _ = "mv t1, {tmp_rvv_vector_buf}";
                    let _ = "268661415 - vse1024.v v5, (t1)";
                    let tmp_bool_var: i64;
                    unsafe { asm ! ("mv {0}, t0" , out (reg) tmp_bool_var ,) }
                    if tmp_bool_var == 0 {
                        None
                    } else {
                        let mut tmp_rvv_vector_buf = [0u8; 128usize];
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , "mv t1, {4}" , ".byte {5}, {6}, {7}, {8}" , const 215u8 , const 34u8 , const 50u8 , const 128u8 , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 114u8 , const 3u8 , const 16u8 ,)
                        }
                        Some(unsafe { core::mem::transmute::<[u8; 128usize], U1024>(tmp_rvv_vector_buf) })
                    }
                }
            };
            let z: U1024 = z.unwrap();
            z
        }
    };
    assert_eq!(output.to_string(), expected_output.to_string());
}
