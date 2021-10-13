use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub trait ToAsm {
    fn to_asm(&self) -> TokenStream;
}

// TODO: we need a better V instruction format that is used both here and CKB-VM.
// The type below is just for prototype simplicity, we need redesign for production.
pub enum RvvInst {
    Load256(u8, String),
    Store256(u8, String),
    // ## include: [*, *=, +, +=, -, -=, %, %=]
    // (vd, vs1, vs2)
    Mul256(u8, u8, u8),
    // (vd, vs1, vs2)
    Add256(u8, u8, u8),
    // (vd, vs1, vs2)
    Sub256(u8, u8, u8),
    // (vd, vs1, vs2)
    Rem256(u8, u8, u8),
    // (rd, vd, vs1, vs2)
    Ge256(u8, u8, u8, u8),
}

// TODO: right now this uses x86 instructions for easy of testing with
// std, in production we should change 2 parts:
// * Real V instruction format should be used.
impl ToAsm for RvvInst {
    #[cfg(not(feature = "simulator"))]
    fn to_asm(&self) -> TokenStream {
        match self {
            RvvInst::Load256(vreg, var_name) => {
                println!("[asm] load256 {}, {}", vreg, var_name);
                let var = format_ident!("{}", var_name);
                quote! {
                    unsafe {
                        asm!(
                            "mv t0, {0}",
                            // This should be vle256
                            ".byte 0x12, {1}, 0x34, 0x56",
                            in(reg) #var.to_le_bytes().as_ptr(),
                            const #vreg,
                            out("t0") _,
                        )
                    }
                }
            }
            RvvInst::Store256(vreg, var_name) => {
                println!("[asm] store256 {}, {}", vreg, var_name);
                let var = format_ident!("{}", var_name);
                quote! {
                      {
                            let mut buf = [0u8; 32];
                            unsafe {
                                  asm!(
                                        "mv t0, {0}",
                                        // This should be vse256
                                        ".byte 0x22, {1}, 0x34, 0x56",
                                        in(reg) buf.as_mut_ptr(),
                                        const #vreg,
                                        out("t0") _,
                                  )
                            };
                            #var = U256::from_le_bytes(&buf);
                      }
                }
            }
            RvvInst::Mul256(dvreg, svreg1, svreg2) => {
                println!("[asm] mul256 {}, {}, {}", dvreg, svreg1, svreg2);
                quote! {
                      unsafe {
                            asm!(
                                  // This should be vmul256
                                  ".byte 0x30, {0}, 0x34, {1}",
                                  const #dvreg,
                                  const ((#svreg1 << 4) | #svreg2),
                            )
                      }
                }
            }
            RvvInst::Add256(dvreg, svreg1, svreg2) => {
                println!("[asm] add256 {}, {}, {}", dvreg, svreg1, svreg2);
                quote! {
                    unsafe {
                        asm!(".byte 0x31, 0x33, 0x34, 0x35")
                    }
                }
            }
            RvvInst::Sub256(dvreg, svreg1, svreg2) => {
                println!("[asm] sub256 {}, {}, {}", dvreg, svreg1, svreg2);
                quote! {
                    unsafe {
                        asm!(".byte 0x32, 0x33, 0x34, 0x35")
                    }
                }
            }
            RvvInst::Rem256(dvreg, svreg1, svreg2) => {
                println!("[asm] rem256 {}, {}, {}", dvreg, svreg1, svreg2);
                quote! {
                    unsafe {
                        asm!(".byte 0x33, 0x33, 0x34, 0x35")
                    }
                }
            }
            RvvInst::Ge256(dxreg, dvreg, svreg1, svreg2) => {
                // FIXME: store result as bool or u256 ???
                println!("[asm] ge256 {}, {}, {}", dvreg, svreg1, svreg2);
                quote! {
                    unsafe {
                        asm!(".byte 0x34, 0x33, 0x34, 0x35")
                    }
                }
            }
        }
    }

    #[cfg(feature = "simulator")]
    fn to_asm(&self) -> TokenStream {
        match self {
            RvvInst::Load256(vreg, var_name) => {
                let var = format_ident!("{}", var_name);
                let var_numext = format_ident!("sim_u256_{}", vreg);
                println!("var: {:?}, var_numext: {:?}", var, var_numext);
                quote! {
                    let #var_numext = ethereum_types::U256::from_little_endian(&#var.to_le_bytes()[..]);
                }
            }
            RvvInst::Store256(vreg, var_name) => {
                let var = format_ident!("{}", var_name);
                let var_numext = format_ident!("sim_u256_{}", vreg);
                quote! {
                    let store = 0u32;
                }
            }
            RvvInst::Mul256(dvreg, svreg1, svreg2) => {
                quote! {
                    let mul = 1u32;
                }
            }
            RvvInst::Add256(dvreg, svreg1, svreg2) => {
                quote! {
                    let add = 2u32;
                }
            }
            RvvInst::Sub256(dvreg, svreg1, svreg2) => {
                quote! {
                    let sub = 3u32;
                }
            }
            RvvInst::Rem256(dvreg, svreg1, svreg2) => {
                quote! {
                    let rem = 4u32;
                }
            }
            RvvInst::Ge256(dxreg, dvreg, svreg1, svreg2) => {
                quote! {
                    let ge = 5u32;
                }
            }
        }
    }
}
