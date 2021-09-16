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
    Mul256(u8, u8, u8),
}

// TODO: right now this uses x86 instructions for easy of testing with
// std, in production we should change 2 parts:
// * rcx should be a RISC-V register, e.g. t0
// * Real V instruction format should be used.
impl ToAsm for RvvInst {
    fn to_asm(&self) -> TokenStream {
        match self {
            RvvInst::Load256(vreg, var_name) => {
                let var = format_ident!("{}", var_name);
                quote! {
                    unsafe {
                        asm!(
                            "mov rcx, {0}",
                            // This should be vle256
                            ".byte 0x12, {1}, 0x34, 0x56",
                            in(reg) #var.to_le_bytes().as_ptr(),
                            const #vreg,
                            out("rcx") _,
                        )
                    }
                }
            }
            RvvInst::Store256(vreg, var_name) => {
                let var = format_ident!("{}", var_name);
                quote! {
                      {
                            let mut buf = [0u8; 32];
                            unsafe {
                                  asm!(
                                        "mov rcx, {0}",
                                        // This should be vse256
                                        ".byte 0x22, {1}, 0x34, 0x56",
                                        in(reg) buf.as_mut_ptr(),
                                        const #vreg,
                                        out("rcx") _,
                                  )
                            };
                            #var = U256::from_le_bytes(&buf);
                      }
                }
            }
            RvvInst::Mul256(dvreg, svreg1, svreg2) => {
                quote! {
                      unsafe {
                            asm!(
                                  // This should be vmul256
                                  ".byte 0x32, {0}, 0x34, {1}",
                                  const #dvreg,
                                  const ((#svreg1 << 4) | #svreg2),
                            )
                      }
                }
            }
        }
    }
}
