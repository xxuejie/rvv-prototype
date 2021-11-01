use quote::{format_ident, quote, ToTokens};
use syn::{Expr, Stmt};

#[cfg(feature = "simulator")]
use proc_macro2::Ident;
#[cfg(feature = "simulator")]
use std::collections::HashSet;

// FIXME: remove all allow later
#[allow(unused_variables)]
#[allow(dead_code)]
mod v_encoder;
#[allow(unused_imports)]
use v_encoder::{Imm, Ivi, Ivv, Ivx, Uimm, VInst, VReg, Vlmul, Vtypei, XReg};

pub trait ToStmts {
    fn to_stmts(&self) -> Vec<Stmt>;
}

// TODO: we need a better V instruction format that is used both here and CKB-VM.
// The type below is just for prototype simplicity, we need redesign for production.
#[derive(Clone, Eq, PartialEq)]
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
    // Keep the original normal statement
    Source(Stmt),
}

pub struct RvvBlock {
    insts: Vec<RvvInst>,
}

impl RvvBlock {
    pub fn new(insts: Vec<RvvInst>) -> RvvBlock {
        RvvBlock { insts }
    }
}

impl ToStmts for RvvBlock {
    #[cfg(not(feature = "simulator"))]
    fn to_stmts(&self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        let mut buf_counter: u16 = 0;
        let vsetvli_ts = {
            // vsetvli x0, t0, e256, m1, ta, ma
            let [b0, b1, b2, b3] = VInst::Vsetvli {
                rd: XReg::Zero,
                rs1: XReg::T0,
                vtypei: Vtypei::new(256, Vlmul::M1, true, true),
            }
            .encode_bytes();
            quote! {
                unsafe {
                    asm!(
                        "li t0, 1",  // AVL = 1
                        ".byte {0}, {1}, {2}, {3}",
                        const #b0, const #b1, const #b2, const #b3,
                    )
                }
            }
        };
        stmts.push(Stmt::Expr(Expr::Verbatim(vsetvli_ts)));
        for inst in &self.insts {
            let token_stream = match inst {
                RvvInst::Load256(vreg, var_name) => {
                    // println!("[asm] load256 {}, {}", vreg, var_name);
                    let var = format_ident!("{}", var_name);
                    // vle256.v v1, (t0)
                    let [b0, b1, b2, b3] = VInst::VleV {
                        width: 256,
                        vd: VReg::from_u8(*vreg),
                        rs1: XReg::T0,
                        vm: false,
                    }
                    .encode_bytes();
                    quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var.to_le_bytes().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    }
                }
                RvvInst::Store256(vreg, var_name) => {
                    // println!("[asm] store256 {}, {}", vreg, var_name);
                    let var = format_ident!("{}", var_name);
                    let var_buf = format_ident!("buf_{}", buf_counter);
                    buf_counter += 1;

                    let [b0, b1, b2, b3] = VInst::VseV {
                        width: 256,
                        vs3: VReg::from_u8(*vreg),
                        rs1: XReg::T0,
                        vm: false,
                    }
                    .encode_bytes();
                    quote! {
                        let mut #var_buf = [0u8; 32];
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                // This should be vse256
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_buf.as_mut_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        };

                        #var = U256::from_le_bytes(&#var_buf);
                        #var
                    }
                }
                RvvInst::Mul256(dvreg, svreg1, svreg2) => {
                    // println!("[asm] mul256 {}, {}, {}", dvreg, svreg1, svreg2);
                    let [b0, b1, b2, b3] = VInst::VmulVv(Ivv {
                        vd: VReg::from_u8(*dvreg),
                        vs2: VReg::from_u8(*svreg2),
                        vs1: VReg::from_u8(*svreg1),
                        vm: false,
                    })
                    .encode_bytes();
                    quote! {
                        unsafe {
                            asm!(
                                ".byte {0}, {1}, {2}, {3}",
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    }
                }
                RvvInst::Add256(dvreg, svreg1, svreg2) => {
                    // println!("[asm] add256 {}, {}, {}", dvreg, svreg1, svreg2);
                    let [b0, b1, b2, b3] = VInst::VaddVv(Ivv {
                        vd: VReg::from_u8(*dvreg),
                        vs2: VReg::from_u8(*svreg2),
                        vs1: VReg::from_u8(*svreg1),
                        vm: false,
                    })
                    .encode_bytes();
                    quote! {
                        unsafe {
                            asm!(
                                ".byte {0}, {1}, {2}, {3}",
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    }
                }
                RvvInst::Sub256(dvreg, svreg1, svreg2) => {
                    // println!("[asm] sub256 {}, {}, {}", dvreg, svreg1, svreg2);
                    let [b0, b1, b2, b3] = VInst::VsubVv(Ivv {
                        vd: VReg::from_u8(*dvreg),
                        vs2: VReg::from_u8(*svreg2),
                        vs1: VReg::from_u8(*svreg1),
                        vm: false,
                    })
                    .encode_bytes();
                    quote! {
                        unsafe {
                            asm!(
                                ".byte {0}, {1}, {2}, {3}",
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    }
                }
                RvvInst::Rem256(dvreg, svreg1, svreg2) => {
                    // println!("[asm] rem256 {}, {}, {}", dvreg, svreg1, svreg2);
                    let [b0, b1, b2, b3] = VInst::VremuVv(Ivv {
                        vd: VReg::from_u8(*dvreg),
                        vs2: VReg::from_u8(*svreg2),
                        vs1: VReg::from_u8(*svreg1),
                        vm: false,
                    })
                    .encode_bytes();
                    quote! {
                        unsafe {
                            asm!(
                                ".byte {0}, {1}, {2}, {3}",
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    }
                }
                RvvInst::Ge256(dxreg, dvreg, svreg1, svreg2) => {
                    // FIXME: store result as bool or u256 ???
                    // println!("[asm] ge256 {}, {}, {}, {}", dxreg, dvreg, svreg1, svreg2);
                    quote! {
                        unsafe {
                            asm!(".byte 0x34, 0x33, 0x34, 0x35")
                        }
                    }
                }
                RvvInst::Source(stmt) => stmt.to_token_stream(),
            };
            stmts.push(Stmt::Expr(Expr::Verbatim(token_stream)));
        }
        stmts
    }

    #[cfg(feature = "simulator")]
    fn to_stmts(&self) -> Vec<Stmt> {
        fn tmp_ident(reg: u8) -> Ident {
            format_ident!("sim_u256_{}", reg)
        }

        let mut stmts = Vec::new();
        let mut used_idents: HashSet<Ident> = HashSet::default();
        for inst in &self.insts {
            let token_stream = match inst {
                RvvInst::Load256(vreg, var_name) => {
                    let var = format_ident!("{}", var_name);
                    let var_numext = tmp_ident(*vreg);
                    used_idents.insert(var.clone());
                    used_idents.insert(var_numext.clone());
                    quote! {
                        let mut #var_numext = ethereum_types::U256::from_little_endian(&#var.to_le_bytes()[..]);
                    }
                }
                RvvInst::Store256(vreg, var_name) => {
                    let var = format_ident!("{}", var_name);
                    let var_numext = tmp_ident(*vreg);
                    let var_numext_data = format_ident!("sim_u256_data_{}", vreg);
                    if used_idents.contains(&var) {
                        quote! {
                            let mut #var_numext_data = [0u8; 32];
                            #var_numext.to_little_endian(&mut #var_numext_data);
                            #var = U256::from_le_bytes(&#var_numext_data);
                            #var
                        }
                    } else {
                        quote! {
                            let mut #var_numext_data = [0u8; 32];
                            #var_numext.to_little_endian(&mut #var_numext_data);
                            let #var = U256::from_le_bytes(&#var_numext_data);
                            #var
                        }
                    }
                }
                RvvInst::Mul256(dvreg, svreg1, svreg2) => {
                    let var_dst = tmp_ident(*dvreg);
                    let var_numext1 = tmp_ident(*svreg1);
                    let var_numext2 = tmp_ident(*svreg2);
                    if used_idents.contains(&var_dst) {
                        quote! {
                            #var_dst = #var_numext1.overflowing_mul(#var_numext2).0;
                        }
                    } else {
                        used_idents.insert(var_dst.clone());
                        quote! {
                            let (mut #var_dst, _) = #var_numext1.overflowing_mul(#var_numext2);
                        }
                    }
                }
                RvvInst::Add256(dvreg, svreg1, svreg2) => {
                    let var_dst = tmp_ident(*dvreg);
                    let var_numext1 = tmp_ident(*svreg1);
                    let var_numext2 = tmp_ident(*svreg2);
                    if used_idents.contains(&var_dst) {
                        quote! {
                            #var_dst = #var_numext1.overflowing_add(#var_numext2).0;
                        }
                    } else {
                        used_idents.insert(var_dst.clone());
                        quote! {
                            let (mut #var_dst, _) = #var_numext1.overflowing_add(#var_numext2);
                        }
                    }
                }
                RvvInst::Sub256(dvreg, svreg1, svreg2) => {
                    let var_dst = tmp_ident(*dvreg);
                    let var_numext1 = tmp_ident(*svreg1);
                    let var_numext2 = tmp_ident(*svreg2);
                    if used_idents.contains(&var_dst) {
                        quote! {
                            #var_dst = #var_numext1.overflowing_sub(#var_numext2).0;
                        }
                    } else {
                        used_idents.insert(var_dst.clone());
                        quote! {
                            let (mut #var_dst, _) = #var_numext1.overflowing_sub(#var_numext2);
                        }
                    }
                }
                RvvInst::Rem256(dvreg, svreg1, svreg2) => {
                    let var_dst = tmp_ident(*dvreg);
                    let var_numext1 = tmp_ident(*svreg1);
                    let var_numext2 = tmp_ident(*svreg2);
                    if used_idents.contains(&var_dst) {
                        quote! {
                            #var_dst = #var_numext1 % #var_numext2;
                        }
                    } else {
                        used_idents.insert(var_dst.clone());
                        quote! {
                            let mut #var_dst = #var_numext1 % #var_numext2;
                        }
                    }
                }
                RvvInst::Ge256(dxreg, dvreg, svreg1, svreg2) => {
                    quote! {
                        let ge = 5u32;
                    }
                }
                RvvInst::Source(stmt) => stmt.to_token_stream(),
            };
            stmts.push(Stmt::Expr(Expr::Verbatim(token_stream)));
        }
        stmts
    }
}
