use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::HashSet;
use syn::{Expr, Stmt};

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

// TODO: right now this uses x86 instructions for easy of testing with
// std, in production we should change 2 parts:
// * Real V instruction format should be used.
impl ToStmts for RvvBlock {
    #[cfg(not(feature = "simulator"))]
    fn to_stmts(&self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        let mut buf_counter: u16 = 0;
        for inst in &self.insts {
            let token_stream = match inst {
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
                    let var_buf = format_ident!("buf_{}", buf_counter);
                    buf_counter += 1;
                    quote! {
                        let mut #var_buf = [0u8; 32];
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                // This should be vse256
                                ".byte 0x22, {1}, 0x34, 0x56",
                                in(reg) #var_buf.as_mut_ptr(),
                                const #vreg,
                                out("t0") _,
                            )
                        };
                        #var = U256::from_le_bytes(&#var_buf);
                        #var
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
                    println!("var: {:?}, var_numext: {:?}", var, var_numext);
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
                            let #var_numext_data: [u8; 32] = #var_numext.into();
                            #var = U256::from_le_bytes(&#var_numext_data);
                            #var
                        }
                    } else {
                        quote! {
                            let #var_numext_data: [u8; 32] = #var_numext.into();
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
