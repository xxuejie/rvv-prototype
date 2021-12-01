use std::collections::HashMap;

use anyhow::anyhow;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::token;

#[cfg(not(feature = "simulator"))]
use rvv_assembler::{Imm, Ivi, Ivv, VConfig, VInst, VReg, Vlmul, Vtypei, XReg};

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Span, Statement,
    Type, TypedExpression, WithSpan,
};
use crate::SpannedError;

// =============================
// ==== impl ToTokens for T ====
// =============================

#[derive(Default)]
pub struct Registers {
    pub category: &'static str,
    pub max_number: u8,
    pub last_number: u8,
}

impl Registers {
    pub fn new(category: &'static str, max_number: u8) -> Registers {
        Registers {
            category,
            max_number,
            last_number: 0,
        }
    }

    pub fn next_register(&mut self) -> Option<u8> {
        if self.last_number < self.max_number {
            let value = self.last_number;
            self.last_number += 1;
            return Some(value);
        }
        None
    }
}

enum OpCategory {
    //   vd = vrs1 op vrs2
    Binary,
    // bool = vrs1 op vrs2
    Bool,
    // vrs1 = vrs1 op vrs2
    AssignOp,
}

impl From<&syn::BinOp> for OpCategory {
    fn from(op: &syn::BinOp) -> OpCategory {
        match op {
            syn::BinOp::Add(_)
            | syn::BinOp::Sub(_)
            | syn::BinOp::Mul(_)
            | syn::BinOp::Div(_)
            | syn::BinOp::Rem(_)
            | syn::BinOp::BitXor(_)
            | syn::BinOp::BitAnd(_)
            | syn::BinOp::BitOr(_)
            | syn::BinOp::Shl(_)
            | syn::BinOp::Shr(_) => OpCategory::Binary,
            syn::BinOp::And(_) | syn::BinOp::Or(_) => unreachable!(),
            syn::BinOp::Eq(_)
            | syn::BinOp::Lt(_)
            | syn::BinOp::Le(_)
            | syn::BinOp::Ne(_)
            | syn::BinOp::Ge(_)
            | syn::BinOp::Gt(_) => OpCategory::Bool,
            syn::BinOp::AddEq(_)
            | syn::BinOp::SubEq(_)
            | syn::BinOp::MulEq(_)
            | syn::BinOp::DivEq(_)
            | syn::BinOp::RemEq(_)
            | syn::BinOp::BitXorEq(_)
            | syn::BinOp::BitAndEq(_)
            | syn::BinOp::BitOrEq(_)
            | syn::BinOp::ShlEq(_)
            | syn::BinOp::ShrEq(_) => OpCategory::AssignOp,
        }
    }
}

#[cfg(not(feature = "simulator"))]
fn inst_codegen(tokens: &mut TokenStream, inst: VInst, show_asm: bool) {
    let [b0, b1, b2, b3] = inst.encode_bytes();
    if show_asm {
        let comment = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment;
        }));
    }
    let ts = quote! {
        unsafe {
            asm!(".byte {0}, {1}, {2}, {3}", const #b0, const #b1, const #b2, const #b3,)
        }
    };
    tokens.extend(Some(ts));
}

#[cfg(not(feature = "simulator"))]
fn overflowing_rv_codegen(tokens: &mut TokenStream, vreg: VReg, bit_length: u16, show_asm: bool) {
    let inst = VInst::VseV {
        width: bit_length,
        vs3: vreg,
        rs1: XReg::T1,
        vm: false,
    };
    if show_asm {
        let comment = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment;
        }));
    }
    let [b0, b1, b2, b3] = inst.encode_bytes();

    let uint_type = quote::format_ident!("U{}", bit_length);
    let buf_length = bit_length as usize / 8;
    tokens.extend(Some(quote! {
        let tmp_bool_var: i64;
        let mut tmp_rvv_vector_buf = [0u8; #buf_length];
        // t0: 0  (vms* success)
        // t0: -1 (not found)
        unsafe {
            asm!(
                "mv {0} t0",
                "mv t1, {1}",
                ".byte {2}, {3}, {4}, {5}",
                out(reg) tmp_bool_var,
                in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                const #b0, const #b1, const #b2, const #b3,
            )
        }
        (unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }, tmp_bool_var == 0)
    }));
}

#[cfg(not(feature = "simulator"))]
fn checked_rv_codegen(tokens: &mut TokenStream, vreg: VReg, bit_length: u16, show_asm: bool) {
    let inst = VInst::VseV {
        width: bit_length,
        vs3: vreg,
        rs1: XReg::T1,
        vm: false,
    };
    if show_asm {
        let comment = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment;
        }));
    }
    let [b0, b1, b2, b3] = inst.encode_bytes();

    let uint_type = quote::format_ident!("U{}", bit_length);
    let buf_length = bit_length as usize / 8;
    tokens.extend(Some(quote! {
        let tmp_bool_var: i64;
        // t0: 0  (vms* success)
        // t0: -1 (not found)
        unsafe {
            asm!(
                "mv {0} t0",
                out(reg) tmp_bool_var,
            )
        }
        if tmp_bool_var == 0 {
            None
        } else {
            let mut tmp_rvv_vector_buf = [0u8; #buf_length];
            unsafe {
                asm!(
                    "mv t1, {0}",
                    ".byte {1}, {2}, {3}, {4}",
                    in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                    const #b0, const #b1, const #b2, const #b3,
                )
            }
            Some(unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) })
        }
    }));
}

#[derive(Default)]
pub struct CodegenContext {
    // vector registers
    v_registers: Registers,
    // general registers
    _x_registers: Registers,

    // FIXME: handle varable scope
    // var_name => register_number
    var_regs: HashMap<syn::Ident, u8>,
    // expr_id => (register_number, bit_length)
    expr_regs: HashMap<usize, (u8, u16)>,

    // expr_id => (var_name, bit_length)
    #[cfg(feature = "simulator")]
    expr_tokens: HashMap<usize, (TokenStream, u16)>,

    // FIXME: fill in current module
    // ident => (mutability, Type)
    _variables: HashMap<syn::Ident, (Option<Span>, Box<WithSpan<Type>>)>,

    // [When update v_config]
    //   1. When first vector instruction used update v_config and insert asm!()
    //   2. When vector config changed:
    //     * reset x_registers
    //     * dump all x register data to memory
    //     * update v_config and insert asm!()
    #[cfg(not(feature = "simulator"))]
    v_config: Option<VConfig>,

    // Add original asm to generated code
    #[allow(dead_code)]
    show_asm: bool,
}

impl CodegenContext {
    pub fn new(
        variables: HashMap<syn::Ident, (Option<Span>, Box<WithSpan<Type>>)>,
        show_asm: bool,
    ) -> CodegenContext {
        CodegenContext {
            v_registers: Registers::new("vector", 32),
            _x_registers: Registers::new("general", 32),
            var_regs: HashMap::default(),
            expr_regs: HashMap::default(),
            #[cfg(feature = "simulator")]
            expr_tokens: HashMap::default(),
            _variables: variables,
            #[cfg(not(feature = "simulator"))]
            v_config: None,
            show_asm,
        }
    }

    #[cfg(feature = "simulator")]
    fn gen_tokens(
        &mut self,
        expr: &TypedExpression,
        top_level: bool,
        extra_bind_id: Option<usize>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        let (left, op, right, is_assign) = match &expr.expr.0 {
            Expression::AssignOp { left, op, right } => (left, op, right, true),
            Expression::Binary { left, op, right } => (left, op, right, false),
            Expression::MethodCall { receiver, method, args, .. } => {
                return self.default_method_call_codegen(receiver, method, args);
            }
            Expression::Paren { expr: sub_expr, .. } => {
                let ts = self.gen_tokens(&*sub_expr, top_level, Some(expr.id), bit_length)?;
                return Ok(quote! {(#ts)});
            }
            _  => return Err((expr.expr.1, anyhow!("invalid expression, inner expression must be simple variable name or binary op"))),
        };
        if !top_level && is_assign {
            return Err((
                expr.expr.1,
                anyhow!("assign op in sub-expression is forbidden"),
            ));
        }

        let mut tokens = TokenStream::new();

        if top_level {
            let left_type_name = left.type_name();
            let right_type_name = right.type_name();
            match (left_type_name.as_deref(), right_type_name.as_deref()) {
                (Some("U256"), Some("U256")) => {
                    bit_length = 256;
                }
                (Some("U512"), Some("U512")) => {
                    bit_length = 512;
                }
                (Some("U1024"), Some("U1024")) => {
                    bit_length = 1024;
                }
                _ => {
                    left.to_tokens(&mut tokens, self)?;
                    op.to_tokens(&mut tokens);
                    right.to_tokens(&mut tokens, self)?;
                    return Ok(tokens);
                }
            };
        }

        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(typed_expr.id, (*vreg, bit_length));
                } else {
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, (vreg, bit_length));
                }
                self.expr_tokens
                    .insert(typed_expr.id, (quote! {#var_ident}, bit_length));
            } else {
                let _ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
            }
        }

        let op_category = OpCategory::from(op);
        let (expr1, bit_len1) = self.expr_tokens.get(&left.id).cloned().unwrap();
        let (expr2, bit_len2) = self.expr_tokens.get(&right.id).cloned().unwrap();
        if bit_len1 != bit_len2 {
            return Err((
                expr.expr.1,
                anyhow!(
                    "bit length not matched, left: {}, right: {}",
                    bit_len1,
                    bit_len2
                ),
            ));
        }
        // FIXME: handle OpCategory::Bool
        if let OpCategory::Binary = op_category {
            let dvreg = self.v_registers.next_register().ok_or_else(|| {
                (
                    expr.expr.1,
                    anyhow!("not enough V register for this expression"),
                )
            })?;
            self.expr_regs.insert(expr.id, (dvreg, bit_len1));
        }

        // FIXME:
        //   * div zero is allowed
        //   * shift more than bit length is allowed
        //   * TODO: find more special behaviors
        // See: https://github.com/riscv-software-src/riscv-isa-sim/blob/master/riscv/insns/v{op}_{v,vv,vx,vi,vm,vf,..}.h
        let ts = match op {
            // The `+` operator (addition)
            syn::BinOp::Add(_) => {
                quote! {
                    #expr1.overflowing_add(#expr2).0
                }
            }
            // The `-` operator (subtraction)
            syn::BinOp::Sub(_) => {
                quote! {
                    #expr1.overflowing_sub(#expr2).0
                }
            }
            // The `*` operator (multiplication)
            syn::BinOp::Mul(_) => {
                quote! {
                    #expr1.overflowing_mul(#expr2).0
                }
            }
            // The `/` operator (division)
            syn::BinOp::Div(_) => {
                let uint_type = quote::format_ident!("U{}", bit_length);
                quote! {
                    #expr1.checked_div(#expr2).unwrap_or_else(|| #uint_type::max_value())
                }
            }
            // The `%` operator (modulus)
            syn::BinOp::Rem(_) => {
                quote! {
                    #expr1 % #expr2
                }
            }

            // The `&&` operator (logical and)
            // The `||` operator (logical or)
            // NOTE: early returned when check type names
            syn::BinOp::And(_) | syn::BinOp::Or(_) => unreachable!(),

            // The `^` operator (bitwise xor)
            syn::BinOp::BitXor(_) => {
                quote! {
                    #expr1 ^ #expr2
                }
            }
            // The `&` operator (bitwise and)
            syn::BinOp::BitAnd(_) => {
                quote! {
                    #expr1 & #expr2
                }
            }
            // The `|` operator (bitwise or)
            syn::BinOp::BitOr(_) => {
                quote! {
                    #expr1 | #expr2
                }
            }
            // The `<<` operator (shift left)
            syn::BinOp::Shl(_) => {
                quote! {
                    #expr1 << #expr2
                }
            }
            // The `>>` operator (shift right)
            syn::BinOp::Shr(_) => {
                quote! {
                    #expr1 >> #expr2
                }
            }
            // The `==` operator (equality)
            syn::BinOp::Eq(_) => {
                quote! {
                    #expr1 == #expr2
                }
            }
            // The `<` operator (less than)
            syn::BinOp::Lt(_) => {
                quote! {
                    #expr1 < #expr2
                }
            }
            // The `<=` operator (less than or equal to)
            syn::BinOp::Le(_) => {
                quote! {
                    #expr1 <= #expr2
                }
            }
            // The `!=` operator (not equal to)
            syn::BinOp::Ne(_) => {
                quote! {
                    #expr1 != #expr2
                }
            }
            // The `>=` operator (greater than or equal to)
            syn::BinOp::Ge(_) => {
                quote! {
                    #expr1 >= #expr2
                }
            }
            // The `>` operator (greater than)
            syn::BinOp::Gt(_) => {
                quote! {
                    #expr1 > #expr2
                }
            }
            // The `+=` operator
            syn::BinOp::AddEq(_) => {
                quote! {
                    #expr1 = #expr1.overflowing_add(#expr2).0
                }
            }
            // The `-=` operator
            syn::BinOp::SubEq(_) => {
                quote! {
                    #expr1 = #expr1.overflowing_sub(#expr2).0
                }
            }
            // The `*=` operator
            syn::BinOp::MulEq(_) => {
                quote! {
                    #expr1 = #expr1.overflowing_mul(#expr2).0
                }
            }
            // The `/=` operator
            syn::BinOp::DivEq(_) => {
                let uint_type = quote::format_ident!("U{}", bit_length);
                quote! {
                    #expr1 = #expr1.checked_div(#expr2).unwrap_or_else(|| #uint_type::max_value())
                }
            }
            // The `%=` operator
            syn::BinOp::RemEq(_) => {
                quote! {
                    #expr1 %= #expr2
                }
            }
            // The `^=` operator
            syn::BinOp::BitXorEq(_) => {
                quote! {
                    #expr1 ^= #expr2
                }
            }
            // The `&=` operator
            syn::BinOp::BitAndEq(_) => {
                quote! {
                    #expr1 &= #expr2
                }
            }
            // The `|=` operator
            syn::BinOp::BitOrEq(_) => {
                quote! {
                    #expr1 |= #expr2
                }
            }
            // The `<<=` operator
            syn::BinOp::ShlEq(_) => {
                quote! {
                    #expr1 <<= #expr2
                }
            }
            // The `>>=` operator
            syn::BinOp::ShrEq(_) => {
                quote! {
                    #expr1 >>= #expr2
                }
            }
        };
        tokens.extend(Some(ts));
        self.expr_tokens.insert(expr.id, (tokens.clone(), bit_len1));
        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some((dvreg, bit_len)) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, (dvreg, bit_len));
            }
            let ts_inner = tokens.clone();
            let ts = quote! {
                (#ts_inner)
            };
            self.expr_tokens.insert(extra_expr_id, (ts, bit_len1));
        }
        Ok(tokens)
    }
    fn default_method_call_codegen(
        &mut self,
        receiver: &TypedExpression,
        method: &syn::Ident,
        args: &[TypedExpression],
    ) -> Result<TokenStream, SpannedError> {
        let mut tokens = TokenStream::new();
        receiver.to_tokens(&mut tokens, self)?;
        token::Dot::default().to_tokens(&mut tokens);
        method.to_tokens(&mut tokens);
        catch_inner_error(|err| {
            token::Paren::default().surround(&mut tokens, |inner| {
                for (idx, ty) in args.iter().enumerate() {
                    if let Err(inner_err) = ty.to_tokens(inner, self) {
                        *err = Some(inner_err);
                        return;
                    }
                    if idx != args.len() - 1 {
                        token::Comma::default().to_tokens(inner);
                    }
                }
            });
        })?;
        Ok(tokens)
    }

    #[cfg(not(feature = "simulator"))]
    #[allow(clippy::too_many_arguments)]
    fn gen_method_call_tokens(
        &mut self,
        expr: &TypedExpression,
        receiver: &TypedExpression,
        method: &syn::Ident,
        args: &[TypedExpression],
        top_level: bool,
        extra_bind_id: Option<usize>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        fn update_vconfig(tokens: &mut TokenStream, bit_length: u16, context: &mut CodegenContext) {
            // vsetvli x0, t0, e{256,512,1024}, m1, ta, ma
            let v_config = VConfig::Vsetvli {
                rd: XReg::Zero,
                rs1: XReg::T0,
                vtypei: Vtypei::new(bit_length, Vlmul::M1, true, true),
            };
            if context.v_config.as_ref() != Some(&v_config) {
                context.v_config = Some(v_config);
                let inst = VInst::VConfig(v_config);
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if context.show_asm {
                    let comment = format!("{} - {}", inst.encode_u32(), inst);
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                    }));
                }
                let ts = quote! {
                    unsafe {
                        asm!(
                            "li t0, 1",  // AVL = 1
                            ".byte {0}, {1}, {2}, {3}",
                            const #b0, const #b1, const #b2, const #b3,
                        )
                    }
                };
                tokens.extend(Some(ts));
            }
        }

        let receiver_bit_length: u16 = match receiver.type_name().as_deref() {
            Some("U256") => 256,
            Some("U512") => 512,
            Some("U1024") => 1024,
            _ => self
                .expr_regs
                .get(&expr.id)
                .map(|(_, bit_len)| *bit_len)
                .unwrap_or(0),
        };
        if top_level {
            bit_length = receiver_bit_length;
        }
        if bit_length == 0 {
            return self.default_method_call_codegen(receiver, method, args);
        }

        let method_string = method.to_string();
        let mut tokens = TokenStream::new();
        match method_string.as_str() {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "wrapping_div" | "wrapping_rem"
            | "overflowing_add" | "overflowing_sub" | "overflowing_mul" | "checked_add"
            | "checked_sub" | "checked_mul" | "checked_div" | "checked_rem" | "saturating_add"
            | "saturating_sub" | "saturating_mul" => {
                if args.len() != 1 {
                    return Err((
                        expr.expr.1,
                        anyhow!(
                            "special method call to U256/U512/U1024, must have exact one argument"
                        ),
                    ));
                }
            }
            _ => {
                return self.default_method_call_codegen(receiver, method, args);
            }
        }

        update_vconfig(&mut tokens, bit_length, self);

        let left = &receiver;
        let right = &args[0];
        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(typed_expr.id, (*vreg, bit_length));
                } else {
                    // Load{256,512,1024}
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    // FIXME: t0 register may already used by Rust code
                    let inst = VInst::VleV {
                        width: bit_length,
                        vd: VReg::from_u8(vreg),
                        rs1: XReg::T0,
                        vm: false,
                    };
                    let [b0, b1, b2, b3] = inst.encode_bytes();
                    if self.show_asm {
                        let comment = format!("{} - {}", inst.encode_u32(), inst);
                        tokens.extend(Some(quote! {
                            let _ = #comment;
                        }));
                    }
                    let ts = quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_ident.as_ref().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    };
                    tokens.extend(Some(ts));
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, (vreg, bit_length));
                }
            } else {
                let ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
                tokens.extend(Some(ts));
            }
        }

        let (svreg2, bit_len2) = *self.expr_regs.get(&left.id).unwrap();
        let (svreg1, bit_len1) = *self.expr_regs.get(&right.id).unwrap();
        assert_eq!(bit_len1, bit_len2);
        let dvreg = self.v_registers.next_register().ok_or_else(|| {
            (
                expr.expr.1,
                anyhow!("not enough V register for this expression"),
            )
        })?;
        self.expr_regs.insert(expr.id, (dvreg, bit_len1));
        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some((dvreg, bit_len)) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, (dvreg, bit_len));
            }
        }

        let ivv = Ivv {
            vd: VReg::from_u8(dvreg),
            vs2: VReg::from_u8(svreg2),
            vs1: VReg::from_u8(svreg1),
            vm: false,
        };

        match method_string.as_str() {
            "wrapping_add" => inst_codegen(&mut tokens, VInst::VaddVv(ivv), self.show_asm),
            "wrapping_sub" => inst_codegen(&mut tokens, VInst::VsubVv(ivv), self.show_asm),
            "wrapping_mul" => inst_codegen(&mut tokens, VInst::VmulVv(ivv), self.show_asm),
            "wrapping_div" => inst_codegen(&mut tokens, VInst::VdivuVv(ivv), self.show_asm),
            "wrapping_rem" => inst_codegen(&mut tokens, VInst::VremuVv(ivv), self.show_asm),

            /*
            vadd.vv v1, v2, v3
            vmsltu.vv v4, v1, v2
            vfirst.m t0, v4
            if t0 == 0 {
                (v1, true)
            } else {
                (v1, false)
            }
            */
            "overflowing_add" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VaddVv(ivv),
                    ivv,
                    bit_length,
                    false,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            vsub.vv v1, v2, v3
            vmsltu.vv v4, v1, v2
            vfirst.m t0, v4
            if t0 == 0 {
                (v1, true)
            } else {
                (v1, false)
            }
             */
            "overflowing_sub" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VsubVv(ivv),
                    ivv,
                    bit_length,
                    false,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            vmul.vv v1, v2, v3
            vmsne.vi v4 v1, 0
            vfirst.m t0, v4
            if t0 == 0 {
                vdivu.vv v4, v1, v2
                vmsne.vv v4, v4, v3
                vfirst.m t1, v4
                (v1, t1 == 0)
            } else {
                (v1, false)
            }
             */
            "overflowing_mul" => {
                self.overflowing_mul_codegen(&mut tokens, ivv, bit_length, false)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            /*
            let (value, overflow) = self.overflowing_add(other);
            if overflow {
                None
            } else {
                Some(value)
            }
             */
            "checked_add" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VaddVv(ivv),
                    ivv,
                    bit_length,
                    true,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            let (value, overflow) = self.overflowing_sub(other);
            if overflow {
                None
            } else {
                Some(value)
            }
             */
            "checked_sub" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VsubVv(ivv),
                    ivv,
                    bit_length,
                    true,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            let (value, overflow) = self.overflowing_mul(other);
            if overflow {
                None
            } else {
                Some(value)
            }
             */
            "checked_mul" => {
                self.overflowing_mul_codegen(&mut tokens, ivv, bit_length, true)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            /*
            if other.is_zero() {
                None
            } else {
                Some(self.wrapping_div(other))
            }

            vmseq.vi v4, v2, 0  # (v2 == vs1)
            vfirst.m t0, v4
            if t0 == 0 {
                None
            } else {
                vdivu.vv v1, v2, v3
                Some(v1)
            }
             */
            "checked_div" => {
                self.simple_checked_codegen(&mut tokens, VInst::VdivuVv(ivv), ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            if other.is_zero() {
                None
            } else {
                Some(self.wrapping_rem(other))
            }

            => Same as checked_div()
             */
            "checked_rem" => {
                self.simple_checked_codegen(&mut tokens, VInst::VremuVv(ivv), ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            // vsaddu.vv vd, vs2, vs1, vm
            "saturating_add" => inst_codegen(&mut tokens, VInst::VsadduVv(ivv), self.show_asm),
            // vssubu.vv vd, vs2, vs1, vm
            "saturating_sub" => inst_codegen(&mut tokens, VInst::VssubuVv(ivv), self.show_asm),
            /*
            vmul.vv v1, v2, v3
            vmsne.vi v4 v1, 0
            vfirst.m t0, v4
            if t0 == 0 {
                vdivu.vv v4, v1, v2
                vmsne.vv v4, v4, v3
                vfirst.m t1, v4
                if t1 == 0 {
                    Uxx::max_value()
                } else {
                    v1
                }
            } else {
                v1
            }
             */
            "saturating_mul" => {
                self.saturating_mul_codegen(&mut tokens, ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }
            _ => {}
        };

        let is_simple_asm = matches!(
            method_string.as_str(),
            "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "wrapping_div"
                | "wrapping_rem"
                | "saturating_add"
                | "saturating_sub"
        );

        if top_level {
            if is_simple_asm {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VseV {
                    width: bit_length,
                    vs3: VReg::from_u8(vreg),
                    rs1: XReg::T0,
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                    }));
                }
                let uint_type = quote::format_ident!("U{}", bit_length);
                let buf_length = bit_length as usize / 8;
                tokens.extend(Some(quote! {
                    let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                    unsafe {
                        asm!(
                            "mv t0, {0}",
                            // This should be vse{256, 512, 1024}
                            ".byte {1}, {2}, {3}, {4}",
                            in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                            const #b0, const #b1, const #b2, const #b3,
                        )
                    }
                    unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
                }));
            }
            let mut rv = TokenStream::new();
            token::Brace::default().surround(&mut rv, |inner| {
                inner.extend(Some(tokens));
            });
            Ok(rv)
        } else {
            Ok(tokens)
        }
    }

    #[cfg(not(feature = "simulator"))]
    fn simple_checked_codegen(
        &mut self,
        tokens: &mut TokenStream,
        inst: VInst,
        ivv: Ivv,
        bit_length: u16,
    ) -> Result<(), anyhow::Error> {
        let eq_vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();
        for pre_inst in [
            VInst::VmseqVi(Ivi {
                vd: VReg::from_u8(eq_vd),
                vs2: ivv.vs1,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(eq_vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, pre_inst, self.show_asm);
        }
        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T1,
            vm: false,
        };
        let [b0_inst, b1_inst, b2_inst, b3_inst] = inst.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;
        let ts = quote! {
            let tmp_bool_var: i64;
            // tn: 0  (vms* success)
            // tn: -1 (not found)
            unsafe {
                asm!(
                    "mv {0} t0",
                    out(reg) tmp_bool_var,
                )
            }
            if tmp_bool_var == 0 {
                None
            } else {
                let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                unsafe {
                    asm!(
                        ".byte {0}, {1}, {2}, {3}"
                        "mv t1, {4}",
                        ".byte {5}, {6}, {7}, {8}",
                        const #b0_inst, const #b1_inst, const #b2_inst, const #b3_inst,
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                    )
                }
                Some(unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) })
            }
        };
        inner_tokens.extend(Some(ts));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    #[cfg(not(feature = "simulator"))]
    fn simple_overflowing_codegen(
        &mut self,
        tokens: &mut TokenStream,
        inst: VInst,
        ivv: Ivv,
        bit_length: u16,
        // checked_{add,sub}()
        is_checked: bool,
    ) -> Result<(), anyhow::Error> {
        let lt_vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();
        for inst in [
            inst,
            VInst::VmsltuVv(Ivv {
                vd: VReg::from_u8(lt_vd),
                vs2: ivv.vd,
                vs1: ivv.vs1,
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(lt_vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }
        if is_checked {
            checked_rv_codegen(&mut inner_tokens, ivv.vd, bit_length, self.show_asm);
        } else {
            overflowing_rv_codegen(&mut inner_tokens, ivv.vd, bit_length, self.show_asm);
        }
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    #[cfg(not(feature = "simulator"))]
    fn overflowing_mul_codegen(
        &mut self,
        tokens: &mut TokenStream,
        ivv: Ivv,
        bit_length: u16,
        // is checked_mul()
        is_checked: bool,
    ) -> Result<(), anyhow::Error> {
        let vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();

        // vmul.vv v1, v2, v3
        // vmsne.vi v4 v1, 0
        // vfirst.m t0, v4
        for inst in [
            VInst::VmulVv(ivv),
            VInst::VmsneVi(Ivi {
                vd: VReg::from_u8(vd),
                vs2: ivv.vd,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }

        let inst_div = VInst::VdivuVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: ivv.vd,
            vs1: ivv.vs2,
            vm: false,
        });

        let inst_ne = VInst::VmsneVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: VReg::from_u8(vd),
            vs1: ivv.vs1,
            vm: false,
        });

        let inst_firstm = VInst::VfirstM {
            rd: XReg::T1,
            vs2: VReg::from_u8(vd),
            vm: false,
        };
        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T2,
            vm: false,
        };

        let [b0_div, b1_div, b2_div, b3_div] = inst_div.encode_bytes();
        let [b0_ne, b1_ne, b2_ne, b3_ne] = inst_ne.encode_bytes();
        let [b0_firstm, b1_firstm, b2_firstm, b3_firstm] = inst_firstm.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;
        inner_tokens.extend(Some(quote! {
            let tmp_bool_t0: i64;
            let mut tmp_rvv_vector_buf = [0u8; #buf_length];
            unsafe {
                asm!(
                    "mv {0}, t0",
                    "mv t2, {1}",
                    // vse{n}.v v1, (t2)
                    ".byte {2}, {3}, {4}, {5}",
                    out(reg) tmp_bool_t0,
                    in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                    const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                )
            }
            let tmp_uint_rv = unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) };
        }));
        let ts = if is_checked {
            quote! {
                if tmp_bool_t0 == 0 {
                    let tmp_bool_t1: i64;
                    unsafe {
                        asm!(
                            // vdivu.vv v4, v1, v2
                            ".byte {0}, {1}, {2}, {3}",
                            // vmsne.vv v4, v4, v3
                            ".byte {4}, {5}, {6}, {7}",
                            // vfirst.m t1, v4
                            ".byte {8}, {9}, {10}, {11}",
                            "mv {12}, t1",
                            const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                            const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                            const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                            out(reg) tmp_bool_t1,
                        )
                    }
                    if tmp_bool_t1 == 0 {
                        None
                    } else {
                        Some(tmp_uint_rv)
                    }
                } else {
                    Some(tmp_uint_rv)
                }
            }
        } else {
            quote! {
                if tmp_bool_t0 == 0 {
                    let tmp_bool_t1: i64;
                    unsafe {
                        asm!(
                            // vdivu.vv v5, v1, v2
                            ".byte {0}, {1}, {2}, {3}",
                            // vmsne.vv v4, v5, v3
                            ".byte {4}, {5}, {6}, {7}",
                            // vfirst.m t1, v4
                            ".byte {8}, {9}, {10}, {11}",
                            "mv {12}, t1",
                            const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                            const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                            const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                            out(reg) tmp_bool_t1,
                        )
                    }
                    (tmp_uint_rv, tmp_bool_t1 == 0)
                } else {
                    (tmp_uint_rv, false)
                }
            }
        };
        inner_tokens.extend(Some(ts));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    #[cfg(not(feature = "simulator"))]
    fn saturating_mul_codegen(
        &mut self,
        tokens: &mut TokenStream,
        ivv: Ivv,
        bit_length: u16,
    ) -> Result<(), anyhow::Error> {
        let vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;

        let mut inner_tokens = TokenStream::new();
        for inst in [
            VInst::VmulVv(ivv),
            VInst::VmsneVi(Ivi {
                vd: VReg::from_u8(vd),
                vs2: ivv.vd,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }

        let inst_div = VInst::VdivuVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: ivv.vd,
            vs1: ivv.vs2,
            vm: false,
        });
        let inst_ne = VInst::VmsneVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: VReg::from_u8(vd),
            vs1: ivv.vs1,
            vm: false,
        });
        let inst_firstm = VInst::VfirstM {
            rd: XReg::T1,
            vs2: VReg::from_u8(vd),
            vm: false,
        };
        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T2,
            vm: false,
        };
        let [b0_div, b1_div, b2_div, b3_div] = inst_div.encode_bytes();
        let [b0_ne, b1_ne, b2_ne, b3_ne] = inst_ne.encode_bytes();
        let [b0_firstm, b1_firstm, b2_firstm, b3_firstm] = inst_firstm.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;
        inner_tokens.extend(Some(quote! {
            let tmp_bool_t0: i64;
            let tmp_bool_t1: i64 = -1;
            unsafe {
                asm!(
                    "mv {0}, t0",
                    out(reg) tmp_bool_t0;
                )
            }
            if tmp_bool_t0 == 0 {
                unsafe {
                    asm!(
                        ".byte {0}, {1}, {2}, {3}",
                        ".byte {4}, {5}, {6}, {7}",
                        ".byte {8}, {9}, {10}, {11}",
                        "mv {12}, t1",
                        const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                        const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                        const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                        out(reg) tmp_bool_t1,
                    )
                }
            }
            if tmp_bool_t1 == 0 {
                #uint_type::max_value()
            } else {
                let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                unsafe {
                    asm!(
                        "mv t2, {0}",
                        ".byte {1}, {2}, {3}, {4}",
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                    )
                }
                unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
            }
        }));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    // Generate raw asm statements for top level expression
    #[cfg(not(feature = "simulator"))]
    fn gen_tokens(
        &mut self,
        expr: &TypedExpression,
        top_level: bool,
        extra_bind_id: Option<usize>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        let (left, op, right, is_assign) = match &expr.expr.0 {
            Expression::AssignOp { left, op, right } => (left, op, right, true),
            Expression::Binary { left, op, right } => (left, op, right, false),
            Expression::MethodCall { receiver, method, args, .. } => {
                return self.gen_method_call_tokens(expr, receiver, method, args, top_level, extra_bind_id, bit_length);
            }
            Expression::Paren { expr: sub_expr, .. } => {
                return self.gen_tokens(&*sub_expr, top_level, Some(expr.id), bit_length);
            }
            _  => return Err((expr.expr.1, anyhow!("invalid expression, inner expression must be simple variable name or binary op"))),
        };
        if !top_level && is_assign {
            return Err((
                expr.expr.1,
                anyhow!("assign op in sub-expression is forbidden"),
            ));
        }

        let mut tokens = TokenStream::new();

        if top_level {
            let left_type_name = left.type_name();
            let right_type_name = right.type_name();
            match (left_type_name.as_deref(), right_type_name.as_deref()) {
                (Some("U256"), Some("U256")) => {
                    bit_length = 256;
                }
                (Some("U512"), Some("U512")) => {
                    bit_length = 512;
                }
                (Some("U1024"), Some("U1024")) => {
                    bit_length = 1024;
                }
                _ => {
                    left.to_tokens(&mut tokens, self)?;
                    op.to_tokens(&mut tokens);
                    right.to_tokens(&mut tokens, self)?;
                    return Ok(tokens);
                }
            };
        }
        // vsetvli x0, t0, e{256,512,1024}, m1, ta, ma
        let v_config = VConfig::Vsetvli {
            rd: XReg::Zero,
            rs1: XReg::T0,
            vtypei: Vtypei::new(bit_length, Vlmul::M1, true, true),
        };
        if self.v_config.as_ref() != Some(&v_config) {
            self.v_config = Some(v_config);
            let inst = VInst::VConfig(v_config);
            let [b0, b1, b2, b3] = inst.encode_bytes();
            if self.show_asm {
                let comment = format!("{} - {}", inst.encode_u32(), inst);
                tokens.extend(Some(quote! {
                    let _ = #comment;
                }));
            }
            let ts = quote! {
                unsafe {
                    asm!(
                        "li t0, 1",  // AVL = 1
                        ".byte {0}, {1}, {2}, {3}",
                        const #b0, const #b1, const #b2, const #b3,
                    )
                }
            };
            tokens.extend(Some(ts));
        }

        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(typed_expr.id, (*vreg, bit_length));
                } else {
                    // Load{256,512,1024}
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    // FIXME: t0 register may already used by Rust code
                    let inst = VInst::VleV {
                        width: bit_length,
                        vd: VReg::from_u8(vreg),
                        rs1: XReg::T0,
                        vm: false,
                    };
                    let [b0, b1, b2, b3] = inst.encode_bytes();
                    if self.show_asm {
                        let comment = format!("{} - {}", inst.encode_u32(), inst);
                        tokens.extend(Some(quote! {
                            let _ = #comment;
                        }));
                    }
                    let ts = quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_ident.as_ref().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    };
                    tokens.extend(Some(ts));
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, (vreg, bit_length));
                }
            } else {
                let ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
                tokens.extend(Some(ts));
            }
        }

        let op_category = OpCategory::from(op);
        let (svreg2, bit_len2) = *self.expr_regs.get(&left.id).unwrap();
        let (svreg1, bit_len1) = *self.expr_regs.get(&right.id).unwrap();
        assert_eq!(bit_len1, bit_len2);
        let dvreg = match op_category {
            OpCategory::Binary | OpCategory::Bool => {
                let dvreg = self.v_registers.next_register().ok_or_else(|| {
                    (
                        expr.expr.1,
                        anyhow!("not enough V register for this expression"),
                    )
                })?;
                self.expr_regs.insert(expr.id, (dvreg, bit_len1));
                dvreg
            }
            OpCategory::AssignOp => svreg1,
        };
        let ivv = Ivv {
            vd: VReg::from_u8(dvreg),
            vs2: VReg::from_u8(svreg2),
            vs1: VReg::from_u8(svreg1),
            vm: false,
        };
        let inst = match op {
            // ==== OpCategory::Binary | OpCategory::AssignOp ====
            // The `+` operator (addition)
            // The `+=` operator
            syn::BinOp::Add(_) | syn::BinOp::AddEq(_) => VInst::VaddVv(ivv),
            // The `-` operator (subtraction)
            // The `-=` operator
            syn::BinOp::Sub(_) | syn::BinOp::SubEq(_) => VInst::VsubVv(ivv),
            // The `*` operator (multiplication)
            // The `*=` operator
            syn::BinOp::Mul(_) | syn::BinOp::MulEq(_) => VInst::VmulVv(ivv),
            // The `/` operator (division)
            // The `/=` operator
            syn::BinOp::Div(_) | syn::BinOp::DivEq(_) => VInst::VdivuVv(ivv),
            // The `%` operator (modulus)
            // The `%=` operator
            syn::BinOp::Rem(_) | syn::BinOp::RemEq(_) => VInst::VremuVv(ivv),
            // The `^` operator (bitwise xor)
            // The `^=` operator
            syn::BinOp::BitXor(_) | syn::BinOp::BitXorEq(_) => VInst::VxorVv(ivv),
            // The `&` operator (bitwise and)
            // The `&=` operator
            syn::BinOp::BitAnd(_) | syn::BinOp::BitAndEq(_) => VInst::VandVv(ivv),
            // The `|` operator (bitwise or)
            // The `|=` operator
            syn::BinOp::BitOr(_) | syn::BinOp::BitOrEq(_) => VInst::VorVv(ivv),
            // The `<<` operator (shift left)
            // The `<<=` operator
            syn::BinOp::Shl(_) | syn::BinOp::ShlEq(_) => VInst::VsllVv(ivv),
            // The `>>` operator (shift right)
            // The `>>=` operator
            syn::BinOp::Shr(_) | syn::BinOp::ShrEq(_) => VInst::VsrlVv(ivv),

            // The `&&` operator (logical and)
            // The `||` operator (logical or)
            // NOTE: early returned when check type names
            syn::BinOp::And(_) | syn::BinOp::Or(_) => unreachable!(),

            // ==== OpCategory::Bool ====
            // The `==` operator (equality)
            syn::BinOp::Eq(_) => VInst::VmseqVv(ivv),
            // The `<` operator (less than)
            syn::BinOp::Lt(_) => VInst::VmsltuVv(ivv),
            // The `<=` operator (less than or equal to)
            syn::BinOp::Le(_) => VInst::VmsleuVv(ivv),
            // The `!=` operator (not equal to)
            syn::BinOp::Ne(_) => VInst::VmsneVv(ivv),
            // The `>=` operator (greater than or equal to)
            syn::BinOp::Ge(_) => VInst::VmsgeuVv(ivv),
            // The `>` operator (greater than)
            syn::BinOp::Gt(_) => VInst::VmsgtuVv(ivv),
        };
        let [b0, b1, b2, b3] = inst.encode_bytes();
        if self.show_asm {
            let comment = format!("{} - {}", inst, inst.encode_u32());
            tokens.extend(Some(quote! {
                let _ = #comment;
            }));
        }
        let ts = quote! {
            unsafe {
                asm!(".byte {0}, {1}, {2}, {3}", const #b0, const #b1, const #b2, const #b3,)
            }
        };
        tokens.extend(Some(ts));

        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some((dvreg, bit_len)) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, (dvreg, bit_len));
            }
        }

        match op_category {
            OpCategory::Binary if top_level => {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VseV {
                    width: bit_length,
                    vs3: VReg::from_u8(vreg),
                    rs1: XReg::T0,
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                    }));
                }
                let uint_type = quote::format_ident!("U{}", bit_length);
                let buf_length = bit_length as usize / 8;
                tokens.extend(Some(quote! {
                    let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                    unsafe {
                        asm!(
                            "mv t0, {0}",
                            // This should be vse{256, 512, 1024}
                            ".byte {1}, {2}, {3}, {4}",
                            in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                            const #b0, const #b1, const #b2, const #b3,
                        )
                    }
                    unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
                }));
                let mut rv = TokenStream::new();
                token::Brace::default().surround(&mut rv, |inner| {
                    inner.extend(Some(tokens));
                });
                Ok(rv)
            }
            OpCategory::Binary | OpCategory::AssignOp => Ok(tokens),
            OpCategory::Bool => {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VfirstM {
                    rd: XReg::T0,
                    vs2: VReg::from_u8(vreg),
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                        let _ = "mv {tmp_rv_t0} t0";
                    }));
                }
                tokens.extend(Some(quote! {
                    let tmp_bool_t0: i64;
                    // t0: 0  (vms* success)
                    // t0: -1 (not found)
                    unsafe {
                        asm!(
                            // This should be vfirst.m t0, vrs2
                            ".byte {0}, {1}, {2}, {3}",
                            "mv {4}, t0",
                            const #b0, const #b1, const #b2, const #b3,
                            out (reg) tmp_bool_t0,
                        )
                    }
                    tmp_bool_t0 == 0
                }));
                let mut rv = TokenStream::new();
                token::Brace::default().surround(&mut rv, |inner| {
                    inner.extend(Some(tokens));
                });
                Ok(rv)
            }
        }
    }
}

fn catch_inner_error<F: FnOnce(&mut Option<SpannedError>)>(func: F) -> Result<(), SpannedError> {
    let mut err: Option<SpannedError> = None;
    func(&mut err);
    if let Some(err) = err {
        return Err(err);
    }
    Ok(())
}

pub trait ToTokenStream {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError>;
    fn to_token_stream(&self, context: &mut CodegenContext) -> Result<TokenStream, SpannedError> {
        let mut tokens = TokenStream::new();
        self.to_tokens(&mut tokens, context)?;
        Ok(tokens)
    }
    fn into_token_stream(self, context: &mut CodegenContext) -> Result<TokenStream, SpannedError>
    where
        Self: Sized,
    {
        self.to_token_stream(context)
    }
}

impl ToTokenStream for ReturnType {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        match self {
            ReturnType::Default => {}
            ReturnType::Type(_span, ty) => {
                token::RArrow::default().to_tokens(tokens);
                ty.0.to_tokens(tokens, context)?;
            }
        }
        Ok(())
    }
}
impl ToTokenStream for BareFnArg {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        if let Some((ident, _colon_token)) = self.name.as_ref() {
            ident.to_tokens(tokens);
            token::Colon::default().to_tokens(tokens);
        }
        self.ty.0.to_tokens(tokens, context)?;
        Ok(())
    }
}

impl ToTokenStream for Type {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        match self {
            Type::Array { elem, len, .. } => {
                catch_inner_error(|err| {
                    token::Bracket::default().surround(tokens, |inner| {
                        if let Err(inner_err) = elem.to_tokens(inner, context) {
                            *err = Some(inner_err);
                            return;
                        }
                        token::Semi::default().to_tokens(inner);
                        if let Err(inner_err) = len.to_tokens(inner, context) {
                            *err = Some(inner_err);
                        };
                    });
                })?;
            }
            Type::BareFn { inputs, output, .. } => {
                token::Fn::default().to_tokens(tokens);
                catch_inner_error(|err| {
                    token::Paren::default().surround(tokens, |inner| {
                        for input in inputs {
                            if let Err(inner_err) = input.to_tokens(inner, context) {
                                *err = Some(inner_err);
                                return;
                            }
                        }
                    });
                })?;
                output.0.to_tokens(tokens, context)?;
            }
            Type::Path(path) => {
                path.to_tokens(tokens);
            }
            Type::Reference {
                lifetime,
                mutability,
                elem,
                ..
            } => {
                token::And::default().to_tokens(tokens);
                if let Some(lifetime) = lifetime {
                    lifetime.to_tokens(tokens);
                }
                if mutability.is_some() {
                    token::Mut::default().to_tokens(tokens);
                }
                elem.0.to_tokens(tokens, context)?;
            }
            Type::Slice { elem, .. } => {
                catch_inner_error(|err| {
                    token::Bracket::default().surround(tokens, |inner| {
                        if let Err(inner_err) = elem.0.to_tokens(inner, context) {
                            *err = Some(inner_err);
                        }
                    });
                })?;
            }
            Type::Tuple { elems, .. } => {
                catch_inner_error(|err| {
                    token::Paren::default().surround(tokens, |inner| {
                        for (idx, elem) in elems.iter().enumerate() {
                            if let Err(inner_err) = elem.0.to_tokens(inner, context) {
                                *err = Some(inner_err);
                                return;
                            }
                            if idx != elems.len() - 1 {
                                token::Comma::default().to_tokens(inner);
                            }
                        }
                    });
                })?;
            }
        }
        Ok(())
    }
}
impl ToTokenStream for Pattern {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        match self {
            Pattern::Ident { mutability, ident } => {
                if mutability.is_some() {
                    token::Mut::default().to_tokens(tokens);
                }
                ident.to_tokens(tokens);
            }
            Pattern::Type { pat, ty, .. } => {
                pat.0.to_tokens(tokens, context)?;
                token::Colon::default().to_tokens(tokens);
                ty.0.to_tokens(tokens, context)?;
            }
            Pattern::Range { lo, limits, hi } => {
                lo.to_tokens(tokens, context)?;
                match limits {
                    syn::RangeLimits::HalfOpen(inner) => {
                        inner.to_tokens(tokens);
                    }
                    syn::RangeLimits::Closed(inner) => {
                        inner.to_tokens(tokens);
                    }
                }
                hi.to_tokens(tokens, context)?;
            }
            Pattern::Path(path) => {
                path.to_tokens(tokens);
            }
            Pattern::Wild(_) => {
                token::Underscore::default().to_tokens(tokens);
            }
        }
        Ok(())
    }
}
impl ToTokenStream for Expression {
    fn to_tokens(
        &self,
        _tokens: &mut TokenStream,
        _context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        Ok(())
    }
}

impl ToTokenStream for TypedExpression {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        match &self.expr.0 {
            Expression::Array(arr) => {
                arr.to_tokens(tokens);
            }
            // TODO: Optimize by using left expression's register.
            // x = y + x;
            Expression::Assign { left, right, .. } => {
                // === ASM ===
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx", in(reg) left.as_mut_ptr());
                // === Simulator ===
                // {
                //     x = #y.overflowing_add(#z).0
                // }

                left.to_tokens(tokens, context)?;
                token::Eq::default().to_tokens(tokens);
                right.to_tokens(tokens, context)?;
            }
            // x += y;
            Expression::AssignOp { .. } => {
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx", in(reg) left.as_mut_ptr());
                tokens.extend(Some(context.gen_tokens(self, true, None, 0)?));
            }
            Expression::Binary { .. } => {
                // {
                //     let rvv_vector_out: U256;
                //     asm!("xxx");
                //     asm!("xxx");
                //     asm!("xxx");
                //     asm!("xxx", in(reg) rvv_vector_out.as_mut_ptr());
                //     rvv_vector_out
                // }
                tokens.extend(Some(context.gen_tokens(self, true, None, 0)?));
            }
            Expression::Call { func, args, .. } => {
                func.to_tokens(tokens, context)?;
                catch_inner_error(|err| {
                    token::Paren::default().surround(tokens, |inner| {
                        for (idx, ty) in args.iter().enumerate() {
                            if let Err(inner_err) = ty.to_tokens(inner, context) {
                                *err = Some(inner_err);
                                return;
                            };
                            if idx != args.len() - 1 {
                                token::Comma::default().to_tokens(inner);
                            }
                        }
                    });
                })?;
            }
            Expression::MethodCall { .. } => {
                // FIXME: use rvv assembler (overflowing_add/overflowing_sub ...)
                tokens.extend(Some(context.gen_tokens(self, true, None, 0)?));
            }
            Expression::Macro(mac) => {
                mac.to_tokens(tokens);
            }
            Expression::Unary { op, expr } => {
                // FIXME: handle ! op (not, logical inversion)
                op.to_tokens(tokens);
                expr.to_tokens(tokens, context)?;
            }
            Expression::Field { base, member, .. } => {
                base.to_tokens(tokens, context)?;
                token::Dot::default().to_tokens(tokens);
                member.to_tokens(tokens);
            }
            Expression::Cast { expr, ty, .. } => {
                expr.to_tokens(tokens, context)?;
                token::As::default().to_tokens(tokens);
                ty.0.to_tokens(tokens, context)?;
            }
            Expression::Repeat { expr, len, .. } => {
                catch_inner_error(|err| {
                    token::Bracket::default().surround(tokens, |inner| {
                        if let Err(inner_err) = expr.to_tokens(inner, context) {
                            *err = Some(inner_err);
                            return;
                        };
                        token::Semi::default().to_tokens(inner);
                        if let Err(inner_err) = len.to_tokens(inner, context) {
                            *err = Some(inner_err);
                        }
                    });
                })?;
            }
            Expression::Lit(lit) => {
                lit.to_tokens(tokens);
            }
            Expression::Paren { expr, .. } => {
                catch_inner_error(|err| {
                    token::Paren::default().surround(tokens, |inner| {
                        if let Err(inner_err) = expr.to_tokens(inner, context) {
                            *err = Some(inner_err);
                        }
                    });
                })?;
            }
            Expression::Reference {
                mutability, expr, ..
            } => {
                token::And::default().to_tokens(tokens);
                if mutability.is_some() {
                    token::Mut::default().to_tokens(tokens);
                }
                expr.to_tokens(tokens, context)?;
            }
            Expression::Index { expr, index, .. } => {
                expr.to_tokens(tokens, context)?;
                catch_inner_error(|err| {
                    token::Bracket::default().surround(tokens, |inner| {
                        if let Err(inner_err) = index.to_tokens(inner, context) {
                            *err = Some(inner_err);
                        }
                    });
                })?;
            }
            Expression::Path(path) => {
                path.to_tokens(tokens);
            }
            Expression::Break(_) => {
                token::Break::default().to_tokens(tokens);
            }
            Expression::Continue(_) => {
                token::Continue::default().to_tokens(tokens);
            }
            Expression::Return { expr, .. } => {
                token::Return::default().to_tokens(tokens);
                if let Some(expr) = expr.as_ref() {
                    expr.to_tokens(tokens, context)?;
                }
            }
            Expression::Block(block) => {
                block.to_tokens(tokens, context)?;
            }
            Expression::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                token::If::default().to_tokens(tokens);
                cond.to_tokens(tokens, context)?;
                then_branch.to_tokens(tokens, context)?;
                if let Some((_span, expr)) = else_branch.as_ref() {
                    token::Else::default().to_tokens(tokens);
                    expr.to_tokens(tokens, context)?;
                }
            }
            Expression::Range { from, limits, to } => {
                if let Some(expr) = from.as_ref() {
                    expr.to_tokens(tokens, context)?;
                }
                match limits {
                    syn::RangeLimits::HalfOpen(inner) => {
                        inner.to_tokens(tokens);
                    }
                    syn::RangeLimits::Closed(inner) => {
                        inner.to_tokens(tokens);
                    }
                }
                if let Some(expr) = to.as_ref() {
                    expr.to_tokens(tokens, context)?;
                }
            }
            Expression::Loop { body, .. } => {
                token::Loop::default().to_tokens(tokens);
                body.to_tokens(tokens, context)?;
            }
            Expression::ForLoop {
                pat, expr, body, ..
            } => {
                token::For::default().to_tokens(tokens);
                pat.0.to_tokens(tokens, context)?;
                token::In::default().to_tokens(tokens);
                expr.to_tokens(tokens, context)?;
                body.to_tokens(tokens, context)?;
            }
        }
        if self.id == usize::max_value() {
            panic!(
                "[Bug]: current expression not assgined with an id: {:?}",
                self
            );
        }
        Ok(())
    }
}
impl ToTokenStream for Statement {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        match self {
            Statement::Local { pat, init, .. } => {
                token::Let::default().to_tokens(tokens);
                pat.0.to_tokens(tokens, context)?;
                token::Eq::default().to_tokens(tokens);
                init.to_tokens(tokens, context)?;
                token::Semi::default().to_tokens(tokens);
            }
            Statement::Expr(expr) => {
                expr.to_tokens(tokens, context)?;
            }
            Statement::Semi(expr) => {
                expr.to_tokens(tokens, context)?;
                token::Semi::default().to_tokens(tokens);
            }
        }
        Ok(())
    }
}
impl ToTokenStream for Block {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        catch_inner_error(|err| {
            token::Brace::default().surround(tokens, |inner| {
                for stmt in &self.stmts {
                    if let Err(inner_err) = stmt.0.to_tokens(inner, context) {
                        *err = Some(inner_err);
                        return;
                    }
                }
            });
        })?;
        Ok(())
    }
}
impl ToTokenStream for FnArg {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        if self.mutability.is_some() {
            token::Mut::default().to_tokens(tokens);
        }
        self.name.to_tokens(tokens);
        token::Colon::default().to_tokens(tokens);
        self.ty.0.to_tokens(tokens, context)?;
        Ok(())
    }
}
impl ToTokenStream for Signature {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        token::Fn::default().to_tokens(tokens);
        self.ident.to_tokens(tokens);
        catch_inner_error(|err| {
            token::Paren::default().surround(tokens, |inner| {
                for (idx, input) in self.inputs.iter().enumerate() {
                    if let Err(inner_err) = input.to_tokens(inner, context) {
                        *err = Some(inner_err);
                        break;
                    };
                    if idx != self.inputs.len() - 1 {
                        token::Comma::default().to_tokens(inner);
                    }
                }
            });
        })?;
        self.output.0.to_tokens(tokens, context)?;
        Ok(())
    }
}
impl ToTokenStream for ItemFn {
    fn to_tokens(
        &self,
        tokens: &mut TokenStream,
        context: &mut CodegenContext,
    ) -> Result<(), SpannedError> {
        self.vis.to_tokens(tokens);
        self.sig.to_tokens(tokens, context)?;
        self.block.to_tokens(tokens, context)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryFrom;

    use super::*;
    use crate::type_checker::{CheckerContext, TypeChecker};

    fn rvv_test(item: TokenStream, show_asm: bool) -> Result<TokenStream, SpannedError> {
        let input: syn::ItemFn = syn::parse2(item).unwrap();
        let mut out = ItemFn::try_from(&input)?;
        let mut checker_context = CheckerContext::default();
        out.check_types(&mut checker_context)?;

        println!("[variables]:");
        for (ident, (mutability, ty)) in &checker_context.variables {
            if mutability.is_some() {
                println!("  [mut {:6}] => {:?}", ident, ty.0);
            } else {
                println!("  [{:10}] => {:?}", ident, ty.0);
            }
        }
        println!("[literal exprs]:");
        for (expr_id, lit) in &checker_context.literal_exprs {
            println!("  [{}] => {:?}", expr_id, lit);
        }
        println!("[uninfered exprs]:");
        for (expr_id, expr) in &checker_context.uninfered_exprs {
            println!("  [{}] => {:?}", expr_id, expr);
        }
        println!("<< type checked >>");

        let mut tokens = TokenStream::new();
        let mut codegen_context = CodegenContext::new(checker_context.variables, show_asm);
        out.to_tokens(&mut tokens, &mut codegen_context)?;
        // println!("out: {:#?}", out);
        Ok(TokenStream::from(quote!(#tokens)))
    }

    #[test]
    fn test_simple() {
        let input = quote! {
            fn simple(x: u32, mut y: u64, z: &mut u64) -> u128 {
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
        let output = rvv_test(input, false).unwrap();
        println!("[otuput]: {}", output);

        #[cfg(feature = "simulator")]
        let expected_output = quote! {
            fn comp_u256(x: U256, y: U256, mut z: U256, w: U256) -> U256 {
                let x_bytes = x.to_le_bytes();
                let j = x
                    .overflowing_add(
                        (z.overflowing_mul(y)
                         .0
                         .checked_div(w)
                         .unwrap_or_else(|| U256::max_value())))
                    .0;
                if x > y && y == z {
                    z = x & (z | y);
                }
                z = (x.overflowing_sub(y).0).overflowing_mul(x).0;
                let abc = 3456;
                z = (y
                     .overflowing_add(j.overflowing_mul((y.overflowing_sub(x).0)).0)
                     .0);
                z = z.overflowing_add(z).0;
                z = z.overflowing_sub(y).0;
                z = z.overflowing_mul(y).0;
                z = z.overflowing_add(y).0;
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
                let x_bytes = x.to_le_bytes();
                let j = {
                    unsafe {
                        asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 14u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 7u8 , const 208u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) z . as_ref () . as_ptr () , const 135u8 , const 208u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) y . as_ref () . as_ptr () , const 7u8 , const 209u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 17u8 , const 148u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) w . as_ref () . as_ptr () , const 7u8 , const 210u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 34u8 , const 50u8 , const 128u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 131u8 , const 2u8 , const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 211u8 , const 2u8 , const 16u8 ,)
                    }
                    core::mem::transmute::<[u8 ; 32usize], U256>(tmp_rvv_vector_buf)
                };
                if {
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 3u8 , const 32u8 , const 104u8 ,)
                    }
                    let tmp_bool_t0: i64;
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 120u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
                    }
                    tmp_bool_t0 == 0
                } && {
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 132u8 , const 32u8 , const 96u8 ,)
                    }
                    let tmp_bool_t0: i64;
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , "mv {4}, t0" , const 215u8 , const 162u8 , const 136u8 , const 64u8 , out (reg) tmp_bool_t0 ,)
                    }
                    tmp_bool_t0 == 0
                } {
                    z = {
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 4u8 , const 17u8 , const 40u8 ,)
                        }
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 133u8 , const 4u8 , const 36u8 ,)
                        }
                        let mut tmp_rvv_vector_buf = [0u8; 32usize];
                        unsafe {
                            asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 213u8 , const 2u8 , const 16u8 ,)
                        }
                        core::mem::transmute::<[u8 ; 32usize], U256>(tmp_rvv_vector_buf)
                    }
                }
                z = {
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 5u8 , const 1u8 , const 8u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 38u8 , const 176u8 , const 148u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 214u8 , const 2u8 , const 16u8 ,)
                    }
                    core::mem::transmute::<[u8 ; 32usize], U256>(tmp_rvv_vector_buf)
                };
                let abc = 3456;
                z = ({
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) j . as_ref () . as_ptr () , const 135u8 , const 214u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 7u8 , const 32u8 , const 8u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 39u8 , const 215u8 , const 148u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 136u8 , const 39u8 , const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 216u8 , const 2u8 , const 16u8 ,)
                    }
                    core::mem::transmute::<[u8 ; 32usize], U256>(tmp_rvv_vector_buf)
                });
                z = {
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 136u8 , const 16u8 , const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 216u8 , const 2u8 , const 16u8 ,)
                    }
                    core::mem::transmute::<[u8 ; 32usize], U256>(tmp_rvv_vector_buf)
                };
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 1u8 , const 17u8 , const 8u8 ,)
                };
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 33u8 , const 17u8 , const 148u8 ,)
                };
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 1u8 , const 17u8 , const 0u8 ,)
                };
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 33u8 , const 17u8 , const 136u8 ,)
                };
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 1u8 , const 17u8 , const 160u8 ,)
                };
                let zero = U256::zero();
                unsafe {
                    asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) zero . as_ref () . as_ptr () , const 7u8 , const 217u8 , const 2u8 , const 16u8 ,)
                }
                unsafe {
                    asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 41u8 , const 25u8 , const 128u8 ,)
                };
                z
            }
        };
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn test_u1024() {
        let input = quote! {
            fn comp_u1024(x: U1024, y: U1024) -> U1024 {
                let z = (x + y) * x;
                z
            }
        };
        println!("[input ]: {}", input);
        let output = rvv_test(input, false).unwrap();
        println!("[otuput]: {}", output);

        #[cfg(feature = "simulator")]
        let expected_output = quote! {
            fn comp_u1024(x: U1024, y: U1024) -> U1024 {
                let z = (x.overflowing_add(y).0).overflowing_mul(x).0;
                z
            }
        };

        #[cfg(not(feature = "simulator"))]
        let expected_output = quote! {
            fn comp_u1024(x: U1024, y: U1024) -> U1024 {
                let z = {
                    unsafe {
                        asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 15u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 7u8 , const 240u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) y . as_ref () . as_ptr () , const 135u8 , const 240u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 129u8 , const 0u8 , const 0u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 33u8 , const 32u8 , const 148u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 128usize];
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 167u8 , const 241u8 , const 2u8 , const 16u8 ,)
                    }
                    core::mem::transmute::<[u8 ; 128usize], U1024>(tmp_rvv_vector_buf)
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
        let output = rvv_test(input, false).unwrap();
        println!("[otuput]: {}", output);

        let expected_output = quote! {
            fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
                let x_tuple = {
                    unsafe {
                        asm ! ("li t0, 1" , ".byte {0}, {1}, {2}, {3}" , const 87u8 , const 240u8 , const 130u8 , const 15u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) a . as_ref () . as_ptr () , const 7u8 , const 240u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) b . as_ref () . as_ptr () , const 135u8 , const 240u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 129u8 , const 0u8 , const 0u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) c . as_ref () . as_ptr () , const 135u8 , const 241u8 , const 2u8 , const 16u8 ,)
                    }
                    {
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 87u8 , const 162u8 , const 33u8 , const 148u8 ,)
                        }
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 50u8 , const 64u8 , const 100u8 ,)
                        }
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 162u8 , const 88u8 , const 64u8 ,)
                        }
                        let tmp_bool_t0: i64;
                        let mut tmp_rvv_vector_buf = [0u8; 128usize];
                        unsafe {
                            asm ! ("mv {0}, t0" , "mv t2, {1}" , ".byte {2}, {3}, {4}, {5}" , out (reg) tmp_bool_t0 , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 242u8 , const 3u8 , const 16u8 ,)
                        }
                        let tmp_uint_rv = core::mem::transmute::<[u8 ; 128usize], U1024>(tmp_rvv_vector_buf);
                        if tmp_bool_t0 == 0 {
                            let tmp_bool_t1: i64;
                            unsafe {
                                asm ! (".byte {0}, {1}, {2}, {3}" , ".byte {4}, {5}, {6}, {7}" , ".byte {8}, {9}, {10}, {11}" , "mv {12}, t1" , const 215u8 , const 34u8 , const 65u8 , const 128u8 , const 215u8 , const 130u8 , const 81u8 , const 100u8 , const 87u8 , const 163u8 , const 88u8 , const 64u8 , out (reg) tmp_bool_t1 ,)
                            }
                            (tmp_uint_rv, tmp_bool_t1 == 0)
                        } else {
                            (tmp_uint_rv, false)
                        }
                    }
                };
                let x = x_tuple.0;
                let z_opt = {
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) x . as_ref () . as_ptr () , const 7u8 , const 243u8 , const 2u8 , const 16u8 ,)
                    }
                    unsafe {
                        asm ! ("mv t0, {0}" , ".byte {1}, {2}, {3}, {4}" , in (reg) d . as_ref () . as_ptr () , const 135u8 , const 243u8 , const 2u8 , const 16u8 ,)
                    }
                    {
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 52u8 , const 112u8 , const 96u8 ,)
                        }
                        unsafe {
                            asm ! (".byte {0}, {1}, {2}, {3}" , const 215u8 , const 162u8 , const 152u8 , const 64u8 ,)
                        }
                        let tmp_bool_var: i64;
                        unsafe { asm ! ("mv {0} t0" , out (reg) tmp_bool_var ,) }
                        if tmp_bool_var == 0 {
                            None
                        } else {
                            let mut tmp_rvv_vector_buf = [0u8; 128usize];
                            unsafe {
                                asm ! (".byte {0}, {1}, {2}, {3}" "mv t1, {4}" , ".byte {5}, {6}, {7}, {8}" , const 87u8 , const 164u8 , const 99u8 , const 128u8 , in (reg) tmp_rvv_vector_buf . as_mut_ptr () , const 39u8 , const 116u8 , const 3u8 , const 16u8 ,)
                            }
                            Some(core::mem::transmute::<[u8 ; 128usize], U1024>(tmp_rvv_vector_buf))
                        }
                    }
                };
                let z: U1024 = z.unwrap();
                z
            }
        };
        assert_eq!(output.to_string(), expected_output.to_string());
    }
}
