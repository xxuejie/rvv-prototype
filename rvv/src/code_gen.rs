use std::collections::HashMap;

use anyhow::anyhow;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::token;

#[cfg(not(feature = "simulator"))]
use rvv_assembler::{Ivv, VConfig, VInst, VReg, Vlmul, Vtypei, XReg};

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
    AssginOp,
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
            | syn::BinOp::ShrEq(_) => OpCategory::AssginOp,
        }
    }
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
    // expr_id => register_number
    expr_regs: HashMap<usize, u8>,

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
            Expression::Paren { expr: sub_expr, .. } => {
                let ts = self.gen_tokens(&*sub_expr, top_level, Some(expr.id), bit_length)?;
                return Ok(quote! {(#ts)});
            }
            _  => return Err((expr.expr.1, anyhow!("invalid expression, inner expression must be simple variable name or binary op"))),
        };
        if !top_level && is_assign {
            return Err((
                expr.expr.1,
                anyhow!("assign op in inner top level expression is forbidden"),
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
                    self.expr_regs.insert(typed_expr.id, *vreg);
                } else {
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, vreg);
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
            self.expr_regs.insert(expr.id, dvreg);
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
            if let Some(dvreg) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, dvreg);
            }
            let ts_inner = tokens.clone();
            let ts = quote! {
                (#ts_inner)
            };
            self.expr_tokens.insert(extra_expr_id, (ts, bit_len1));
        }
        Ok(tokens)
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
            Expression::Paren { expr: sub_expr, .. } => {
                return self.gen_tokens(&*sub_expr, top_level, Some(expr.id), bit_length);
            }
            _  => return Err((expr.expr.1, anyhow!("invalid expression, inner expression must be simple variable name or binary op"))),
        };
        if !top_level && is_assign {
            return Err((
                expr.expr.1,
                anyhow!("assign op in inner top level expression is forbidden"),
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
            let [b0, b1, b2, b3] = VInst::VConfig(v_config).encode_bytes();
            if self.show_asm {
                // TODO: use to_string()
                let comment = format!("{:?}", v_config);
                tokens.extend(Some(quote! {
                    let _ = concat!(#comment);
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
                    self.expr_regs.insert(typed_expr.id, *vreg);
                } else {
                    // Load{256,512,1024}
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    let inst = VInst::VleV {
                        width: bit_length,
                        vd: VReg::from_u8(vreg),
                        rs1: XReg::T0,
                        vm: false,
                    };
                    let [b0, b1, b2, b3] = inst.encode_bytes();
                    if self.show_asm {
                        // TODO: use VInst::to_string()
                        let comment = format!("{:?}", inst);
                        tokens.extend(Some(quote! {
                            let _ = concat!(#comment);
                        }));
                    }
                    let ts = quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_ident.to_le_bytes().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    };
                    tokens.extend(Some(ts));
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, vreg);
                }
            } else {
                let ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
                tokens.extend(Some(ts));
            }
        }

        let op_category = OpCategory::from(op);
        let svreg1 = *self.expr_regs.get(&left.id).unwrap();
        let svreg2 = *self.expr_regs.get(&right.id).unwrap();
        let dvreg = match op_category {
            OpCategory::Binary | OpCategory::Bool => {
                let dvreg = self.v_registers.next_register().ok_or_else(|| {
                    (
                        expr.expr.1,
                        anyhow!("not enough V register for this expression"),
                    )
                })?;
                self.expr_regs.insert(expr.id, dvreg);
                dvreg
            }
            OpCategory::AssginOp => svreg1,
        };
        let ivv = Ivv {
            vd: VReg::from_u8(dvreg),
            vs2: VReg::from_u8(svreg2),
            vs1: VReg::from_u8(svreg1),
            vm: false,
        };
        let inst = match op {
            // ==== OpCategory::Binary | OpCategory::AssginOp ====
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
            // TODO: use to_string()
            let comment = format!("{:?}", inst);
            tokens.extend(Some(quote! {
                let _ = concat!(#comment);
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
            if let Some(dvreg) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, dvreg);
            }
        }

        // FIXME: handle OpCategory::Bool
        //   1. add vfirst.m asm
        //   2. add label for jump
        if top_level && !is_assign {
            let vreg = *self.expr_regs.get(&expr.id).unwrap();
            let inst = VInst::VseV {
                width: bit_length,
                vs3: VReg::from_u8(vreg),
                rs1: XReg::T0,
                vm: false,
            };
            let [b0, b1, b2, b3] = inst.encode_bytes();
            if self.show_asm {
                // TODO: use to_string()
                let comment = format!("{:?}", inst);
                tokens.extend(Some(quote! {
                    let _ = concat!(#comment);
                }));
            }
            tokens.extend(Some(quote! {
                let mut tmp_rvv_vector_buf = [0u8; 32];
                unsafe {
                    asm!(
                        "mv t0, {0}",
                        // This should be vse{256, 512, 1024}
                        ".byte {1}, {2}, {3}, {4}",
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0, const #b1, const #b2, const #b3,
                    )
                };
                U256::from_little_endian(&tmp_rvv_vector_buf[..])
            }));
            let mut rv = TokenStream::new();
            token::Brace::default().surround(&mut rv, |inner| {
                inner.extend(Some(tokens));
            });
            Ok(rv)
        } else {
            Ok(tokens)
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
            Expression::MethodCall {
                receiver,
                method,
                args,
                ..
            } => {
                // FIXME: use rvv assembler (overflowing_add/overflowing_sub ...)
                receiver.to_tokens(tokens, context)?;
                token::Dot::default().to_tokens(tokens);
                method.to_tokens(tokens);
                catch_inner_error(|err| {
                    token::Paren::default().surround(tokens, |inner| {
                        for (idx, ty) in args.iter().enumerate() {
                            if let Err(inner_err) = ty.to_tokens(inner, context) {
                                *err = Some(inner_err);
                                return;
                            }
                            if idx != args.len() - 1 {
                                token::Comma::default().to_tokens(inner);
                            }
                        }
                    });
                })?;
            }
            Expression::Macro(mac) => {
                mac.to_tokens(tokens);
            }
            Expression::Unary { op, expr } => {
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
        {
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
            assert_eq!(output.to_string(), expected_output.to_string());
        }
    }

    #[test]
    fn test_u1024() {
        let input = quote! {
            fn comp_u1024(x: U1024, y: U1024) -> U1024 {
                let z = (x + y) * x;
                let zero = U1024::zero();
                let q = z / zero;
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
                        asm!("li t0, 1", ".byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 15u8 ,)
                    }
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) x.to_le_bytes ().as_ptr (), const 7u8, const 240u8, const 2u8, const 16u8 ,)
                    }
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) y.to_le_bytes ().as_ptr (), const 135u8, const 240u8, const 2u8, const 16u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 1u8, const 16u8, const 0u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 1u8, const 1u8, const 148u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr (), const 167u8, const 241u8, const 2u8, const 16u8 ,)
                    };
                    U256::from_little_endian(&tmp_rvv_vector_buf[..])
                };
                z
            }
        };
        assert_eq!(output.to_string(), expected_output.to_string());
    }
}
