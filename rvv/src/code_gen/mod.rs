use std::collections::HashMap;

#[cfg(not(feature = "simulator"))]
use anyhow::anyhow;
#[cfg(not(feature = "simulator"))]
use quote::quote;

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::token;

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Statement, Type,
    TypedExpression,
};
use crate::type_checker::VarInfo;
use crate::SpannedError;
#[cfg(not(feature = "simulator"))]
use rvv_assembler::{VConfig, VInst, VReg, XReg};

#[cfg(not(feature = "simulator"))]
mod asm;
#[cfg(feature = "simulator")]
mod simulator;

// =============================
// ==== impl ToTokens for T ====
// =============================

#[derive(Default)]
pub struct Registers {
    pub category: &'static str,
    pub items: [bool; 32],
}

impl Registers {
    pub fn new(category: &'static str, pre_alloced: Vec<usize>) -> Registers {
        let mut items = [false; 32];
        for idx in pre_alloced {
            items[idx] = true;
        }
        Registers { category, items }
    }

    pub fn alloc(&mut self) -> Option<u8> {
        // skip v0 register
        for i in 1..32 {
            if !self.items[i] {
                self.items[i] = true;
                return Some(i as u8);
            }
        }
        None
    }
    // Regsiter should be free when:
    //  * variable register reach it's lifetime end
    //  * expression register when after be used in outter expression
    //  * expression register be stored to variable (top level expression)
    #[cfg(not(feature = "simulator"))]
    pub fn free(&mut self, index: u8) {
        if index >= 32 {
            panic!("invalid register number to free: {}", index);
        }
        if !self.items[index as usize] {
            panic!("double free register, number: {}", index);
        }
        self.items[index as usize] = false;
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

#[derive(Clone)]
struct RegInfo {
    number: u8,
    bit_length: u16,
    var_ident: Option<syn::Ident>,
    is_freed: bool,
}

impl RegInfo {
    fn new(number: u8, bit_length: u16, var_ident: Option<syn::Ident>) -> RegInfo {
        RegInfo {
            number,
            bit_length,
            var_ident,
            is_freed: false,
        }
    }
}

#[derive(Default)]
pub struct CodegenContext {
    // vector registers
    v_registers: Registers,
    // general registers

    // FIXME: handle varable scope
    // var_name => register_number
    var_regs: HashMap<syn::Ident, u8>,
    // expr_id => (register_number, bit_length)
    expr_regs: HashMap<usize, RegInfo>,

    // expr_id => (var_name, bit_length)
    #[cfg(feature = "simulator")]
    expr_tokens: HashMap<usize, (TokenStream, u16)>,

    // FIXME: fill in current module
    // ident => (mutability, Type)
    #[allow(dead_code)]
    variables: HashMap<syn::Ident, VarInfo>,

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

    // (arg_name, arg_type_name)
    #[cfg(not(feature = "simulator"))]
    fn_args: Option<Vec<FnArg>>,
}

impl CodegenContext {
    pub fn new(variables: HashMap<syn::Ident, VarInfo>, show_asm: bool) -> CodegenContext {
        CodegenContext {
            v_registers: Registers::new("vector", vec![0]),
            var_regs: HashMap::default(),
            expr_regs: HashMap::default(),
            #[cfg(feature = "simulator")]
            expr_tokens: HashMap::default(),
            variables,
            #[cfg(not(feature = "simulator"))]
            v_config: None,
            show_asm,
            #[cfg(not(feature = "simulator"))]
            fn_args: None,
        }
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
            // x = y + x;
            Expression::Assign { .. } => {
                // === ASM ===
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx", in(reg) left.as_mut_ptr());
                // === Simulator ===
                // {
                //     x = #y.overflowing_add(#z).0
                // }

                tokens.extend(Some(context.gen_tokens(self, true, None, None, 0)?));
            }
            // x += y;
            Expression::AssignOp { .. } => {
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx");
                // asm!("xxx", in(reg) left.as_mut_ptr());
                tokens.extend(Some(context.gen_tokens(self, true, None, None, 0)?));
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
                tokens.extend(Some(context.gen_tokens(self, true, None, None, 0)?));
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
                tokens.extend(Some(context.gen_tokens(self, true, None, None, 0)?));
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
            Expression::Path(_) => {
                tokens.extend(Some(context.gen_tokens(self, true, None, None, 0)?));
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
                #[cfg(not(feature = "simulator"))]
                if let Some(fn_args) = context.fn_args.take() {
                    let mut args = fn_args
                        .into_iter()
                        .filter(|fn_arg| {
                            context
                                .variables
                                .get(&fn_arg.name)
                                .map(|info| !info.is_unused())
                                .expect("function input variable")
                        })
                        .filter_map(|fn_arg| {
                            let bit_length: u16 = match fn_arg.ty.0.type_name().as_deref() {
                                Some("U256") => 256,
                                Some("U512") => 512,
                                Some("U1024") => 1024,
                                _ => 0,
                            };
                            if bit_length > 0 {
                                Some((fn_arg, bit_length))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<_>>();
                    args.sort_by_key(|(_, bit_length)| *bit_length);

                    for (fn_arg, bit_length) in args {
                        context.update_vconfig(inner, bit_length);
                        // Load{256,512,1024}
                        let vreg = match context.v_registers.alloc() {
                            Some(vreg) => vreg,
                            None => {
                                *err = Some((
                                    fn_arg.span,
                                    anyhow!("not enough V register for function argument"),
                                ));
                                return;
                            }
                        };
                        // FIXME: t0 register may already used by Rust code
                        let inst = VInst::VleV {
                            width: bit_length,
                            vd: VReg::from_u8(vreg),
                            rs1: XReg::T0,
                            vm: false,
                        };
                        let [b0, b1, b2, b3] = inst.encode_bytes();
                        if context.show_asm {
                            let comment = format!("{} - {}", inst.encode_u32(), inst);
                            inner.extend(Some(quote! {
                                let _ = #comment;
                            }));
                        }
                        let var_ident = fn_arg.name;
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
                        inner.extend(Some(ts));
                        context.var_regs.insert(var_ident.clone(), vreg);
                    }
                }
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
        for attr in &self.attrs {
            if let syn::AttrStyle::Outer = attr.style {
                attr.to_tokens(tokens);
            }
        }
        self.vis.to_tokens(tokens);
        self.sig.to_tokens(tokens, context)?;
        #[cfg(not(feature = "simulator"))]
        {
            context.fn_args = Some(self.sig.inputs.clone());
        }
        self.block.to_tokens(tokens, context)?;
        Ok(())
    }
}
