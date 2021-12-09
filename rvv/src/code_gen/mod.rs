use std::collections::HashMap;

#[cfg(not(feature = "simulator"))]
use anyhow::anyhow;
#[cfg(not(feature = "simulator"))]
use quote::quote;

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::token;

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Span, Statement,
    Type, TypedExpression, WithSpan,
};
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

    // (arg_name, arg_type_name)
    #[cfg(not(feature = "simulator"))]
    fn_args: Option<Vec<FnArg>>,
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
                #[cfg(not(feature = "simulator"))]
                if let Some(fn_args) = context.fn_args.take() {
                    let mut args = fn_args
                        .into_iter()
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
                        let vreg = match context.v_registers.next_register() {
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

#[cfg(test)]
mod test {
    use quote::quote;
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
                unsafe {
                    asm!("li t0, 1", ".byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 14u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) x.as_ref().as_ptr(), const 7u8, const 208u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) y.as_ref().as_ptr(), const 135u8, const 208u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) z.as_ref().as_ptr(), const 7u8, const 209u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) w.as_ref().as_ptr(), const 135u8, const 209u8, const 2u8, const 16u8 ,)
                }
                let x_bytes = x.to_le_bytes();
                let j = {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 162u8, const 32u8, const 148u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 162u8, const 65u8, const 128u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 131u8, const 2u8, const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 211u8, const 2u8, const 16u8 ,)
                    }
                    unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
                };
                if {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 3u8, const 16u8, const 104u8 ,)
                    }
                    let tmp_bool_t0: i64;
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", "mv {4}, t0", const 215u8, const 162u8, const 120u8, const 64u8, out (reg) tmp_bool_t0 ,)
                    }
                    tmp_bool_t0 == 0
                } && {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 4u8, const 17u8, const 96u8 ,)
                    }
                    let tmp_bool_t0: i64;
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", "mv {4}, t0", const 215u8, const 162u8, const 136u8, const 64u8, out (reg) tmp_bool_t0 ,)
                    }
                    tmp_bool_t0 == 0
                } {
                    z = {
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 132u8, const 32u8, const 40u8 ,)
                        }
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 133u8, const 4u8, const 36u8 ,)
                        }
                        let mut tmp_rvv_vector_buf = [0u8; 32usize];
                        unsafe {
                            asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 213u8, const 2u8, const 16u8 ,)
                        }
                        unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
                    };
                }
                z = {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 133u8, const 0u8, const 8u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 38u8, const 176u8, const 148u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 214u8, const 2u8, const 16u8 ,)
                    }
                    unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
                };
                let abc = 3456;
                z = ({
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) j.as_ref().as_ptr(), const 135u8, const 214u8, const 2u8, const 16u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 7u8, const 16u8, const 8u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 39u8, const 215u8, const 148u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 136u8, const 23u8, const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 216u8, const 2u8, const 16u8 ,)
                    }
                    unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
                });
                z = {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 8u8, const 33u8, const 0u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 32usize];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 167u8, const 216u8, const 2u8, const 16u8 ,)
                    }
                    unsafe { core::mem::transmute::<[u8; 32usize], U256>(tmp_rvv_vector_buf) }
                };
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 128u8, const 32u8, const 8u8 ,)
                };
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 160u8, const 32u8, const 148u8 ,)
                };
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 128u8, const 32u8, const 0u8 ,)
                };
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 160u8, const 32u8, const 136u8 ,)
                };
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 128u8, const 32u8, const 160u8 ,)
                };
                let zero = U256::zero();
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) zero.as_ref().as_ptr(), const 7u8, const 217u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 41u8, const 41u8, const 128u8 ,)
                };
                z
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
        let output = rvv_test(input, false).unwrap();
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
                unsafe {
                    asm!("li t0, 1", ".byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 15u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) x.as_ref().as_ptr(), const 7u8, const 240u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) y.as_ref().as_ptr(), const 135u8, const 240u8, const 2u8, const 16u8 ,)
                }
                let z = {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 129u8, const 0u8, const 0u8 ,)
                    }
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 33u8, const 32u8, const 148u8 ,)
                    }
                    let mut tmp_rvv_vector_buf = [0u8; 128usize];
                    unsafe {
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 167u8, const 241u8, const 2u8, const 16u8 ,)
                    }
                    unsafe { core::mem::transmute::<[u8 ; 128usize], U1024>(tmp_rvv_vector_buf) }
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

        #[cfg(feature = "simulator")]
        let expected_output = quote! {
            fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
                let x_tuple = a.wrapping_add (b).overflowing_mul(c);
                let x = x_tuple.0 ;
                let z_opt = x.checked_div(d) ;
                let z : U1024 = z.unwrap() ;
                z
            }
        };

        #[cfg(not(feature = "simulator"))]
        let expected_output = quote! {
            fn comp_u1024(a: U1024, b: U1024, c: U1024, d: U1024) -> U1024 {
                unsafe {
                    asm!("li t0, 1", ".byte {0}, {1}, {2}, {3}", const 87u8, const 240u8, const 130u8, const 15u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) a.as_ref().as_ptr(), const 7u8, const 240u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) b.as_ref().as_ptr(), const 135u8, const 240u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) c.as_ref().as_ptr(), const 7u8, const 241u8, const 2u8, const 16u8 ,)
                }
                unsafe {
                    asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) d.as_ref().as_ptr(), const 135u8, const 241u8, const 2u8, const 16u8 ,)
                }
                let x_tuple = {
                    unsafe {
                        asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 130u8, const 0u8, const 0u8 ,)
                    }
                    {
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 34u8, const 65u8, const 148u8 ,)
                        }
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 87u8, const 51u8, const 80u8, const 100u8 ,)
                        }
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 162u8, const 104u8, const 64u8 ,)
                        }
                        let tmp_bool_t0: i64;
                        let mut tmp_rvv_vector_buf = [0u8; 128usize];
                        unsafe {
                            asm!("mv {0}, t0", "mv t2, {1}", ".byte {2}, {3}, {4}, {5}", out (reg) tmp_bool_t0, in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 167u8, const 242u8, const 3u8, const 16u8 ,)
                        }
                        let tmp_uint_rv =
                            unsafe { core::mem::transmute::<[u8; 128usize], U1024>(tmp_rvv_vector_buf) };
                        if tmp_bool_t0 == 0 {
                            let tmp_bool_t1: i64;
                            unsafe {
                                asm!(".byte {0}, {1}, {2}, {3}", ".byte {4}, {5}, {6}, {7}", ".byte {8}, {9}, {10}, {11}", "mv {12}, t1", const 87u8, const 35u8, const 82u8, const 128u8, const 87u8, const 3u8, const 97u8, const 100u8, const 87u8, const 163u8, const 104u8, const 64u8, out (reg) tmp_bool_t1 ,)
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
                        asm!("mv t0, {0}", ".byte {1}, {2}, {3}, {4}", in (reg) x.as_ref().as_ptr(), const 135u8, const 243u8, const 2u8, const 16u8 ,)
                    }
                    {
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 52u8, const 48u8, const 96u8 ,)
                        }
                        unsafe {
                            asm!(".byte {0}, {1}, {2}, {3}", const 215u8, const 162u8, const 152u8, const 64u8 ,)
                        }
                        let tmp_bool_var: i64;
                        unsafe { asm!("mv {0}, t0", out (reg) tmp_bool_var ,) }
                        if tmp_bool_var == 0 {
                            None
                        } else {
                            let mut tmp_rvv_vector_buf = [0u8; 128usize];
                            unsafe {
                                asm!(".byte {0}, {1}, {2}, {3}", "mv t1, {4}", ".byte {5}, {6}, {7}, {8}", const 87u8, const 164u8, const 113u8, const 128u8, in (reg) tmp_rvv_vector_buf.as_mut_ptr(), const 39u8, const 116u8, const 3u8, const 16u8 ,)
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
}
