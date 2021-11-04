use std::collections::HashMap;

use anyhow::{anyhow, bail, Error};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::token;

use rvv_assembler::{Imm, Ivi, Ivv, Ivx, Uimm, VConfig, VInst, VReg, Vlmul, Vtypei, XReg};

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Statement, Type,
    TypedExpression,
};

// =============================
// ==== impl ToTokens for T ====
// =============================

#[derive(Default)]
pub struct Registers {
    pub category: &'static str,
    pub max_number: u8,
    pub last_number: u8,
    // ident_name => (register_number, is_function_argument)
    pub mapping: HashMap<String, (u8, bool)>,
}

impl Registers {
    pub fn new(category: &'static str, max_number: u8) -> Registers {
        Registers {
            category,
            max_number,
            last_number: 0,
            mapping: HashMap::default(),
        }
    }

    pub fn next_register(&mut self) -> Option<u8> {
        if self.last_number < self.max_number {
            self.last_number += 1;
            let tmp_var_name = format!("__tmp_{}_var{}", self.category, self.last_number);
            self.mapping.insert(tmp_var_name, (self.last_number, false));
            return Some(self.last_number);
        }
        None
    }

    pub fn search_reg(&self, reg: u8) -> Option<(String, bool)> {
        for (name, (number, is_fn_arg)) in &self.mapping {
            if *number == reg {
                return Some((name.clone(), *is_fn_arg));
            }
        }
        None
    }

    pub fn get_reg(&self, var_name: &str) -> Result<(u8, bool), String> {
        self.mapping
            .get(var_name)
            .cloned()
            .ok_or_else(|| format!("Unrecognized {} variable name: {}", self.category, var_name))
    }

    pub fn insert(&mut self, var_name: String, value: (u8, bool)) {
        self.mapping.insert(var_name, value);
    }
}

#[derive(Default)]
pub struct Context {
    // vector registers
    v_registers: Registers,
    // general registers
    x_registers: Registers,

    variables: HashMap<syn::Ident, (bool, Type)>,
    // [When update v_config]
    //   1. When first vector instruction used update v_config and insert asm!()
    //   2. When vector config changed:
    //     * reset x_registers
    //     * dump all x register data to memory
    //     * update v_config and insert asm!()
    v_config: Option<VConfig>,
}

pub trait ToTokenStream {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context);
    fn to_token_stream(&self, context: &mut Context) -> TokenStream {
        let mut tokens = TokenStream::new();
        self.to_tokens(&mut tokens, context);
        tokens
    }
    fn into_token_stream(self, context: &mut Context) -> TokenStream
    where
        Self: Sized,
    {
        self.to_token_stream(context)
    }
}

impl ToTokenStream for ReturnType {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            ReturnType::Default => {}
            ReturnType::Type(ty) => {
                token::RArrow::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
        }
    }
}
impl ToTokenStream for BareFnArg {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        if let Some(ident) = self.name.as_ref() {
            ident.to_tokens(tokens);
            token::Colon::default().to_tokens(tokens);
        }
        self.ty.to_tokens(tokens, context);
    }
}
impl ToTokenStream for Type {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Type::Array { elem, len } => {
                token::Bracket::default().surround(tokens, |inner| {
                    elem.to_tokens(inner, context);
                    token::Semi::default().to_tokens(inner);
                    len.to_tokens(inner, context);
                });
            }
            Type::BareFn { inputs, output } => {
                token::Fn::default().to_tokens(tokens);
                token::Paren::default().surround(tokens, |inner| {
                    for input in inputs {
                        input.to_tokens(inner, context);
                    }
                });
                output.to_tokens(tokens, context);
            }
            Type::Path(path) => {
                path.to_tokens(tokens);
            }
            Type::Reference {
                lifetime,
                mutability,
                elem,
            } => {
                token::And::default().to_tokens(tokens);
                if let Some(lifetime) = lifetime {
                    lifetime.to_tokens(tokens);
                }
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                elem.to_tokens(tokens, context);
            }
            Type::Slice(ty) => {
                token::Bracket::default().surround(tokens, |inner| {
                    ty.to_tokens(inner, context);
                });
            }
            Type::Tuple(types) => token::Paren::default().surround(tokens, |inner| {
                for (idx, ty) in types.iter().enumerate() {
                    ty.to_tokens(inner, context);
                    if idx != types.len() - 1 {
                        token::Comma::default().to_tokens(inner);
                    }
                }
            }),
        }
    }
}
impl ToTokenStream for Pattern {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Pattern::Ident { mutability, ident } => {
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                ident.to_tokens(tokens);
            }
            Pattern::Type { pat, ty } => {
                pat.to_tokens(tokens, context);
                token::Colon::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
            Pattern::Range { lo, limits, hi } => {
                lo.to_tokens(tokens, context);
                match limits {
                    syn::RangeLimits::HalfOpen(inner) => {
                        inner.to_tokens(tokens);
                    }
                    syn::RangeLimits::Closed(inner) => {
                        inner.to_tokens(tokens);
                    }
                }
                hi.to_tokens(tokens, context);
            }
            Pattern::Path(path) => {
                path.to_tokens(tokens);
            }
            Pattern::Wild => {
                token::Underscore::default().to_tokens(tokens);
            }
        }
    }
}
impl ToTokenStream for Expression {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Expression::Array(arr) => {
                arr.to_tokens(tokens);
            }
            Expression::Assign { left, right } => {
                left.to_tokens(tokens, context);
                token::Eq::default().to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::AssignOp { left, op, right } => {
                // FIXME: use rvv assembler
                left.to_tokens(tokens, context);
                op.to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::Binary { left, op, right } => {
                // FIXME: use rvv assembler
                left.to_tokens(tokens, context);
                op.to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::Call { func, args } => {
                func.to_tokens(tokens, context);
                token::Paren::default().surround(tokens, |inner| {
                    for (idx, ty) in args.iter().enumerate() {
                        ty.to_tokens(inner, context);
                        if idx != args.len() - 1 {
                            token::Comma::default().to_tokens(inner);
                        }
                    }
                });
            }
            Expression::MethodCall {
                receiver,
                method,
                args,
            } => {
                // FIXME: use rvv assembler
                receiver.to_tokens(tokens, context);
                token::Dot::default().to_tokens(tokens);
                method.to_tokens(tokens);
                token::Paren::default().surround(tokens, |inner| {
                    for (idx, ty) in args.iter().enumerate() {
                        ty.to_tokens(inner, context);
                        if idx != args.len() - 1 {
                            token::Comma::default().to_tokens(inner);
                        }
                    }
                });
            }
            Expression::Macro(mac) => {
                mac.to_tokens(tokens);
            }
            Expression::Unary { op, expr } => {
                op.to_tokens(tokens);
                expr.to_tokens(tokens, context);
            }
            Expression::Field { base, member } => {
                base.to_tokens(tokens, context);
                token::Dot::default().to_tokens(tokens);
                member.to_tokens(tokens);
            }
            Expression::Cast { expr, ty } => {
                expr.to_tokens(tokens, context);
                token::As::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
            Expression::Repeat { expr, len } => {
                token::Bracket::default().surround(tokens, |inner| {
                    expr.to_tokens(inner, context);
                    token::Semi::default().to_tokens(inner);
                    len.to_tokens(inner, context);
                });
            }
            Expression::Lit(lit) => {
                lit.to_tokens(tokens);
            }
            Expression::Paren(expr) => {
                token::Paren::default().surround(tokens, |inner| {
                    expr.to_tokens(inner, context);
                });
            }
            Expression::Reference { mutability, expr } => {
                token::And::default().to_tokens(tokens);
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                expr.to_tokens(tokens, context);
            }
            Expression::Index { expr, index } => {
                expr.to_tokens(tokens, context);
                token::Bracket::default().surround(tokens, |inner| {
                    index.to_tokens(inner, context);
                });
            }
            Expression::Path(path) => {
                path.to_tokens(tokens);
            }
            Expression::Break => {
                token::Break::default().to_tokens(tokens);
            }
            Expression::Continue => {
                token::Continue::default().to_tokens(tokens);
            }
            Expression::Return(expr_opt) => {
                token::Return::default().to_tokens(tokens);
                if let Some(expr) = expr_opt.as_ref() {
                    expr.to_tokens(tokens, context);
                }
            }
            Expression::Block(block) => {
                block.to_tokens(tokens, context);
            }
            Expression::If {
                cond,
                then_branch,
                else_branch,
            } => {
                token::If::default().to_tokens(tokens);
                cond.to_tokens(tokens, context);
                then_branch.to_tokens(tokens, context);
                if let Some(expr) = else_branch.as_ref() {
                    token::Else::default().to_tokens(tokens);
                    expr.to_tokens(tokens, context);
                }
            }
            Expression::Range { from, limits, to } => {
                if let Some(expr) = from.as_ref() {
                    expr.to_tokens(tokens, context);
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
                    expr.to_tokens(tokens, context);
                }
            }
            Expression::Loop(body) => {
                token::Loop::default().to_tokens(tokens);
                body.to_tokens(tokens, context);
            }
            Expression::ForLoop { pat, expr, body } => {
                token::For::default().to_tokens(tokens);
                pat.to_tokens(tokens, context);
                token::In::default().to_tokens(tokens);
                expr.to_tokens(tokens, context);
                body.to_tokens(tokens, context);
            }
        }
    }
}

impl ToTokenStream for Statement {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Statement::Local { pat, init } => {
                token::Let::default().to_tokens(tokens);
                pat.to_tokens(tokens, context);
                token::Eq::default().to_tokens(tokens);
                init.to_tokens(tokens, context);
                token::Semi::default().to_tokens(tokens);
            }
            Statement::Expr(expr) => {
                expr.to_tokens(tokens, context);
            }
            Statement::Semi(expr) => {
                expr.to_tokens(tokens, context);
                token::Semi::default().to_tokens(tokens);
            }
        }
    }
}
impl ToTokenStream for Block {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        token::Brace::default().surround(tokens, |inner| {
            for stmt in &self.stmts {
                stmt.to_tokens(inner, context);
            }
        })
    }
}
impl ToTokenStream for FnArg {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        if self.mutability {
            token::Mut::default().to_tokens(tokens);
        }
        self.name.to_tokens(tokens);
        token::Colon::default().to_tokens(tokens);
        self.ty.to_tokens(tokens, context);
    }
}
impl ToTokenStream for Signature {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        token::Fn::default().to_tokens(tokens);
        self.ident.to_tokens(tokens);
        token::Paren::default().surround(tokens, |inner| {
            for (idx, input) in self.inputs.iter().enumerate() {
                input.to_tokens(inner, context);
                if idx != self.inputs.len() - 1 {
                    token::Comma::default().to_tokens(inner);
                }
            }
        });
        self.output.to_tokens(tokens, context);
    }
}
impl ToTokenStream for ItemFn {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        self.vis.to_tokens(tokens);
        self.sig.to_tokens(tokens, context);
        self.block.to_tokens(tokens, context);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn rvv_test(item: TokenStream) -> TokenStream {
        let input: syn::ItemFn = syn::parse2(item).unwrap();
        let out = ItemFn::try_from(&input).unwrap();
        let mut tokens = TokenStream::new();
        let mut context = Context::default();
        out.to_tokens(&mut tokens, &mut context);
        println!("out: {:#?}", out);
        TokenStream::from(quote!(#tokens))
    }

    #[test]
    fn test_simple() {
        let input = quote! {
            fn simple(x: u32, mut y: u64, z: &mut u64) -> u128 {
                *z += 3;
                if z > 5 {
                    y = y * 6;
                } else {
                    y = y * 3;
                }
                y = y >> 1;
                for i in 0..6 {
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
        let output = rvv_test(input);
        let output_string = output.to_string();
        println!("[otuput]: {}", output_string);
        assert_eq!(input_string, output_string);
    }

    #[test]
    fn test_u256() {
        let input = quote! {
            fn comp_u256(x: U256, y: U256) -> U256 {
                let mut z: U256 = x + y * x;
                z = z + z;
                z
            }
        };
        println!("[input ]: {}", input);
        let output = rvv_test(input);
        println!("[otuput]: {}", output);
    }
}
