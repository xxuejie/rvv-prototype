mod code_gen_mixed;
mod code_gen_partial;

use std::convert::TryFrom;

use proc_macro2::TokenStream;
use quote::quote;

use crate::ast::ItemFn;
use crate::code_gen::{CodegenContext, ToTokenStream};
use crate::type_checker::{CheckerContext, TypeChecker};
use crate::SpannedError;

fn rvv_codegen(item: TokenStream, show_asm: bool) -> Result<TokenStream, SpannedError> {
    let input: syn::ItemFn = syn::parse2(item).unwrap();
    let mut out = ItemFn::try_from(&input)?;
    let mut checker_context = CheckerContext::default();
    out.check_types(&mut checker_context)?;

    println!("[variables]:");
    for (ident, info) in &checker_context.variables {
        if info.mut_token.is_some() {
            println!(
                "  [mut {:6}] => {:?} (lifetime = expr[{}] to expr[{}], unused: {})",
                ident,
                info.ty.as_ref().map(|ty| &ty.0),
                info.start_expr_id,
                info.end_expr_id,
                info.is_unused(),
            );
        } else {
            println!(
                "  [{:10}] => {:?} (lifetime = expr[{}] to expr[{}], unused: {})",
                ident,
                info.ty.as_ref().map(|ty| &ty.0),
                info.start_expr_id,
                info.end_expr_id,
                info.is_unused(),
            );
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

fn run_rvv_test(input: TokenStream, expected_output: TokenStream) {
    let output = rvv_codegen(input, true).unwrap();
    assert_eq!(output.to_string(), expected_output.to_string());
}
