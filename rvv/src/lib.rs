#![feature(proc_macro_diagnostic)]

extern crate proc_macro;
use anyhow::anyhow;
use proc_macro::{Diagnostic, Level, TokenStream};
use quote::quote;
use std::convert::TryFrom;
use syn::{parse_macro_input, ItemFn};

mod ast;
mod ast_transform;
mod code_gen;
mod type_checker;

use code_gen::{CodegenContext, ToTokenStream};
use type_checker::{CheckerContext, TypeChecker};

// TODO: Support U256 [ops](https://doc.rust-lang.org/core/ops/index.html):
//   Add          The addition operator +. (NOTE: actually wrapping_add)
//   AddAssign    The addition assignment operator +=.
//   BitAnd       The bitwise AND operator &.
//   BitAndAssign The bitwise AND assignment operator &=.
//   BitOr        The bitwise OR operator |.
//   BitOrAssign  The bitwise OR assignment operator |=.
//   BitXor       The bitwise XOR operator ^.
//   BitXorAssign The bitwise XOR assignment operator ^=.
//   Div          The division operator /.
//   DivAssign    The division assignment operator /=.
//   Mul          The multiplication operator *.
//   MulAssign    The multiplication assignment operator *=.
//   Neg          The unary negation operator -.
//   Not          The unary logical negation operator !.
//   Rem          The remainder operator %.
//   RemAssign    The remainder assignment operator %=.
//   Shl          The left shift operator <<. Note that because this trait is
//                  implemented for all integer types with multiple right-hand-side types, Rust’s
//                  type checker has special handling for _ << _, setting the result type for
//                  integer operations to the type of the left-hand-side operand. This means that
//                  though a << b and a.shl(b) are one and the same from an evaluation standpoint,
//                  they are different when it comes to type inference.
//   ShlAssign    The left shift assignment operator <<=.
//   Shr          The right shift operator >>. Note that because this trait is
//                  implemented for all integer types with multiple right-hand-side types, Rust’s
//                  type checker has special handling for _ >> _, setting the result type for
//                  integer operations to the type of the left-hand-side operand. This means that
//                  though a >> b and a.shr(b) are one and the same from an evaluation standpoint,
//                  they are different when it comes to type inference.
//   ShrAssign    The right shift assignment operator >>=.
//   Sub          The subtraction operator -. (NOTE: actually wrapping_sub)
//   SubAssign    The subtraction assignment operator -=.

// TODO: Support U256 [cmp](https://doc.rust-lang.org/core/cmp/index.html)
//   Eq           Trait for equality comparisons which are equivalence relations.
//   Ord          Trait for types that form a total order.
//   PartialEq    Trait for equality comparisons which are partial equivalence relations.
//   PartialOrd   Trait for values that can be compared for a sort-order.

pub(crate) type SpannedError = (ast::Span, anyhow::Error);

fn rvv_vector_inner(
    attr_opt: Option<syn::Path>,
    input: ItemFn,
) -> Result<TokenStream, SpannedError> {
    let show_asm = if let Some(attr) = attr_opt {
        if attr.is_ident("show_asm") {
            true
        } else {
            let ident = attr.get_ident().unwrap();
            return Err((
                ident.span().into(),
                anyhow!("unexpected attribute: {}", ident),
            ));
        }
    } else {
        false
    };

    let mut out = ast::ItemFn::try_from(&input)?;
    let mut checker_context = CheckerContext::default();
    out.check_types(&mut checker_context)?;
    let mut tokens = proc_macro2::TokenStream::new();
    let mut codegen_context = CodegenContext::new(checker_context.variables, show_asm);
    out.to_tokens(&mut tokens, &mut codegen_context)?;
    Ok(TokenStream::from(quote!(#tokens)))
}

#[proc_macro_attribute]
pub fn rvv_vector(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = if attr.is_empty() {
        None
    } else {
        Some(parse_macro_input!(attr as syn::Path))
    };
    let input = parse_macro_input!(item as ItemFn);
    match rvv_vector_inner(attr, input) {
        Ok(tokens) => tokens,
        Err((span, message)) => {
            Diagnostic::spanned(span.0.unwrap(), Level::Error, message.to_string()).emit();
            TokenStream::new()
        }
    }
}
