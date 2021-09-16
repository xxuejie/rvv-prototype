extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use rvv_assembler::{RvvInst, ToAsm};
use std::collections::HashMap;
use syn::{fold::Fold, parse_macro_input, parse_quote, Block, FnArg, ItemFn};

struct RvvTransformer {}

impl Fold for RvvTransformer {
    fn fold_fn_arg(&mut self, i: FnArg) -> FnArg {
        self.0 += 1;
        println!("Folding fn arg: {:?}", i);
        i
    }

    fn fold_block(&mut self, block: Block) -> Block {
        let inst = RvvInst::Mul256(3, 4, 5);
        let a = inst.to_asm();
        let block: Block = parse_quote! {
            {
                #a
                unimplemented!()
            }
        };

        block
    }
}

#[proc_macro_attribute]
pub fn rvv_vector(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let mut transformer = RvvTransformer(10);

    let output = transformer.fold_item_fn(input);

    TokenStream::from(quote!(#output))
}
