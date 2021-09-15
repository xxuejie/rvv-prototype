extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Expr, FnArg, ItemFn, fold::{Fold}};

struct RvvTransformer(u8);

impl Fold for RvvTransformer {
    fn fold_fn_arg(&mut self, i: FnArg) -> FnArg {
        self.0 += 1;
        println!("Folding fn arg: {:?}", i);
        i
    }

    fn fold_expr(&mut self, e: Expr) -> Expr {
        println!("Folding expr: {:#?}", e);
        e
    }

    // fn fold_block(&mut self, _block: Block) -> Block {
        // let i = self.0;
        // let block: Block = parse_quote! {
            // {
    	          // unsafe {
    		            // asm!(".byte 0xba, {}, 0x0, 0x0, 0x0", const #i);
    	          // }
    	          // unimplemented!()
    	      // }
        // };
        // block
    // }
}

#[proc_macro_attribute]
pub fn rvv_vector(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let mut transformer = RvvTransformer(10);

    let output = transformer.fold_item_fn(input);

    TokenStream::from(quote!(#output))
}
