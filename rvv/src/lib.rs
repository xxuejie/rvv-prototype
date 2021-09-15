extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{fold::Fold, parse_macro_input, Block, FnArg, ItemFn};

struct RvvTransformer(u8);

impl Fold for RvvTransformer {
    fn fold_fn_arg(&mut self, i: FnArg) -> FnArg {
        self.0 += 1;
        println!("Folding fn arg: {:?}", i);
        i
    }

    fn fold_block(&mut self, block: Block) -> Block {
        // let i = self.0;
        // let block: Block = parse_quote! {
            // {
    	          // unsafe {
    		            // asm!(".byte 0xba, {}, 0x0, 0x0, 0x0", const #i);
    	          // }
    	          // unimplemented!()
    	      // }
        // };
        println!("Folding block: {:#?}", block);
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
