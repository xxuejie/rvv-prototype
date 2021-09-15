extern crate proc_macro;
use proc_macro::TokenStream;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn rvv_vector(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item2 = item.clone();
    let input = parse_macro_input!(item as ItemFn);
    println!("Parsed item: {:#?}", input);

    item2
}
