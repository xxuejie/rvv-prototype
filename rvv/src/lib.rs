extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use rvv_assembler::{RvvInst, ToAsm};
use std::collections::HashMap;
use syn::{
    fold::Fold, parse_macro_input, parse_quote, BinOp, Block, Expr, ExprBinary, FnArg, Ident,
    ItemFn, Pat, PatType, Stmt, Type,
};

#[derive(Default)]
struct RvvTransformer {
    last_register: u8,
    mapping: HashMap<String, u8>,
    prefix_stmts: Vec<Stmt>,
}

impl RvvTransformer {
    fn next_register(&mut self) -> Option<u8> {
        if self.last_register < 32 {
            self.last_register += 1;
            return Some(self.last_register);
        }
        None
    }
}

fn extract_ident_name(ident: &Ident) -> String {
    format!("{}", ident).to_string()
}

impl Fold for RvvTransformer {
    fn fold_fn_arg(&mut self, i: FnArg) -> FnArg {
        match &i {
            FnArg::Typed(PatType { pat, ty, .. }) => {
                if let Pat::Ident(pat_ident) = &**pat {
                    if let Type::Path(type_path) = &**ty {
                        if let Some(type_ident) = type_path.path.get_ident() {
                            if type_ident == "U256" {
                                let var_name = extract_ident_name(&pat_ident.ident);
                                let vreg = self.next_register().expect("No available register!");
                                let inst = RvvInst::Load256(vreg, var_name.clone()).to_asm();
                                let stmt: Stmt = parse_quote! {
                                    #inst;
                                };
                                self.prefix_stmts.push(stmt);
                                self.mapping.insert(var_name, vreg);
                            }
                        }
                    }
                }
            }
            _ => (),
        };
        i
    }

    fn fold_block(&mut self, block: Block) -> Block {
        let mut stmts = self.prefix_stmts.clone();

        // TODO: right now this only supports one expression in a block, add handling
        // for more statements later.
        if block.stmts.len() != 1 {
            unimplemented!();
        }
        if let Stmt::Expr(expr) = &block.stmts[0] {
            let mut matched = false;
            match expr {
                Expr::Binary(ExprBinary {
                    left, op, right, ..
                }) => {
                    if let Expr::Path(left_path) = &**left {
                        if let Some(left_ident) = left_path.path.get_ident() {
                            if let Expr::Path(right_path) = &**right {
                                if let Some(right_ident) = right_path.path.get_ident() {
                                    if let BinOp::Mul(_) = op {
                                        let svreg1 = self.mapping[&extract_ident_name(left_ident)];
                                        let svreg2 = self.mapping[&extract_ident_name(right_ident)];
                                        let dvreg = self.next_register().expect("no register");
                                        let mul_inst =
                                            RvvInst::Mul256(dvreg, svreg1, svreg2).to_asm();
                                        let store_inst =
                                            RvvInst::Store256(dvreg, "__ret".to_string()).to_asm();

                                        let expr: Expr = parse_quote! {
                                            {
                                                #mul_inst;
                                                let mut __ret = U256::default();
                                                #store_inst;
                                                __ret
                                            }
                                        };
                                        stmts.push(Stmt::Expr(expr));

                                        matched = true;
                                    }
                                }
                            }
                        }
                    }
                }
                _ => (),
            };
            if !matched {
                panic!("Unmatched case! Needs more development work!");
            }
        } else {
            unimplemented!();
        }

        Block {
            brace_token: block.brace_token,
            stmts,
        }
    }
}

#[proc_macro_attribute]
pub fn rvv_vector(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let mut transformer = RvvTransformer::default();

    let output = transformer.fold_item_fn(input);

    TokenStream::from(quote!(#output))
}
