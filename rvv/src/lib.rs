extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use rvv_assembler::{RvvBlock, RvvInst, ToStmts};
use syn::{
    fold::Fold, parse_macro_input, BinOp, Block, Expr, ExprAssign, ExprAssignOp, ExprBinary,
    ExprPath, FnArg, Ident, ItemFn, Local, Pat, PatIdent, PatType, Stmt, Type,
};

mod ast;
mod ast_transform;
mod code_gen;
mod type_checker;

use code_gen::Registers;

// use hacspec::ast;
// mod syn_to_hacspec;

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

struct RvvTransformer {
    // vector registers
    v_registers: Registers,
    // general registers
    x_registers: Registers,
    insts: Vec<RvvInst>,
}

impl Default for RvvTransformer {
    fn default() -> RvvTransformer {
        RvvTransformer {
            v_registers: Registers::new("vector", 32),
            x_registers: Registers::new("general", 32),
            insts: Vec::default(),
        }
    }
}

impl RvvTransformer {
    fn match_binary_op(
        &mut self,
        left_ident: &str,
        op: &BinOp,
        right_ident: &str,
        // x or v register
        dreg_opt: Option<u8>,
    ) -> Result<(RvvInst, u8), String> {
        // println!(">> {} {:?} {}", left_ident, op, right_ident);
        let (svreg1, _) = self.v_registers.get_reg(left_ident)?;
        let (svreg2, _) = self.v_registers.get_reg(right_ident)?;
        if let Some((dvreg, inst)) = match op {
            BinOp::Mul(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Mul256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Add(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Add256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Sub(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Sub256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Rem(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Rem256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::MulEq(_) => {
                let dvreg = svreg1;
                let inst = RvvInst::Mul256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::AddEq(_) => {
                let dvreg = svreg1;
                let inst = RvvInst::Add256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::SubEq(_) => {
                let dvreg = svreg1;
                let inst = RvvInst::Sub256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::RemEq(_) => {
                let dvreg = svreg1;
                let inst = RvvInst::Rem256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Shl(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Sll256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Shr(_) => {
                let dvreg = dreg_opt
                    .unwrap_or_else(|| self.v_registers.next_register().expect("no register"));
                let inst = RvvInst::Srl256(dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            BinOp::Ge(_) => {
                let dxreg = dreg_opt
                    .unwrap_or_else(|| self.x_registers.next_register().expect("no register"));
                let dvreg = self.v_registers.next_register().expect("no register");
                let inst = RvvInst::Ge256(dxreg, dvreg, svreg1, svreg2);
                Some((dvreg, inst))
            }
            _ => None,
        } {
            // Ok((Stmt::Expr(Expr::Verbatim(inst)), dvreg))
            Ok((inst, dvreg))
        } else {
            Err(format!("Unsupported binary op: {:?}", op))
        }
    }

    fn resolve_expr(
        &mut self,
        expr: &Box<Expr>,
        insts: &mut Vec<RvvInst>,
    ) -> Result<String, String> {
        match &**expr {
            Expr::Path(path) => Ok(extract_ident_name(path.path.get_ident().unwrap())),
            Expr::Binary(ExprBinary {
                left, op, right, ..
            }) => {
                let left_name = self.resolve_expr(left, insts)?;
                let right_name = self.resolve_expr(right, insts)?;
                let (inst, dvreg) =
                    self.match_binary_op(left_name.as_str(), op, right_name.as_str(), None)?;
                insts.push(inst);
                let (var_name, _) = self.v_registers.search_reg(dvreg).unwrap();
                Ok(var_name)
            }
            Expr::Paren(expr_paren) => self.resolve_expr(&expr_paren.expr, insts),
            _ => Err(format!("Unexpected expr: {:?}", expr)),
        }
    }

    fn handle_binary_op(
        &mut self,
        left: &Box<Expr>,
        op: &BinOp,
        right: &Box<Expr>,
        dreg_opt: Option<u8>,
    ) -> Result<(Vec<RvvInst>, u8), String> {
        let mut insts = Vec::new();
        let left_name = self.resolve_expr(left, &mut insts)?;
        let right_name = self.resolve_expr(right, &mut insts)?;
        let (inst, dvreg) =
            self.match_binary_op(left_name.as_str(), op, right_name.as_str(), dreg_opt)?;
        insts.push(inst);
        Ok((insts, dvreg))
    }

    fn return_expr(&mut self, dvreg: u8) -> RvvInst {
        RvvInst::Store256(dvreg, "__ret".to_string())
        // let store_inst = RvvInst::Store256(dvreg, "__ret".to_string()).to_asm();
        // let expr: Expr = parse_quote! {
        //     {
        //         let mut __ret = U256::default();
        //         #store_inst;
        //         __ret
        //     }
        // };
        // Stmt::Expr(expr)
    }

    // Path as a return value or a normal statement to ignore.
    fn handle_path(
        &mut self,
        ident: &Ident,
        origin_stmt: Option<&Stmt>,
    ) -> Result<Option<RvvInst>, String> {
        let (dvreg, is_fn_arg) = self.v_registers.get_reg(&extract_ident_name(ident))?;
        let rv = if is_fn_arg {
            Some(RvvInst::Store256(dvreg, extract_ident_name(ident)))
            // origin_stmt.cloned().map(|stmt| RvvInst::Source(stmt))
        } else {
            origin_stmt.map(|_| self.return_expr(dvreg))
        };
        Ok(rv)
    }
}

fn extract_ident_name(ident: &Ident) -> String {
    format!("{}", ident)
}

impl Fold for RvvTransformer {
    fn fold_fn_arg(&mut self, i: FnArg) -> FnArg {
        // println!("fn_arg: {:#?}", i);
        match &i {
            FnArg::Typed(PatType { pat, ty, .. }) => {
                if let Pat::Ident(pat_ident) = &**pat {
                    if let Type::Path(type_path) = &**ty {
                        if let Some(type_ident) = type_path.path.get_ident() {
                            if type_ident == "U256" {
                                let var_name = extract_ident_name(&pat_ident.ident);
                                let vreg = self
                                    .v_registers
                                    .next_register()
                                    .expect("No available register!");
                                // let inst = RvvInst::Load256(vreg, var_name.clone()).to_asm();
                                // let stmt: Stmt = Stmt::Expr(Expr::Verbatim(inst));
                                self.insts.push(RvvInst::Load256(vreg, var_name.clone()));
                                let is_fn_arg = true;
                                self.v_registers.insert(var_name, (vreg, is_fn_arg));
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
        // println!("block: {:#?}", block);

        let mut insts = self.insts.clone();
        // TODO: right now this only supports one expression in a block, add handling
        // for more statements later.
        for (idx, stmt) in block.stmts.iter().enumerate() {
            let is_last_stmt = idx == block.stmts.len() - 1;
            // println!("is last: {}, stmt: {:?}", is_last_stmt, stmt);
            match stmt {
                // a
                Stmt::Expr(Expr::Path(ExprPath { path, .. })) => {
                    let rv_stmt = if is_last_stmt { Some(stmt) } else { None };
                    if let Some(new_inst) = self
                        .handle_path(&path.segments.first().unwrap().ident, rv_stmt)
                        .unwrap()
                    {
                        insts.push(new_inst);
                    }
                }
                // let x = a * b
                Stmt::Local(Local { pat, init, .. }) => {
                    if let (Pat::Ident(PatIdent { ident, .. }), Some((_, expr))) = (pat, init) {
                        if let Expr::Binary(ExprBinary {
                            left, op, right, ..
                        }) = &**expr
                        {
                            let var_name = extract_ident_name(ident);
                            if self.v_registers.mapping.contains_key(&var_name) {
                                panic!("Variable shadowing is not allowed in current macro");
                            }
                            let vreg = self
                                .v_registers
                                .next_register()
                                .expect("No available register!");
                            // println!(
                            //     "[register] mapping variable {} to V register {}",
                            //     var_name, vreg
                            // );
                            self.v_registers.insert(var_name, (vreg, false));
                            let (new_insts, _dvreg) =
                                self.handle_binary_op(left, op, right, Some(vreg)).unwrap();
                            insts.extend(new_insts);
                        } else {
                            panic!("Unsupported local expr: {:?}", expr);
                        }
                    } else {
                        panic!("Unsupported local stmt: {:?}", stmt);
                    }
                }
                // a * b
                Stmt::Expr(Expr::Binary(ExprBinary {
                    left, op, right, ..
                })) => {
                    let (new_insts, dvreg) = self.handle_binary_op(left, op, right, None).unwrap();
                    insts.extend(new_insts);
                    if is_last_stmt {
                        insts.push(self.return_expr(dvreg));
                    }
                }
                // a *= c
                Stmt::Semi(
                    Expr::AssignOp(ExprAssignOp {
                        left, op, right, ..
                    }),
                    _semi,
                ) => {
                    let (new_insts, _dvreg) = self.handle_binary_op(left, op, right, None).unwrap();
                    insts.extend(new_insts);
                }
                // a = a * c
                Stmt::Semi(Expr::Assign(ExprAssign { left, right, .. }), _semi) => {
                    if let (
                        Expr::Path(path),
                        Expr::Binary(ExprBinary {
                            left, op, right, ..
                        }),
                    ) = (&**left, &**right)
                    {
                        let var_name = extract_ident_name(path.path.get_ident().unwrap());
                        let (vreg, _) = self.v_registers.get_reg(&var_name).unwrap();
                        let (new_insts, _dvreg) =
                            self.handle_binary_op(left, op, right, Some(vreg)).unwrap();
                        insts.extend(new_insts);
                    } else {
                        unimplemented!();
                    }
                }
                _ => {
                    panic!("Unmatched stmt: {}", stmt.to_token_stream());
                }
            }
        }

        let stmts = RvvBlock::new(insts).to_stmts();
        Block {
            brace_token: block.brace_token,
            stmts,
        }
    }
}

#[proc_macro_attribute]
pub fn rvv_vector(attr: TokenStream, item: TokenStream) -> TokenStream {
    // println!("attr: \"{}\"", attr.to_string());
    // println!("item: \"{}\"", item.to_string());
    let input = parse_macro_input!(item as ItemFn);
    let mut transformer = RvvTransformer::default();
    let output = transformer.fold_item_fn(input);
    TokenStream::from(quote!(#output))
}
