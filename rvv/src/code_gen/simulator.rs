use anyhow::anyhow;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use super::RegInfo;
use super::{CodegenContext, OpCategory, ToTokenStream};
use crate::ast::{Expression, TypedExpression};
use crate::SpannedError;

impl CodegenContext {
    pub(crate) fn gen_tokens(
        &mut self,
        expr: &TypedExpression,
        top_level: bool,
        extra_bind_id: Option<usize>,
        _exists_vd: Option<u8>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        let (left, op, right, is_assign) = match &expr.expr.0 {
            Expression::Assign { left, right, .. } => {
                let mut tokens = TokenStream::new();
                left.to_tokens(&mut tokens, self)?;
                syn::token::Eq::default().to_tokens(&mut tokens);
                right.to_tokens(&mut tokens, self)?;
                return Ok(tokens)
            }
            Expression::AssignOp { left, op, right } => (left, op, right, true),
            Expression::Binary { left, op, right } => (left, op, right, false),
            Expression::Path(path) => {
                let mut tokens = TokenStream::new();
                path.to_tokens(&mut tokens);
                return Ok(tokens);
            }
            Expression::MethodCall { receiver, method, args, .. } => {
                return self.default_method_call_codegen(receiver, method, args);
            }
            Expression::Paren { expr: sub_expr, .. } => {
                let ts = self.gen_tokens(&*sub_expr, top_level, Some(expr.id), None, bit_length)?;
                return Ok(quote! {(#ts)});
            }
            _  => return Err((expr.expr.1, anyhow!("invalid expression, inner expression must be simple variable name or binary op"))),
        };
        if !top_level && is_assign {
            return Err((
                expr.expr.1,
                anyhow!("assign op in sub-expression is forbidden"),
            ));
        }

        let mut tokens = TokenStream::new();

        if top_level {
            let left_type_name = left.type_name();
            let right_type_name = right.type_name();
            match (left_type_name.as_deref(), right_type_name.as_deref()) {
                (Some("U256"), Some("U256")) => {
                    bit_length = 256;
                }
                (Some("U512"), Some("U512")) => {
                    bit_length = 512;
                }
                (Some("U1024"), Some("U1024")) => {
                    bit_length = 1024;
                }
                _ => {
                    left.to_tokens(&mut tokens, self)?;
                    op.to_tokens(&mut tokens);
                    right.to_tokens(&mut tokens, self)?;
                    return Ok(tokens);
                }
            };
        }

        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(
                        typed_expr.id,
                        RegInfo::new(*vreg, bit_length, Some(var_ident.clone())),
                    );
                } else {
                    let vreg = self.v_registers.alloc().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(
                        typed_expr.id,
                        RegInfo::new(vreg, bit_length, Some(var_ident.clone())),
                    );
                }
                self.expr_tokens
                    .insert(typed_expr.id, (quote! {#var_ident}, bit_length));
            } else {
                let _ts = self.gen_tokens(typed_expr, false, None, None, bit_length)?;
            }
        }

        let op_category = OpCategory::from(op);
        let (expr1, bit_len1) = self.expr_tokens.get(&left.id).cloned().unwrap();
        let (expr2, bit_len2) = self.expr_tokens.get(&right.id).cloned().unwrap();
        if bit_len1 != bit_len2 {
            return Err((
                expr.expr.1,
                anyhow!(
                    "bit length not matched, left: {}, right: {}",
                    bit_len1,
                    bit_len2
                ),
            ));
        }
        // FIXME: handle OpCategory::Bool
        if let OpCategory::Binary = op_category {
            let dvreg = self.v_registers.alloc().ok_or_else(|| {
                (
                    expr.expr.1,
                    anyhow!("not enough V register for this expression"),
                )
            })?;
            self.expr_regs
                .insert(expr.id, RegInfo::new(dvreg, bit_len1, None));
        }

        // FIXME:
        //   * div zero is allowed
        //   * shift more than bit length is allowed
        //   * TODO: find more special behaviors
        // See: https://github.com/riscv-software-src/riscv-isa-sim/blob/master/riscv/insns/v{op}_{v,vv,vx,vi,vm,vf,..}.h
        let ts = match op {
            // The `+` operator (addition)
            syn::BinOp::Add(_) => {
                quote! {
                    #expr1.wrapping_add(#expr2)
                }
            }
            // The `-` operator (subtraction)
            syn::BinOp::Sub(_) => {
                quote! {
                    #expr1.wrapping_sub(#expr2)
                }
            }
            // The `*` operator (multiplication)
            syn::BinOp::Mul(_) => {
                quote! {
                    #expr1.wrapping_mul(#expr2)
                }
            }
            // The `/` operator (division)
            syn::BinOp::Div(_) => {
                let uint_type = quote::format_ident!("U{}", bit_length);
                quote! {
                    #expr1.checked_div(#expr2).unwrap_or_else(|| #uint_type::max_value())
                }
            }
            // The `%` operator (modulus)
            syn::BinOp::Rem(_) => {
                quote! {
                    #expr1 % #expr2
                }
            }

            // The `&&` operator (logical and)
            // The `||` operator (logical or)
            // NOTE: early returned when check type names
            syn::BinOp::And(_) | syn::BinOp::Or(_) => unreachable!(),

            // The `^` operator (bitwise xor)
            syn::BinOp::BitXor(_) => {
                quote! {
                    #expr1 ^ #expr2
                }
            }
            // The `&` operator (bitwise and)
            syn::BinOp::BitAnd(_) => {
                quote! {
                    #expr1 & #expr2
                }
            }
            // The `|` operator (bitwise or)
            syn::BinOp::BitOr(_) => {
                quote! {
                    #expr1 | #expr2
                }
            }
            // The `<<` operator (shift left)
            syn::BinOp::Shl(_) => {
                quote! {
                    #expr1 << #expr2
                }
            }
            // The `>>` operator (shift right)
            syn::BinOp::Shr(_) => {
                quote! {
                    #expr1 >> #expr2
                }
            }
            // The `==` operator (equality)
            syn::BinOp::Eq(_) => {
                quote! {
                    #expr1 == #expr2
                }
            }
            // The `<` operator (less than)
            syn::BinOp::Lt(_) => {
                quote! {
                    #expr1 < #expr2
                }
            }
            // The `<=` operator (less than or equal to)
            syn::BinOp::Le(_) => {
                quote! {
                    #expr1 <= #expr2
                }
            }
            // The `!=` operator (not equal to)
            syn::BinOp::Ne(_) => {
                quote! {
                    #expr1 != #expr2
                }
            }
            // The `>=` operator (greater than or equal to)
            syn::BinOp::Ge(_) => {
                quote! {
                    #expr1 >= #expr2
                }
            }
            // The `>` operator (greater than)
            syn::BinOp::Gt(_) => {
                quote! {
                    #expr1 > #expr2
                }
            }
            // The `+=` operator
            syn::BinOp::AddEq(_) => {
                quote! {
                    #expr1 = #expr1.wrapping_add(#expr2)
                }
            }
            // The `-=` operator
            syn::BinOp::SubEq(_) => {
                quote! {
                    #expr1 = #expr1.wrapping_sub(#expr2)
                }
            }
            // The `*=` operator
            syn::BinOp::MulEq(_) => {
                quote! {
                    #expr1 = #expr1.wrapping_mul(#expr2)
                }
            }
            // The `/=` operator
            syn::BinOp::DivEq(_) => {
                let uint_type = quote::format_ident!("U{}", bit_length);
                quote! {
                    #expr1 = #expr1.checked_div(#expr2).unwrap_or_else(|| #uint_type::max_value())
                }
            }
            // The `%=` operator
            syn::BinOp::RemEq(_) => {
                quote! {
                    #expr1 %= #expr2
                }
            }
            // The `^=` operator
            syn::BinOp::BitXorEq(_) => {
                quote! {
                    #expr1 ^= #expr2
                }
            }
            // The `&=` operator
            syn::BinOp::BitAndEq(_) => {
                quote! {
                    #expr1 &= #expr2
                }
            }
            // The `|=` operator
            syn::BinOp::BitOrEq(_) => {
                quote! {
                    #expr1 |= #expr2
                }
            }
            // The `<<=` operator
            syn::BinOp::ShlEq(_) => {
                quote! {
                    #expr1 <<= #expr2
                }
            }
            // The `>>=` operator
            syn::BinOp::ShrEq(_) => {
                quote! {
                    #expr1 >>= #expr2
                }
            }
        };
        tokens.extend(Some(ts));
        self.expr_tokens.insert(expr.id, (tokens.clone(), bit_len1));
        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some(info) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, info);
            }
            let ts_inner = tokens.clone();
            let ts = quote! {
                (#ts_inner)
            };
            self.expr_tokens.insert(extra_expr_id, (ts, bit_len1));
        }
        Ok(tokens)
    }
}
