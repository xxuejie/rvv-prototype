use anyhow::anyhow;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::token;

use super::{CodegenContext, OpCategory, ToTokenStream};
use crate::ast::{Expression, TypedExpression};
use crate::SpannedError;

use rvv_assembler::{Imm, Ivi, Ivv, VConfig, VInst, VReg, Vlmul, Vtypei, XReg};

impl CodegenContext {
    // Generate raw asm statements for top level expression
    pub(crate) fn gen_tokens(
        &mut self,
        expr: &TypedExpression,
        top_level: bool,
        extra_bind_id: Option<usize>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        let (left, op, right, is_assign) = match &expr.expr.0 {
            Expression::AssignOp { left, op, right } => (left, op, right, true),
            Expression::Binary { left, op, right } => (left, op, right, false),
            Expression::MethodCall { receiver, method, args, .. } => {
                return self.gen_method_call_tokens(expr, receiver, method, args, top_level, extra_bind_id, bit_length);
            }
            Expression::Paren { expr: sub_expr, .. } => {
                return self.gen_tokens(&*sub_expr, top_level, Some(expr.id), bit_length);
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
        self.update_vconfig(&mut tokens, bit_length);

        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(typed_expr.id, (*vreg, bit_length));
                } else {
                    // Load{256,512,1024}
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    // FIXME: t0 register may already used by Rust code
                    let inst = VInst::VleV {
                        width: bit_length,
                        vd: VReg::from_u8(vreg),
                        rs1: XReg::T0,
                        vm: false,
                    };
                    let [b0, b1, b2, b3] = inst.encode_bytes();
                    if self.show_asm {
                        let comment = format!("{} - {}", inst.encode_u32(), inst);
                        tokens.extend(Some(quote! {
                            let _ = #comment;
                        }));
                    }
                    let ts = quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_ident.as_ref().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    };
                    tokens.extend(Some(ts));
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, (vreg, bit_length));
                }
            } else {
                let ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
                tokens.extend(Some(ts));
            }
        }

        let op_category = OpCategory::from(op);
        let (svreg2, bit_len2) = *self.expr_regs.get(&left.id).unwrap();
        let (svreg1, bit_len1) = *self.expr_regs.get(&right.id).unwrap();
        assert_eq!(bit_len1, bit_len2);
        let dvreg = match op_category {
            OpCategory::Binary | OpCategory::Bool => {
                let dvreg = self.v_registers.next_register().ok_or_else(|| {
                    (
                        expr.expr.1,
                        anyhow!("not enough V register for this expression"),
                    )
                })?;
                self.expr_regs.insert(expr.id, (dvreg, bit_len1));
                dvreg
            }
            OpCategory::AssignOp => svreg1,
        };
        let ivv = Ivv {
            vd: VReg::from_u8(dvreg),
            vs2: VReg::from_u8(svreg2),
            vs1: VReg::from_u8(svreg1),
            vm: false,
        };
        let inst = match op {
            // ==== OpCategory::Binary | OpCategory::AssignOp ====
            // The `+` operator (addition)
            // The `+=` operator
            syn::BinOp::Add(_) | syn::BinOp::AddEq(_) => VInst::VaddVv(ivv),
            // The `-` operator (subtraction)
            // The `-=` operator
            syn::BinOp::Sub(_) | syn::BinOp::SubEq(_) => VInst::VsubVv(ivv),
            // The `*` operator (multiplication)
            // The `*=` operator
            syn::BinOp::Mul(_) | syn::BinOp::MulEq(_) => VInst::VmulVv(ivv),
            // The `/` operator (division)
            // The `/=` operator
            syn::BinOp::Div(_) | syn::BinOp::DivEq(_) => VInst::VdivuVv(ivv),
            // The `%` operator (modulus)
            // The `%=` operator
            syn::BinOp::Rem(_) | syn::BinOp::RemEq(_) => VInst::VremuVv(ivv),
            // The `^` operator (bitwise xor)
            // The `^=` operator
            syn::BinOp::BitXor(_) | syn::BinOp::BitXorEq(_) => VInst::VxorVv(ivv),
            // The `&` operator (bitwise and)
            // The `&=` operator
            syn::BinOp::BitAnd(_) | syn::BinOp::BitAndEq(_) => VInst::VandVv(ivv),
            // The `|` operator (bitwise or)
            // The `|=` operator
            syn::BinOp::BitOr(_) | syn::BinOp::BitOrEq(_) => VInst::VorVv(ivv),
            // The `<<` operator (shift left)
            // The `<<=` operator
            syn::BinOp::Shl(_) | syn::BinOp::ShlEq(_) => VInst::VsllVv(ivv),
            // The `>>` operator (shift right)
            // The `>>=` operator
            syn::BinOp::Shr(_) | syn::BinOp::ShrEq(_) => VInst::VsrlVv(ivv),

            // The `&&` operator (logical and)
            // The `||` operator (logical or)
            // NOTE: early returned when check type names
            syn::BinOp::And(_) | syn::BinOp::Or(_) => unreachable!(),

            // ==== OpCategory::Bool ====
            // The `==` operator (equality)
            syn::BinOp::Eq(_) => VInst::VmseqVv(ivv),
            // The `<` operator (less than)
            syn::BinOp::Lt(_) => VInst::VmsltuVv(ivv),
            // The `<=` operator (less than or equal to)
            syn::BinOp::Le(_) => VInst::VmsleuVv(ivv),
            // The `!=` operator (not equal to)
            syn::BinOp::Ne(_) => VInst::VmsneVv(ivv),
            // The `>=` operator (greater than or equal to)
            syn::BinOp::Ge(_) => VInst::VmsgeuVv(ivv),
            // The `>` operator (greater than)
            syn::BinOp::Gt(_) => VInst::VmsgtuVv(ivv),
        };
        let [b0, b1, b2, b3] = inst.encode_bytes();
        if self.show_asm {
            let comment = format!("{} - {}", inst, inst.encode_u32());
            tokens.extend(Some(quote! {
                let _ = #comment;
            }));
        }
        let ts = quote! {
            unsafe {
                asm!(".byte {0}, {1}, {2}, {3}", const #b0, const #b1, const #b2, const #b3,)
            }
        };
        tokens.extend(Some(ts));

        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some((dvreg, bit_len)) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, (dvreg, bit_len));
            }
        }

        match op_category {
            OpCategory::Binary if top_level => {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VseV {
                    width: bit_length,
                    vs3: VReg::from_u8(vreg),
                    rs1: XReg::T0,
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                    }));
                }
                let uint_type = quote::format_ident!("U{}", bit_length);
                let buf_length = bit_length as usize / 8;
                tokens.extend(Some(quote! {
                    let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                    unsafe {
                        asm!(
                            "mv t0, {0}",
                            // This should be vse{256, 512, 1024}
                            ".byte {1}, {2}, {3}, {4}",
                            in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                            const #b0, const #b1, const #b2, const #b3,
                        )
                    }
                    unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
                }));
                let mut rv = TokenStream::new();
                token::Brace::default().surround(&mut rv, |inner| {
                    inner.extend(Some(tokens));
                });
                Ok(rv)
            }
            OpCategory::Binary | OpCategory::AssignOp => Ok(tokens),
            OpCategory::Bool => {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VfirstM {
                    rd: XReg::T0,
                    vs2: VReg::from_u8(vreg),
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment;
                        let _ = "mv {tmp_rv_t0}, t0";
                    }));
                }
                tokens.extend(Some(quote! {
                    let tmp_bool_t0: i64;
                    // t0: 0  (vms* success)
                    // t0: -1 (not found)
                    unsafe {
                        asm!(
                            // This should be vfirst.m t0, vrs2
                            ".byte {0}, {1}, {2}, {3}",
                            "mv {4}, t0",
                            const #b0, const #b1, const #b2, const #b3,
                            out (reg) tmp_bool_t0,
                        )
                    }
                    tmp_bool_t0 == 0
                }));
                let mut rv = TokenStream::new();
                token::Brace::default().surround(&mut rv, |inner| {
                    inner.extend(Some(tokens));
                });
                Ok(rv)
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn gen_method_call_tokens(
        &mut self,
        expr: &TypedExpression,
        receiver: &TypedExpression,
        method: &syn::Ident,
        args: &[TypedExpression],
        top_level: bool,
        extra_bind_id: Option<usize>,
        mut bit_length: u16,
    ) -> Result<TokenStream, SpannedError> {
        let receiver_bit_length: u16 = match receiver.type_name().as_deref() {
            Some("U256") => 256,
            Some("U512") => 512,
            Some("U1024") => 1024,
            _ => self
                .expr_regs
                .get(&expr.id)
                .map(|(_, bit_len)| *bit_len)
                .unwrap_or(0),
        };
        if top_level {
            bit_length = receiver_bit_length;
        }
        if bit_length == 0 {
            return self.default_method_call_codegen(receiver, method, args);
        }

        let method_string = method.to_string();
        let mut tokens = TokenStream::new();
        match method_string.as_str() {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "wrapping_div" | "wrapping_rem"
            | "overflowing_add" | "overflowing_sub" | "overflowing_mul" | "checked_add"
            | "checked_sub" | "checked_mul" | "checked_div" | "checked_rem" | "saturating_add"
            | "saturating_sub" | "saturating_mul" => {
                if args.len() != 1 {
                    return Err((
                        expr.expr.1,
                        anyhow!(
                            "special method call to U256/U512/U1024, must have exact one argument"
                        ),
                    ));
                }
            }
            _ => {
                return self.default_method_call_codegen(receiver, method, args);
            }
        }

        self.update_vconfig(&mut tokens, bit_length);

        let left = &receiver;
        let right = &args[0];
        for typed_expr in [left, right] {
            if let Some(var_ident) = typed_expr.expr.0.var_ident() {
                if let Some(vreg) = self.var_regs.get(var_ident) {
                    self.expr_regs.insert(typed_expr.id, (*vreg, bit_length));
                } else {
                    // Load{256,512,1024}
                    let vreg = self.v_registers.next_register().ok_or_else(|| {
                        (
                            typed_expr.expr.1,
                            anyhow!("not enough V register for this expression"),
                        )
                    })?;
                    // FIXME: t0 register may already used by Rust code
                    let inst = VInst::VleV {
                        width: bit_length,
                        vd: VReg::from_u8(vreg),
                        rs1: XReg::T0,
                        vm: false,
                    };
                    let [b0, b1, b2, b3] = inst.encode_bytes();
                    if self.show_asm {
                        let comment = format!("{} - {}", inst.encode_u32(), inst);
                        tokens.extend(Some(quote! {
                            let _ = #comment;
                        }));
                    }
                    let ts = quote! {
                        unsafe {
                            asm!(
                                "mv t0, {0}",
                                ".byte {1}, {2}, {3}, {4}",
                                in(reg) #var_ident.as_ref().as_ptr(),
                                const #b0, const #b1, const #b2, const #b3,
                            )
                        }
                    };
                    tokens.extend(Some(ts));
                    self.var_regs.insert(var_ident.clone(), vreg);
                    self.expr_regs.insert(typed_expr.id, (vreg, bit_length));
                }
            } else {
                let ts = self.gen_tokens(typed_expr, false, None, bit_length)?;
                tokens.extend(Some(ts));
            }
        }

        let (svreg2, bit_len2) = *self.expr_regs.get(&left.id).unwrap();
        let (svreg1, bit_len1) = *self.expr_regs.get(&right.id).unwrap();
        assert_eq!(bit_len1, bit_len2);
        let dvreg = self.v_registers.next_register().ok_or_else(|| {
            (
                expr.expr.1,
                anyhow!("not enough V register for this expression"),
            )
        })?;
        self.expr_regs.insert(expr.id, (dvreg, bit_len1));
        // Handle `Expression::Paren(expr)`, bind current expr register to parent expr.
        if let Some(extra_expr_id) = extra_bind_id {
            if let Some((dvreg, bit_len)) = self.expr_regs.get(&expr.id).cloned() {
                self.expr_regs.insert(extra_expr_id, (dvreg, bit_len));
            }
        }

        let ivv = Ivv {
            vd: VReg::from_u8(dvreg),
            vs2: VReg::from_u8(svreg2),
            vs1: VReg::from_u8(svreg1),
            vm: false,
        };

        match method_string.as_str() {
            "wrapping_add" => inst_codegen(&mut tokens, VInst::VaddVv(ivv), self.show_asm),
            "wrapping_sub" => inst_codegen(&mut tokens, VInst::VsubVv(ivv), self.show_asm),
            "wrapping_mul" => inst_codegen(&mut tokens, VInst::VmulVv(ivv), self.show_asm),
            "wrapping_div" => inst_codegen(&mut tokens, VInst::VdivuVv(ivv), self.show_asm),
            "wrapping_rem" => inst_codegen(&mut tokens, VInst::VremuVv(ivv), self.show_asm),

            /*
            vadd.vv v1, v2, v3
            vmsltu.vv v4, v1, v2
            vfirst.m t0, v4
            if t0 == 0 {
                (v1, true)
            } else {
                (v1, false)
            }
            */
            "overflowing_add" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VaddVv(ivv),
                    ivv,
                    bit_length,
                    false,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            vsub.vv v1, v2, v3
            vmsltu.vv v4, v2, v3
            vfirst.m t0, v4
            if t0 == 0 {
                (v1, true)
            } else {
                (v1, false)
            }
             */
            "overflowing_sub" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VsubVv(ivv),
                    ivv,
                    bit_length,
                    false,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            vmul.vv v1, v2, v3
            vmsne.vi v4 v1, 0
            vfirst.m t0, v4
            if t0 == 0 {
                vdivu.vv v4, v1, v2
                vmsne.vv v4, v4, v3
                vfirst.m t1, v4
                (v1, t1 == 0)
            } else {
                (v1, false)
            }
             */
            "overflowing_mul" => {
                self.overflowing_mul_codegen(&mut tokens, ivv, bit_length, false)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            /*
            let (value, overflow) = self.overflowing_add(other);
            if overflow {
                None
            } else {
                Some(value)
            }
             */
            "checked_add" => {
                self.simple_overflowing_codegen(
                    &mut tokens,
                    VInst::VaddVv(ivv),
                    ivv,
                    bit_length,
                    true,
                )
                .map_err(|err| (expr.expr.1, err))?;
            }

            // FIXME: current impl is wrong
            /*
            vmsltu.vv v4, v2, v3
            vfirst.m t0, v4
            if t0 == 0 {
                None
            } else {
                vsub.vv v1, v2, v3
                Some(v1)
            }
             */
            "checked_sub" => {
                self.checked_sub(&mut tokens, VInst::VsubVv(ivv), ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            let (value, overflow) = self.overflowing_mul(other);
            if overflow {
                None
            } else {
                Some(value)
            }
             */
            "checked_mul" => {
                self.overflowing_mul_codegen(&mut tokens, ivv, bit_length, true)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            /*
            vmseq.vi v4, v2, 0  # (v2 == vs1)
            vfirst.m t0, v4
            if t0 == 0 {
                None
            } else {
                vdivu.vv v1, v2, v3
                Some(v1)
            }
             */
            "checked_div" => {
                self.simple_checked_codegen(&mut tokens, VInst::VdivuVv(ivv), ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }
            /*
            => Same as checked_div()
             */
            "checked_rem" => {
                self.simple_checked_codegen(&mut tokens, VInst::VremuVv(ivv), ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }

            // vsaddu.vv vd, vs2, vs1, vm
            "saturating_add" => inst_codegen(&mut tokens, VInst::VsadduVv(ivv), self.show_asm),
            // vssubu.vv vd, vs2, vs1, vm
            "saturating_sub" => inst_codegen(&mut tokens, VInst::VssubuVv(ivv), self.show_asm),
            /*
            vmul.vv v1, v2, v3
            vmsne.vi v4 v1, 0
            vfirst.m t0, v4
            if t0 == 0 {
                vdivu.vv v4, v1, v2
                vmsne.vv v4, v4, v3
                vfirst.m t1, v4
                if t1 == 0 {
                    Uxx::max_value()
                } else {
                    v1
                }
            } else {
                v1
            }
             */
            "saturating_mul" => {
                self.saturating_mul_codegen(&mut tokens, ivv, bit_length)
                    .map_err(|err| (expr.expr.1, err))?;
            }
            _ => {}
        };

        let is_simple_asm = matches!(
            method_string.as_str(),
            "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "wrapping_div"
                | "wrapping_rem"
                | "saturating_add"
                | "saturating_sub"
        );

        if top_level {
            if is_simple_asm {
                let (vreg, _bit_len) = *self.expr_regs.get(&expr.id).unwrap();
                let inst = VInst::VseV {
                    width: bit_length,
                    vs3: VReg::from_u8(vreg),
                    rs1: XReg::T0,
                    vm: false,
                };
                let [b0, b1, b2, b3] = inst.encode_bytes();
                if self.show_asm {
                    let comment0 = "mv t0, {tmp_rvv_vector_buf}";
                    let comment1 = format!("{} - {}", inst, inst.encode_u32());
                    tokens.extend(Some(quote! {
                        let _ = #comment0;
                        let _ = #comment1;
                    }));
                }
                let uint_type = quote::format_ident!("U{}", bit_length);
                let buf_length = bit_length as usize / 8;
                tokens.extend(Some(quote! {
                    let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                    unsafe {
                        asm!(
                            "mv t0, {0}",
                            // This should be vse{256, 512, 1024}
                            ".byte {1}, {2}, {3}, {4}",
                            in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                            const #b0, const #b1, const #b2, const #b3,
                        )
                    }
                    unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
                }));
            }
            let mut rv = TokenStream::new();
            token::Brace::default().surround(&mut rv, |inner| {
                inner.extend(Some(tokens));
            });
            Ok(rv)
        } else {
            Ok(tokens)
        }
    }

    pub(crate) fn update_vconfig(&mut self, tokens: &mut TokenStream, bit_length: u16) {
        // vsetvli x0, t0, e{256,512,1024}, m1, ta, ma
        let v_config = VConfig::Vsetvli {
            rd: XReg::Zero,
            rs1: XReg::T0,
            vtypei: Vtypei::new(bit_length, Vlmul::M1, true, true),
        };
        if self.v_config.as_ref() != Some(&v_config) {
            self.v_config = Some(v_config);
            let inst = VInst::VConfig(v_config);
            let [b0, b1, b2, b3] = inst.encode_bytes();
            if self.show_asm {
                let comment0 = "li t0, 1";
                let comment1 = format!("{} - {}", inst.encode_u32(), inst);
                tokens.extend(Some(quote! {
                    let _ = #comment0;
                    let _ = #comment1;
                }));
            }
            let ts = quote! {
                unsafe {
                    asm!(
                        "li t0, 1",  // AVL = 1
                        ".byte {0}, {1}, {2}, {3}",
                        const #b0, const #b1, const #b2, const #b3,
                    )
                }
            };
            tokens.extend(Some(ts));
        }
    }

    fn simple_checked_codegen(
        &mut self,
        tokens: &mut TokenStream,
        inst: VInst,
        ivv: Ivv,
        bit_length: u16,
    ) -> Result<(), anyhow::Error> {
        let eq_vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();
        for pre_inst in [
            VInst::VmseqVi(Ivi {
                vd: VReg::from_u8(eq_vd),
                vs2: ivv.vs1,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(eq_vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, pre_inst, self.show_asm);
        }

        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T1,
            vm: false,
        };
        let [b0_inst, b1_inst, b2_inst, b3_inst] = inst.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;

        if self.show_asm {
            let comment0 = "mv {tmp_bool_var}, t0";
            let comment1 = format!("{} - {}", inst.encode_u32(), inst);
            let comment2 = "mv t1, {tmp_rvv_vector_buf}";
            let comment3 = format!("{} - {}", inst_store.encode_u32(), inst_store);
            tokens.extend(Some(quote! {
                let _ = #comment0;
                let _ = #comment1;
                let _ = #comment2;
                let _ = #comment3;
            }));
        }
        let ts = quote! {
            let tmp_bool_var: i64;
            // tn: 0  (vms* success)
            // tn: -1 (not found)
            unsafe {
                asm!(
                    "mv {0}, t0",
                    out(reg) tmp_bool_var,
                )
            }
            if tmp_bool_var == 0 {
                None
            } else {
                let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                unsafe {
                    asm!(
                        ".byte {0}, {1}, {2}, {3}",
                        "mv t1, {4}",
                        ".byte {5}, {6}, {7}, {8}",
                        const #b0_inst, const #b1_inst, const #b2_inst, const #b3_inst,
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                    )
                }
                Some(unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) })
            }
        };
        inner_tokens.extend(Some(ts));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    // TODO: merge this method with simple_checked_codegen()
    fn checked_sub(
        &mut self,
        tokens: &mut TokenStream,
        inst: VInst,
        ivv: Ivv,
        bit_length: u16,
    ) -> Result<(), anyhow::Error> {
        let lt_vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();
        for inst in [
            VInst::VmsltuVv(Ivv {
                vd: VReg::from_u8(lt_vd),
                vs2: ivv.vs2,
                vs1: ivv.vs1,
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(lt_vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }

        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T1,
            vm: false,
        };
        let [b0_inst, b1_inst, b2_inst, b3_inst] = inst.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;

        if self.show_asm {
            let comment0 = "mv {tmp_bool_var}, t0";
            let comment1 = format!("{} - {}", inst.encode_u32(), inst);
            let comment2 = "mv t1, {tmp_rvv_vector_buf}";
            let comment3 = format!("{} - {}", inst_store.encode_u32(), inst_store);
            tokens.extend(Some(quote! {
                let _ = #comment0;
                let _ = #comment1;
                let _ = #comment2;
                let _ = #comment3;
            }));
        }
        let ts = quote! {
            let tmp_bool_var: i64;
            // tn: 0  (vms* success)
            // tn: -1 (not found)
            unsafe {
                asm!(
                    "mv {0}, t0",
                    out(reg) tmp_bool_var,
                )
            }
            if tmp_bool_var == 0 {
                None
            } else {
                let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                unsafe {
                    asm!(
                        ".byte {0}, {1}, {2}, {3}",
                        "mv t1, {4}",
                        ".byte {5}, {6}, {7}, {8}",
                        const #b0_inst, const #b1_inst, const #b2_inst, const #b3_inst,
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                    )
                }
                Some(unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) })
            }
        };
        inner_tokens.extend(Some(ts));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    fn simple_overflowing_codegen(
        &mut self,
        tokens: &mut TokenStream,
        inst: VInst,
        ivv: Ivv,
        bit_length: u16,
        // checked_{add,sub}()
        is_checked: bool,
    ) -> Result<(), anyhow::Error> {
        let lt_vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();
        for inst in [
            inst,
            VInst::VmsltuVv(Ivv {
                vd: VReg::from_u8(lt_vd),
                vs2: ivv.vd,
                vs1: ivv.vs1,
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(lt_vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }
        if is_checked {
            checked_rv_codegen(&mut inner_tokens, ivv.vd, bit_length, self.show_asm);
        } else {
            overflowing_rv_codegen(&mut inner_tokens, ivv.vd, bit_length, self.show_asm);
        }
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    fn overflowing_mul_codegen(
        &mut self,
        tokens: &mut TokenStream,
        ivv: Ivv,
        bit_length: u16,
        // is checked_mul()
        is_checked: bool,
    ) -> Result<(), anyhow::Error> {
        let vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;
        let mut inner_tokens = TokenStream::new();

        // vmul.vv v1, v2, v3
        // vmsne.vi v4 v1, 0
        // vfirst.m t0, v4
        for inst in [
            VInst::VmulVv(ivv),
            VInst::VmsneVi(Ivi {
                vd: VReg::from_u8(vd),
                vs2: ivv.vd,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }

        let inst_div = VInst::VdivuVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: ivv.vd,
            vs1: ivv.vs2,
            vm: false,
        });

        let inst_ne = VInst::VmsneVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: VReg::from_u8(vd),
            vs1: ivv.vs1,
            vm: false,
        });

        let inst_firstm = VInst::VfirstM {
            rd: XReg::T1,
            vs2: VReg::from_u8(vd),
            vm: false,
        };
        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T2,
            vm: false,
        };

        let [b0_div, b1_div, b2_div, b3_div] = inst_div.encode_bytes();
        let [b0_ne, b1_ne, b2_ne, b3_ne] = inst_ne.encode_bytes();
        let [b0_firstm, b1_firstm, b2_firstm, b3_firstm] = inst_firstm.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;
        if self.show_asm {
            let comment0 = "mv {tmp_bool_t0}, t0";
            let comment1 = "mv t2, {tmp_rvv_vector_buf}";
            let comment2 = format!("{} - {}", inst_store.encode_u32(), inst_store);
            tokens.extend(Some(quote! {
                let _ = #comment0;
                let _ = #comment1;
                let _ = #comment2;
            }));
        }
        inner_tokens.extend(Some(quote! {
            let tmp_bool_t0: i64;
            let mut tmp_rvv_vector_buf = [0u8; #buf_length];
            unsafe {
                asm!(
                    "mv {0}, t0",
                    "mv t2, {1}",
                    // vse{n}.v v1, (t2)
                    ".byte {2}, {3}, {4}, {5}",
                    out(reg) tmp_bool_t0,
                    in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                    const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                )
            }
            let tmp_uint_rv = unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) };
        }));
        if self.show_asm {
            let comment0 = format!("{} - {}", inst_div.encode_u32(), inst_div);
            let comment1 = format!("{} - {}", inst_ne.encode_u32(), inst_ne);
            let comment2 = format!("{} - {}", inst_firstm.encode_u32(), inst_firstm);
            let comment3 = "mv {tmp_bool_t1}, t1";
            tokens.extend(Some(quote! {
                let _ = #comment0;
                let _ = #comment1;
                let _ = #comment2;
                let _ = #comment3;
            }));
        }
        let ts = if is_checked {
            quote! {
                if tmp_bool_t0 == 0 {
                    let tmp_bool_t1: i64;
                    unsafe {
                        asm!(
                            // vdivu.vv v4, v1, v2
                            ".byte {0}, {1}, {2}, {3}",
                            // vmsne.vv v4, v4, v3
                            ".byte {4}, {5}, {6}, {7}",
                            // vfirst.m t1, v4
                            ".byte {8}, {9}, {10}, {11}",
                            "mv {12}, t1",
                            const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                            const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                            const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                            out(reg) tmp_bool_t1,
                        )
                    }
                    if tmp_bool_t1 == 0 {
                        None
                    } else {
                        Some(tmp_uint_rv)
                    }
                } else {
                    Some(tmp_uint_rv)
                }
            }
        } else {
            quote! {
                if tmp_bool_t0 == 0 {
                    let tmp_bool_t1: i64;
                    unsafe {
                        asm!(
                            // vdivu.vv v5, v1, v2
                            ".byte {0}, {1}, {2}, {3}",
                            // vmsne.vv v4, v5, v3
                            ".byte {4}, {5}, {6}, {7}",
                            // vfirst.m t1, v4
                            ".byte {8}, {9}, {10}, {11}",
                            "mv {12}, t1",
                            const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                            const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                            const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                            out(reg) tmp_bool_t1,
                        )
                    }
                    (tmp_uint_rv, tmp_bool_t1 == 0)
                } else {
                    (tmp_uint_rv, false)
                }
            }
        };
        inner_tokens.extend(Some(ts));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }

    fn saturating_mul_codegen(
        &mut self,
        tokens: &mut TokenStream,
        ivv: Ivv,
        bit_length: u16,
    ) -> Result<(), anyhow::Error> {
        let vd = self
            .v_registers
            .next_register()
            .ok_or_else(|| anyhow!("not enough V register for this expression"))?;

        let mut inner_tokens = TokenStream::new();
        for inst in [
            VInst::VmulVv(ivv),
            VInst::VmsneVi(Ivi {
                vd: VReg::from_u8(vd),
                vs2: ivv.vd,
                imm: Imm(0),
                vm: false,
            }),
            VInst::VfirstM {
                rd: XReg::T0,
                vs2: VReg::from_u8(vd),
                vm: false,
            },
        ] {
            inst_codegen(&mut inner_tokens, inst, self.show_asm);
        }

        let inst_div = VInst::VdivuVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: ivv.vd,
            vs1: ivv.vs2,
            vm: false,
        });
        let inst_ne = VInst::VmsneVv(Ivv {
            vd: VReg::from_u8(vd),
            vs2: VReg::from_u8(vd),
            vs1: ivv.vs1,
            vm: false,
        });
        let inst_firstm = VInst::VfirstM {
            rd: XReg::T1,
            vs2: VReg::from_u8(vd),
            vm: false,
        };
        let inst_store = VInst::VseV {
            width: bit_length,
            vs3: ivv.vd,
            rs1: XReg::T2,
            vm: false,
        };
        let [b0_div, b1_div, b2_div, b3_div] = inst_div.encode_bytes();
        let [b0_ne, b1_ne, b2_ne, b3_ne] = inst_ne.encode_bytes();
        let [b0_firstm, b1_firstm, b2_firstm, b3_firstm] = inst_firstm.encode_bytes();
        let [b0_store, b1_store, b2_store, b3_store] = inst_store.encode_bytes();
        let uint_type = quote::format_ident!("U{}", bit_length);
        let buf_length = bit_length as usize / 8;
        inner_tokens.extend(Some(quote! {
            let tmp_bool_t0: i64;
            let mut tmp_bool_t1: i64 = -1;
            unsafe {
                asm!(
                    "mv {0}, t0",
                    out(reg) tmp_bool_t0,
                )
            }
            if tmp_bool_t0 == 0 {
                unsafe {
                    asm!(
                        ".byte {0}, {1}, {2}, {3}",
                        ".byte {4}, {5}, {6}, {7}",
                        ".byte {8}, {9}, {10}, {11}",
                        "mv {12}, t1",
                        const #b0_div, const #b1_div, const #b2_div, const #b3_div,
                        const #b0_ne, const #b1_ne, const #b2_ne, const #b3_ne,
                        const #b0_firstm, const #b1_firstm, const #b2_firstm, const #b3_firstm,
                        out(reg) tmp_bool_t1,
                    )
                }
            }
            if tmp_bool_t1 == 0 {
                #uint_type::max_value()
            } else {
                let mut tmp_rvv_vector_buf = [0u8; #buf_length];
                unsafe {
                    asm!(
                        "mv t2, {0}",
                        ".byte {1}, {2}, {3}, {4}",
                        in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                        const #b0_store, const #b1_store, const #b2_store, const #b3_store,
                    )
                }
                unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }
            }
        }));
        token::Brace::default().surround(tokens, |inner| {
            inner.extend(Some(inner_tokens));
        });
        Ok(())
    }
}

fn inst_codegen(tokens: &mut TokenStream, inst: VInst, show_asm: bool) {
    let [b0, b1, b2, b3] = inst.encode_bytes();
    if show_asm {
        let comment = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment;
        }));
    }
    let ts = quote! {
        unsafe {
            asm!(".byte {0}, {1}, {2}, {3}", const #b0, const #b1, const #b2, const #b3,)
        }
    };
    tokens.extend(Some(ts));
}

fn overflowing_rv_codegen(tokens: &mut TokenStream, vreg: VReg, bit_length: u16, show_asm: bool) {
    let inst = VInst::VseV {
        width: bit_length,
        vs3: vreg,
        rs1: XReg::T1,
        vm: false,
    };
    if show_asm {
        let comment0 = "mv {tmp_bool_var}, t0";
        let comment1 = "mv t1, {tmp_rvv_vector_buf}";
        let comment2 = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment0;
            let _ = #comment1;
            let _ = #comment2;
        }));
    }
    let [b0, b1, b2, b3] = inst.encode_bytes();

    let uint_type = quote::format_ident!("U{}", bit_length);
    let buf_length = bit_length as usize / 8;
    tokens.extend(Some(quote! {
        let tmp_bool_var: i64;
        let mut tmp_rvv_vector_buf = [0u8; #buf_length];
        // t0: 0  (vms* success)
        // t0: -1 (not found)
        unsafe {
            asm!(
                "mv {0}, t0",
                "mv t1, {1}",
                ".byte {2}, {3}, {4}, {5}",
                out(reg) tmp_bool_var,
                in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                const #b0, const #b1, const #b2, const #b3,
            )
        }
        (unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) }, tmp_bool_var == 0)
    }));
}

fn checked_rv_codegen(tokens: &mut TokenStream, vreg: VReg, bit_length: u16, show_asm: bool) {
    let inst = VInst::VseV {
        width: bit_length,
        vs3: vreg,
        rs1: XReg::T1,
        vm: false,
    };
    if show_asm {
        let comment0 = "mv {tmp_bool_var}, t0";
        let comment1 = "mv t1, {tmp_rvv_vector_buf}";
        let comment2 = format!("{} - {}", inst, inst.encode_u32());
        tokens.extend(Some(quote! {
            let _ = #comment0;
            let _ = #comment1;
            let _ = #comment2;
        }));
    }
    let [b0, b1, b2, b3] = inst.encode_bytes();

    let uint_type = quote::format_ident!("U{}", bit_length);
    let buf_length = bit_length as usize / 8;
    tokens.extend(Some(quote! {
        let tmp_bool_var: i64;
        // t0: 0  (vms* success)
        // t0: -1 (not found)
        unsafe {
            asm!(
                "mv {0}, t0",
                out(reg) tmp_bool_var,
            )
        }
        if tmp_bool_var == 0 {
            None
        } else {
            let mut tmp_rvv_vector_buf = [0u8; #buf_length];
            unsafe {
                asm!(
                    "mv t1, {0}",
                    ".byte {1}, {2}, {3}, {4}",
                    in(reg) tmp_rvv_vector_buf.as_mut_ptr(),
                    const #b0, const #b1, const #b2, const #b3,
                )
            }
            Some(unsafe { core::mem::transmute::<[u8; #buf_length], #uint_type>(tmp_rvv_vector_buf) })
        }
    }));
}
