use std::collections::HashMap;

use anyhow::{anyhow, bail, Error};
use proc_macro2::Span as SynSpan;

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Statement, Type,
    TypedExpression,
};

#[derive(Default, Debug)]
pub struct CheckerContext {
    expr_id: usize,
    // ident => (mutability, Type)
    variables: HashMap<syn::Ident, (bool, Box<Type>)>,
}

impl CheckerContext {
    fn get_expr_id(&mut self) -> usize {
        let current_id = self.expr_id;
        self.expr_id += 1;
        current_id
    }
}

// ================================
// ==== impl TypeChecker for T ====
// ================================
// Extra Rules:
//   1. variable shadowing is forbidden
pub trait TypeChecker {
    // infer(by fill TypedExpression.{ty, id} field) and check types
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error>;
}

impl TypeChecker for ReturnType {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            ReturnType::Default => {}
            ReturnType::Type(ty) => {
                ty.check_types(context)?;
            }
        }
        Ok(())
    }
}

impl TypeChecker for BareFnArg {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for Type {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            Type::Array { elem, len } => {
                elem.check_types(context)?;
                len.check_types(context)?;
            }
            Type::BareFn { inputs, output } => {
                for input in inputs {
                    input.check_types(context)?;
                }
                output.check_types(context)?;
            }
            Type::Path(_path) => {}
            Type::Reference {
                lifetime,
                mutability,
                elem,
            } => {
                elem.check_types(context)?;
            }
            Type::Slice(ty) => {
                ty.check_types(context)?;
            }
            Type::Tuple(types) => {
                for ty in types {
                    ty.check_types(context)?;
                }
            }
        }
        Ok(())
    }
}
impl TypeChecker for Pattern {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            Pattern::Ident { mutability, ident } => {}
            Pattern::Type { pat, ty } => {
                pat.check_types(context)?;
                ty.check_types(context)?;
            }
            Pattern::Range { lo, limits, hi } => {
                lo.check_types(context)?;
                hi.check_types(context)?;
            }
            Pattern::Path(_path) => {}
            Pattern::Wild => {}
        }
        Ok(())
    }
}
impl TypeChecker for Expression {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            Expression::Array(arr) => {}
            Expression::Assign { left, right } => {
                left.check_types(context)?;
                right.check_types(context)?;
            }
            Expression::AssignOp { left, op, right } => {
                left.check_types(context)?;
                right.check_types(context)?;
            }
            Expression::Binary { left, op, right } => {
                left.check_types(context)?;
                right.check_types(context)?;
            }
            Expression::Call { func, args } => {
                func.check_types(context)?;
                for arg in args {
                    arg.check_types(context)?;
                }
            }
            Expression::MethodCall {
                receiver,
                method,
                args,
            } => {
                receiver.check_types(context)?;
                for arg in args {
                    arg.check_types(context)?;
                }
            }
            Expression::Macro(mac) => {}
            Expression::Unary { op, expr } => {
                expr.check_types(context)?;
            }
            Expression::Field { base, member } => {
                base.check_types(context)?;
            }
            Expression::Cast { expr, ty } => {
                expr.check_types(context)?;
                ty.check_types(context)?;
            }
            Expression::Repeat { expr, len } => {
                expr.check_types(context)?;
                len.check_types(context)?;
            }
            Expression::Lit(lit) => {}
            Expression::Paren(expr) => {
                expr.check_types(context)?;
            }
            Expression::Reference { mutability, expr } => {
                expr.check_types(context)?;
            }
            Expression::Index { expr, index } => {
                expr.check_types(context)?;
                index.check_types(context)?;
            }
            Expression::Path(_path) => {}
            Expression::Break => {}
            Expression::Continue => {}
            Expression::Return(expr_opt) => {
                if let Some(expr) = expr_opt.as_mut() {
                    expr.check_types(context)?;
                }
            }
            Expression::Block(block) => {
                block.check_types(context)?;
            }
            Expression::If {
                cond,
                then_branch,
                else_branch,
            } => {
                cond.check_types(context)?;
                then_branch.check_types(context)?;
                if let Some(expr) = else_branch.as_mut() {
                    expr.check_types(context)?;
                }
            }
            Expression::Range { from, limits, to } => {
                if let Some(expr) = from.as_mut() {
                    expr.check_types(context)?;
                }
                if let Some(expr) = to.as_mut() {
                    expr.check_types(context)?;
                }
            }
            Expression::Loop(body) => {
                body.check_types(context)?;
            }
            Expression::ForLoop { pat, expr, body } => {
                pat.check_types(context)?;
                expr.check_types(context)?;
                body.check_types(context)?;
            }
        }
        Ok(())
    }
}
impl TypeChecker for TypedExpression {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        if self.id != usize::max_value() {
            panic!(
                "TypedExpression.id assigned more than once: id={}, expr={:?}",
                self.id, self.expr
            );
        }
        self.id = context.get_expr_id();

        self.expr.check_types(context)?;
        self.ty = match &mut self.expr {
            Expression::Assign { left, right } | Expression::AssignOp { left, right, .. } => {
                if left.ty.is_none() {
                    left.ty = right.ty.clone()
                } else if right.ty.is_none() {
                    right.ty = left.ty.clone()
                } else {
                    if left.ty != right.ty {
                        bail!(
                            "Assign/AssignOp with different types is not supported in rvv_vector"
                        );
                    }
                }
                Some(Box::new(Type::unit()))
            }
            Expression::AssignOp { left, op, right } => {
                match (&mut left.ty, &mut right.ty) {
                    (Some(left_ty), Some(right_ty)) => {
                        if left_ty != right_ty {
                            bail!("assign op with different types is not supported in rvv_vector");
                        }
                    }
                    (None, Some(right_ty)) => {
                        left.ty = right.ty.clone();
                    }
                    (Some(left_ty), None) => {
                        right.ty = left.ty.clone();
                    }
                    (None, None) => {}
                }
                Some(Box::new(Type::unit()))
            }
            Expression::Binary { left, op, right } => {
                let bool_op = match op {
                    syn::BinOp::Eq(_)
                    | syn::BinOp::Lt(_)
                    | syn::BinOp::Le(_)
                    | syn::BinOp::Ne(_)
                    | syn::BinOp::Ge(_)
                    | syn::BinOp::Gt(_) => true,
                    _ => false,
                };

                let inner_ty = match (&mut left.ty, &mut right.ty) {
                    (Some(left_ty), Some(right_ty)) => {
                        if left_ty != right_ty {
                            bail!("Binary op with different types is not supported in rvv_vector");
                        }
                        left.ty.clone()
                    }
                    (None, Some(right_ty)) => {
                        left.ty = right.ty.clone();
                        right.ty.clone()
                    }
                    (Some(left_ty), None) => {
                        right.ty = left.ty.clone();
                        left.ty.clone()
                    }
                    (None, None) => None,
                };

                if bool_op {
                    Some(Box::new(Type::primitive("bool")))
                } else {
                    inner_ty
                }
            }
            Expression::Unary { op, expr } => {
                match op {
                    syn::UnOp::Deref(_) => {
                        if !expr.ty.as_ref().map(|ty| ty.is_ref()).unwrap_or(true) {
                            bail!("deref a variable that is not reference is not supported in rvv_vector");
                        }
                        if let Some(ty) = expr.ty.as_ref() {
                            if let Some((_mutability, ty)) = ty.clone().into_deref() {
                                Some(ty)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    syn::UnOp::Not(_) | syn::UnOp::Neg(_) => None,
                }
            }
            Expression::Paren(expr) => expr.ty.clone(),
            Expression::Reference { expr, mutability } => {
                if expr.ty.as_ref().map(|ty| ty.is_ref()).unwrap_or(false) {
                    bail!("multiple reference to a variable is not supported in rvv_vector");
                }
                expr.ty
                    .clone()
                    .map(|ty| Box::new(ty.into_ref(None, *mutability)))
            }
            Expression::Block(block) => block.get_type(),
            Expression::If {
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(else_expr) = else_branch.as_mut() {
                    let then_type = then_branch.get_type();
                    match (&then_type, &else_expr.ty) {
                        (Some(left_ty), Some(right_ty)) => {
                            if left_ty != right_ty {
                                bail!(
                                    "different if else branch types is not supported in rvv_vector"
                                );
                            }
                            then_type.clone()
                        }
                        (None, Some(_)) => else_expr.ty.clone(),
                        (Some(_), None) => {
                            else_expr.ty = then_type.clone();
                            then_type.clone()
                        }
                        (None, None) => None,
                    }
                } else {
                    Some(Box::new(Type::unit()))
                }
            }
            Expression::Cast { expr, ty } => Some(ty.clone()),
            Expression::Path(path) => match path.get_ident() {
                Some(ident) => context.variables.get(ident).map(|(_, ty)| ty.clone()),
                None => None,
            },
            Expression::Break => Some(Box::new(Type::unit())),
            Expression::Continue => Some(Box::new(Type::unit())),
            Expression::Loop { .. } => Some(Box::new(Type::unit())),
            Expression::ForLoop { .. } => Some(Box::new(Type::unit())),
            _ => None,
        };

        if !self.expr.is_literal() && self.ty.is_none() {
            // println!("[WARN]: non-literal expression type not infered, id={}, {:?}", self.id, self.expr);
        }
        Ok(())
    }
}
impl TypeChecker for Statement {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            Statement::Local { pat, init } => {
                // println!(">> stmt::local: {:?}", pat);
                pat.check_types(context)?;
                init.check_types(context)?;
                match pat {
                    Pattern::Ident { mutability, ident } => {
                        if context.variables.contains_key(ident) {
                            bail!(
                                "variable ({}) shadowing is not supported in rvv_vector",
                                ident
                            );
                        }
                        if let Some(ty) = init.ty.clone() {
                            context
                                .variables
                                .insert((*ident).clone(), (*mutability, ty));
                        }
                    }
                    Pattern::Type { pat, ty } => match &**pat {
                        Pattern::Ident { mutability, ident } => {
                            if init.ty.is_none() {
                                init.ty = Some(ty.clone());
                            }
                            if context
                                .variables
                                .insert((*ident).clone(), (*mutability, ty.clone()))
                                .is_some()
                            {
                                bail!(
                                    "variable ({}) shadowing is not supported in rvv_vector",
                                    ident
                                );
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
            Statement::Expr(expr) => {
                // println!(">> stmt::expr: {:?}", expr);
                expr.check_types(context)?;
            }
            Statement::Semi(expr) => {
                // println!(">> stmt::semi: {:?}", expr);
                expr.check_types(context)?;
            }
        }
        Ok(())
    }
}
impl TypeChecker for Block {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        for stmt in self.stmts.iter_mut() {
            stmt.check_types(context)?;
        }
        Ok(())
    }
}
impl TypeChecker for FnArg {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        self.ty.check_types(context)?;
        Ok(())
    }
}
impl TypeChecker for Signature {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        for input in self.inputs.iter_mut() {
            // let binding in signature
            context
                .variables
                .insert(input.name.clone(), (input.mutability, input.ty.clone()));
            input.check_types(context)?;
        }
        self.output.check_types(context)?;
        Ok(())
    }
}

impl TypeChecker for ItemFn {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        self.sig.check_types(context)?;
        self.block.check_types(context)?;
        Ok(())
    }
}
