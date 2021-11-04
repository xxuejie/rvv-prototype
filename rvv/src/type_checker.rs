use std::collections::HashMap;

use anyhow::{anyhow, bail, Error};

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Statement, Type,
    TypedExpression,
};

#[derive(Default, Debug)]
pub struct CheckerContext {
    expr_id: usize,
    variables: HashMap<syn::Ident, (bool, Type)>,
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
        Ok(())
    }
}
impl TypeChecker for Pattern {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for Expression {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for TypedExpression {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for Statement {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        match self {
            Statement::Local { pat, init } => {
                match pat {
                    Pattern::Ident { mutability, ident } => {
                        if let Some(ty) = init.get_type(&context.variables) {
                            if context
                                .variables
                                .insert((*ident).clone(), (*mutability, ty))
                                .is_some()
                            {
                                bail!("variable shadowing is not supported in rvv_vector");
                            }
                        }
                    }
                    Pattern::Type { pat, ty } => match &**pat {
                        Pattern::Ident { mutability, ident } => {
                            if context
                                .variables
                                .insert((*ident).clone(), (*mutability, Type::clone(ty)))
                                .is_some()
                            {
                                bail!("variable shadowing is not supported in rvv_vector");
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                }
                pat.check_types(context)?;
                init.check_types(context)?;
            }
            Statement::Expr(expr) => {
                expr.check_types(context)?;
            }
            Statement::Semi(expr) => {
                expr.check_types(context)?;
            }
        }
        Ok(())
    }
}
impl TypeChecker for Block {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for FnArg {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
impl TypeChecker for Signature {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        for input in &self.inputs {
            // let binding in signature
            context.variables.insert(
                input.name.clone(),
                (input.mutability, Type::clone(&input.ty)),
            );
        }
        Ok(())
    }
}

impl TypeChecker for ItemFn {
    fn check_types(&mut self, context: &mut CheckerContext) -> Result<(), Error> {
        Ok(())
    }
}
