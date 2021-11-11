use std::convert::TryFrom;

use anyhow::{anyhow, bail};

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Span, Statement,
    Type, TypedExpression,
};
use syn::spanned::Spanned;

pub type Error = (Span, anyhow::Error);

// ============================
// ==== impl TryFrom for T ====
// ============================
impl TryFrom<&syn::ReturnType> for ReturnType {
    type Error = Error;
    fn try_from(return_type: &syn::ReturnType) -> Result<ReturnType, Error> {
        match return_type {
            syn::ReturnType::Default => Ok(ReturnType::Default),
            syn::ReturnType::Type(rarrow_token, ty) => {
                let rarrow_token = rarrow_token.span().into();
                let ty = Box::new((Type::try_from(&**ty)?, ty.span().into()));
                Ok(ReturnType::Type(rarrow_token, ty))
            }
        }
    }
}

impl TryFrom<&syn::BareFnArg> for BareFnArg {
    type Error = Error;
    fn try_from(bare_fn_arg: &syn::BareFnArg) -> Result<BareFnArg, Error> {
        let span = bare_fn_arg.span().into();
        let name = bare_fn_arg
            .name
            .as_ref()
            .map(|(ident, colon_token)| ((*ident).clone(), colon_token.span().into()));
        let ty = (
            Type::try_from(&bare_fn_arg.ty)?,
            bare_fn_arg.ty.span().into(),
        );
        Ok(BareFnArg { span, name, ty })
    }
}

impl TryFrom<&syn::Type> for Type {
    type Error = Error;
    fn try_from(ty: &syn::Type) -> Result<Type, Error> {
        match ty {
            syn::Type::Array(syn::TypeArray { elem, len, bracket_token, semi_token, ..}) => {
                let elem = Box::new(Type::try_from(&**elem)?);
                let len = TypedExpression::try_from(len)?;
                let bracket_token = bracket_token.span.into();
                let semi_token = semi_token.span.into();
                Ok(Type::Array { elem, len, bracket_token, semi_token })
            },
            syn::Type::BareFn(syn::TypeBareFn { lifetimes, unsafety, abi, inputs, variadic, output, fn_token, paren_token, .. }) => {
                if let Some(lifetimes) = lifetimes.as_ref() {
                    return Err((lifetimes.span().into(), anyhow!("lifetime in bare function type is not supported in rvv_vector")));
                }
                if let Some(unsafety) = unsafety.as_ref() {
                    return Err((unsafety.span().into(), anyhow!("unsafe bare function type is not supported in rvv_vector")));
                }
                if let Some(abi) = abi.as_ref() {
                    return Err((abi.span().into(), anyhow!("extern \"C\" in bare function type is not supported in rvv_vector")));
                }
                if let Some(variadic) = variadic.as_ref() {
                    return Err((variadic.span().into(), anyhow!("variadic argument in bare function type is not supported in rvv_vector")));
                }
                let inputs = inputs.iter()
                    .map(BareFnArg::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                let output = (ReturnType::try_from(output)?, output.span().into());
                let fn_token = fn_token.span.into();
                let paren_token = paren_token.span.into();
                Ok(Type::BareFn { inputs, output, fn_token, paren_token })
            },
            syn::Type::Group(_) => {
                Err((ty.span().into(), anyhow!("type contained within invisible delimiters is not supported in rvv_vector")))
            },
            syn::Type::ImplTrait(_) => {
                Err((ty.span().into(), anyhow!("impl Trait type is not supported in rvv_vector")))
            },
            syn::Type::Infer(_) => {
                Err((ty.span().into(), anyhow!("type should be inferred by the compiler is not supported in rvv_vector")))
            },
            syn::Type::Macro(_) => {
                Err((ty.span().into(), anyhow!("macro in the type position is not supported in rvv_vector")))
            },
            syn::Type::Never(_) => {
                Err((ty.span().into(), anyhow!("never type(!) is not supported in rvv_vector")))
            },
            syn::Type::Paren(syn::TypeParen{ elem, .. }) => {
                // pub struct TypeParen {
                //     pub paren_token: Paren,
                //     pub elem: Box<Type>,
                // }
                Ok(Type::try_from(&**elem)?)
            },
            syn::Type::Path(syn::TypePath { qself, path }) => {
                if let Some(qself) = qself.as_ref() {
                    return Err((qself.lt_token.span().into(), anyhow!("self-type in path type is not supported in rvv_vector")));
                }
                Ok(Type::Path((*path).clone()))
            },
            syn::Type::Ptr(_) => {
                Err((ty.span().into(), anyhow!("raw pointer type is not supported in rvv_vector")))
            },
            syn::Type::Reference(syn::TypeReference{ lifetime, mutability, elem, and_token, .. }) => {
                let lifetime = lifetime.as_ref().map(|lifetime| lifetime.ident.clone());
                let mutability = mutability.as_ref().map(|mutability| mutability.span.into());
                let elem = Box::new((Type::try_from(&**elem)?, elem.span().into()));
                let and_token = and_token.span().into();
                Ok(Type::Reference { mutability, lifetime, elem, and_token })
            },
            syn::Type::Slice(syn::TypeSlice{ elem, bracket_token, .. }) => {
                let elem = Box::new((Type::try_from(&**elem)?, elem.span().into()));
                let bracket_token = bracket_token.span.into();
                Ok(Type::Slice{elem, bracket_token })
            },
            syn::Type::TraitObject(_) => {
                Err((ty.span().into(), anyhow!("trait object type is not supported in rvv_vector")))
            },
            syn::Type::Tuple(syn::TypeTuple { elems, paren_token }) => {
                let paren_token = paren_token.span.into();
                let elems = elems.iter()
                    .map(|elem| Ok((Type::try_from(elem)?, elem.span().into())))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Type::Tuple{
                    paren_token,
                    elems
                })
            },
            syn::Type::Verbatim(_) => {
                Err((ty.span().into(), anyhow!("Tokens in type position that not interpreted by syn is not supported in rvv_vector")))
            },
            // some variants omitted
            ty => {
                Err((ty.span().into(), anyhow!("all other kind of type is not supported in rvv_vector")))
            }
        }
    }
}

impl TryFrom<&syn::Pat> for Pattern {
    type Error = Error;
    fn try_from(pat: &syn::Pat) -> Result<Pattern, Error> {
        match pat {
            syn::Pat::Box(_) => {
                Err((pat.span().into(), anyhow!("box pattern is not supported in rvv_vector")))
            },
            syn::Pat::Ident(syn::PatIdent { by_ref, mutability, ident, subpat, .. }) => {
                if let Some(by_ref) = by_ref.as_ref() {
                    return Err((by_ref.span().into(), anyhow!("ref pattern is not supported in rvv_vector")));
                }
                if let Some((_at, subpat)) = subpat.as_ref() {
                    return Err((subpat.span().into(), anyhow!("sub-pattern is not supported in rvv_vector")));
                }
                let mutability = mutability.as_ref().map(|mutability| mutability.span.into());
                let ident = (*ident).clone();
                Ok(Pattern::Ident{ mutability, ident })
            },
            syn::Pat::Lit(_) => {
                Err((pat.span().into(), anyhow!("literal pattern is not supported in rvv_vector")))
            },
            syn::Pat::Macro(_) => {
                Err((pat.span().into(), anyhow!("macro in pattern position is not supported in rvv_vector")))
            },
            syn::Pat::Or(_) => {
                Err((pat.span().into(), anyhow!("pattern that matches more than one case is not supported in rvv_vector")))
            },
            syn::Pat::Path(syn::PatPath { qself, path, .. }) => {
                if qself.is_some() {
                    return Err((pat.span().into(), anyhow!("self-type in path pattern is not supported in rvv_vector")));
                }
                Ok(Pattern::Path((*path).clone()))
            },
            syn::Pat::Range(syn::PatRange { lo, limits, hi, .. }) => {
                let lo = Box::new(TypedExpression::try_from(&**lo)?);
                let hi = Box::new(TypedExpression::try_from(&**hi)?);
                let limits = *limits;
                Ok(Pattern::Range { lo, limits, hi })
            },
            syn::Pat::Reference(_) => {
                Err((pat.span().into(), anyhow!("reference pattern is not supported in rvv_vector")))
            },
            syn::Pat::Rest(_) => {
                Err((pat.span().into(), anyhow!("dots in a tuple or slice pattern is not supported in rvv_vector")))
            },
            syn::Pat::Slice(_) => {
                Err((pat.span().into(), anyhow!("dynamically sized slice pattern is not supported in rvv_vector")))
            },
            syn::Pat::Struct(_) => {
                Err((pat.span().into(), anyhow!("struct or struct variant pattern is not supported in rvv_vector")))
            },
            syn::Pat::Tuple(_) => {
                Err((pat.span().into(), anyhow!("tuple pattern is not supported in rvv_vector")))
            },
            syn::Pat::TupleStruct(_) => {
                Err((pat.span().into(), anyhow!("tuple struct or tuple variant pattern is not supported in rvv_vector")))
            },
            syn::Pat::Type(syn::PatType { pat, ty, colon_token, .. }) => {
                let pat = Box::new((Pattern::try_from(&**pat)?, pat.span().into()));
                let ty = Box::new((Type::try_from(&**ty)?, ty.span().into()));
                let colon_token = colon_token.span().into();
                Ok(Pattern::Type { pat, ty, colon_token })
            },
            syn::Pat::Verbatim(_) => {
                Err((pat.span().into(), anyhow!("Tokens in pattern position that not interpreted by syn is not supported in rvv_vector")))
            },
            syn::Pat::Wild(_) => {
                Ok(Pattern::Wild(pat.span().into()))
            },
            pat => {
                Err((pat.span().into(), anyhow!("all other kind of pattern is not supported in rvv_vector")))
            }
        }
    }
}

impl TryFrom<&syn::Expr> for TypedExpression {
    type Error = Error;
    fn try_from(expr: &syn::Expr) -> Result<TypedExpression, Error> {
        let expr = (Expression::try_from(expr)?, expr.span().into());
        Ok(TypedExpression {
            expr,
            id: usize::max_value(),
            ty: None,
        })
    }
}

impl TryFrom<&syn::Expr> for Expression {
    type Error = Error;
    fn try_from(expr: &syn::Expr) -> Result<Expression, Error> {
        match expr {
            syn::Expr::Array(expr_array) => {
                Ok(Expression::Array(expr_array.clone()))
            }
            syn::Expr::Assign(syn::ExprAssign { left, right, eq_token, .. }) => {
                let left = Box::new(TypedExpression::try_from(&**left)?);
                let right = Box::new(TypedExpression::try_from(&**right)?);
                let eq_token = eq_token.span.into();
                Ok(Expression::Assign { left, right, eq_token })
            },
            syn::Expr::AssignOp(syn::ExprAssignOp { left, op, right, ..}) => {
                let left = Box::new(TypedExpression::try_from(&**left)?);
                let right = Box::new(TypedExpression::try_from(&**right)?);
                let op = *op;
                Ok(Expression::AssignOp { left, op, right})
            },
            syn::Expr::Async(_) => {
                Err((expr.span().into(), anyhow!("async block is not supported in rvv_vector")))
            },
            syn::Expr::Await(_) => {
                Err((expr.span().into(), anyhow!("await expression is not supported in rvv_vector")))
            },
            syn::Expr::Binary(syn::ExprBinary { left, op, right, ..}) => {
                let left = Box::new(TypedExpression::try_from(&**left)?);
                let right = Box::new(TypedExpression::try_from(&**right)?);
                let op = *op;
                Ok(Expression::Binary { left, op, right})
            },
            syn::Expr::Block(syn::ExprBlock { label, block, .. }) => {
                if let Some(label) = label.as_ref() {
                    return Err((label.span().into(), anyhow!("label in blocked scope is not supported in rvv_vector")));
                }
                Ok(Expression::Block(Block::try_from(block)?))
            },
            syn::Expr::Box(_) => {
                Err((expr.span().into(), anyhow!("box expression is not supported in rvv_vector")))
            },
            syn::Expr::Break(_) => {
                Ok(Expression::Break(expr.span().into()))
            },
            syn::Expr::Call(syn::ExprCall { func, args, paren_token, .. }) => {
                let func = Box::new(TypedExpression::try_from(&**func)?);
                let args = args.iter()
                    .map(|expr| Ok(TypedExpression::try_from(expr)?))
                    .collect::<Result<Vec<TypedExpression>, Error>>()?;
                let paren_token = paren_token.span.into();
                Ok(Expression::Call { func, args, paren_token })
            },
            syn::Expr::Cast(syn::ExprCast { expr, ty, as_token, .. }) => {
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                let ty = Box::new((Type::try_from(&**ty)?, ty.span().into()));
                let as_token = as_token.span.into();
                Ok(Expression::Cast { expr, ty, as_token })
            },
            syn::Expr::Closure(_) => {
                Err((expr.span().into(), anyhow!("closure expression is not supported in rvv_vector")))
            },
            syn::Expr::Continue(_) => {
                Ok(Expression::Continue(expr.span().into()))
            },
            syn::Expr::Field(syn::ExprField { base, member, dot_token, .. }) => {
                let base = Box::new(TypedExpression::try_from(&**base)?);
                let member = (*member).clone();
                let dot_token = dot_token.span().into();
                Ok(Expression::Field { base, member, dot_token })
            },
            syn::Expr::ForLoop(syn::ExprForLoop { label, pat, expr, body, for_token, in_token, .. }) => {
                if let Some(label) = label.as_ref() {
                    return Err((label.span().into(), anyhow!("label in for loop is not supported in rvv_vector")));
                }
                let pat = (Pattern::try_from(pat)?, pat.span().into());
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                let body = Block::try_from(body)?;
                let for_token = for_token.span.into();
                let in_token = in_token.span.into();
                Ok(Expression::ForLoop { pat, expr, body, for_token, in_token })
            },
            syn::Expr::Group(_) => {
                Err((expr.span().into(), anyhow!("expression contained within invisible delimiters is not supported in rvv_vector")))
            },
            syn::Expr::If(syn::ExprIf { if_token, cond, then_branch, else_branch, ..}) => {
                let if_token = if_token.span.into();
                let cond = Box::new(TypedExpression::try_from(&**cond)?);
                let then_branch = Block::try_from(then_branch)?;
                let else_branch = else_branch
                    .as_ref()
                    .map::<Result<_, Error>, _>(|(else_span, expr)| Ok((else_span.span.into(), Box::new(TypedExpression::try_from(&**expr)?))))
                    .transpose()?;
                Ok(Expression::If { if_token, cond, then_branch, else_branch })
            },
            syn::Expr::Index(syn::ExprIndex { expr, index, bracket_token, .. }) => {
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                let index = Box::new(TypedExpression::try_from(&**index)?);
                let bracket_token = bracket_token.span.into();
                Ok(Expression::Index { expr, index, bracket_token })
            },
            syn::Expr::Let(_) => {
                Err((expr.span().into(), anyhow!("let guard is not supported in rvv_vector")))
            },
            syn::Expr::Lit(syn::ExprLit{ lit, .. }) => {
                Ok(Expression::Lit((*lit).clone()))
            },
            syn::Expr::Loop(syn::ExprLoop{ label, body, loop_token, .. }) => {
                if let Some(label) = label.as_ref() {
                    return Err((label.span().into(), anyhow!("label in loop is not supported in rvv_vector")));
                }
                let body = Block::try_from(body)?;
                let loop_token = loop_token.span.into();
                Ok(Expression::Loop{body, loop_token})
            },
            syn::Expr::Macro(syn::ExprMacro { mac, .. }) => {
                Ok(Expression::Macro((*mac).clone()))
            },
            syn::Expr::Match(_) => {
                Err((expr.span().into(), anyhow!("match expression is not supported in rvv_vector")))
            },
            syn::Expr::MethodCall(syn::ExprMethodCall { receiver, method, turbofish, args, dot_token, paren_token, .. }) => {
                if let Some(turbofish) = turbofish.as_ref() {
                    return Err((turbofish.span().into(), anyhow!("explicit type parameters passed to a method call is not supported in rvv_vector")));
                }
                let receiver = Box::new(TypedExpression::try_from(&**receiver)?);
                let method = (*method).clone();
                let args = args.iter()
                    .map(TypedExpression::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                let dot_token = dot_token.span().into();
                let paren_token = paren_token.span.into();
                Ok(Expression::MethodCall { receiver, method, args, dot_token, paren_token })
            },
            syn::Expr::Paren(syn::ExprParen { expr, paren_token, .. }) => {
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                let paren_token = paren_token.span.into();
                Ok(Expression::Paren{expr, paren_token})
            },
            syn::Expr::Path(syn::ExprPath{ qself, path, .. }) => {
                if let Some(qself) = qself.as_ref() {
                    return Err((qself.lt_token.span().into(), anyhow!("explicit Self type in a qualified path is not supported in rvv_vector")));
                }
                Ok(Expression::Path((*path).clone()))
            },
            syn::Expr::Range(syn::ExprRange { from, limits, to, .. }) => {
                let from = from.as_ref().map::<Result<_, Error>, _>(|expr| Ok(Box::new(TypedExpression::try_from(&**expr)?))).transpose()?;
                let limits = *limits;
                let to = to.as_ref().map::<Result<_, Error>, _>(|expr| Ok(Box::new(TypedExpression::try_from(&**expr)?))).transpose()?;
                Ok(Expression::Range { from, limits, to })
            },
            syn::Expr::Reference(syn::ExprReference{ and_token, mutability, expr, .. }) => {
                let and_token = and_token.span().into();
                let mutability = mutability.as_ref().map(|mutability| mutability.span.into());
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                Ok(Expression::Reference { and_token, mutability, expr })
            },
            syn::Expr::Repeat(syn::ExprRepeat { expr, len, bracket_token, semi_token, .. }) => {
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                let len = Box::new(TypedExpression::try_from(&**len)?);
                let bracket_token = bracket_token.span.into();
                let semi_token = semi_token.span().into();
                Ok(Expression::Repeat { expr, len, bracket_token, semi_token })
            },
            syn::Expr::Return(syn::ExprReturn { expr, return_token, .. }) => {
                let expr = expr
                    .as_ref()
                    .map::<Result<_, Error>, _>(|expr| Ok(Box::new(TypedExpression::try_from(&**expr)?)))
                    .transpose()?;
                let return_token = return_token.span.into();
                Ok(Expression::Return{expr, return_token })
            },
            syn::Expr::Struct(_) => {
                Err((expr.span().into(), anyhow!("struct literal expression is not supported in rvv_vector")))
            },
            syn::Expr::Try(_) => {
                Err((expr.span().into(), anyhow!("try-expression is not supported in rvv_vector")))
            },
            syn::Expr::TryBlock(_) => {
                Err((expr.span().into(), anyhow!("try block is not supported in rvv_vector")))
            },
            syn::Expr::Tuple(_) => {
                Err((expr.span().into(), anyhow!("tuple expression is not supported in rvv_vector")))
            },
            syn::Expr::Type(_) => {
                Err((expr.span().into(), anyhow!("type ascription expression is not supported in rvv_vector")))
            },
            syn::Expr::Unary(syn::ExprUnary { op, expr, .. }) => {
                let op = *op;
                let expr = Box::new(TypedExpression::try_from(&**expr)?);
                Ok(Expression::Unary { op, expr })
            },
            syn::Expr::Unsafe(_) => {
                Err((expr.span().into(), anyhow!("unsafe block is not supported in rvv_vector")))
            },
            syn::Expr::Verbatim(_) => {
                Err((expr.span().into(), anyhow!("Tokens in expression position that not interpreted by syn is not supported in rvv_vector")))
            },
            syn::Expr::While(_) => {
                Err((expr.span().into(), anyhow!("while loop is not supported in rvv_vector")))
            },
            syn::Expr::Yield(_) => {
                Err((expr.span().into(), anyhow!("yield expression is not supported in rvv_vector")))
            },
            expr => {
                Err((expr.span().into(), anyhow!("all other kind of expression is not supported in rvv_vector")))
            }
        }
    }
}

impl TryFrom<&syn::Stmt> for Statement {
    type Error = Error;
    fn try_from(stmt: &syn::Stmt) -> Result<Statement, Error> {
        match stmt {
            syn::Stmt::Local(syn::Local {
                pat,
                init,
                let_token,
                semi_token,
                ..
            }) => {
                if init.is_none() {
                    return Err((
                        stmt.span().into(),
                        anyhow!(
                        "local let binding without init expression is not supported in rvv_vector"
                    ),
                    ));
                }
                let pat_span: Span = pat.span().into();
                let pat = (Pattern::try_from(pat)?, pat_span);
                match &pat.0 {
                    Pattern::Ident { .. } => {}
                    Pattern::Type { pat, .. } => match &pat.0 {
                        Pattern::Ident { .. } => {}
                        _ => {
                            return Err((
                                pat_span,
                                anyhow!("complex local let binding is not supported in rvv_vector"),
                            ));
                        }
                    },
                    _ => {
                        return Err((
                            pat_span,
                            anyhow!("complex local let binding is not supported in rvv_vector"),
                        ));
                    }
                }
                let (eq_token, init) = init
                    .as_ref()
                    .map(|(eq_token, expr)| {
                        Ok((eq_token.span().into(), TypedExpression::try_from(&**expr)?))
                    })
                    .transpose()?
                    .unwrap();
                Ok(Statement::Local {
                    pat,
                    init,
                    eq_token,
                    let_token: let_token.span.into(),
                    semi_token: semi_token.span().into(),
                })
            }
            syn::Stmt::Item(_) => Err((
                stmt.span().into(),
                anyhow!("item definition is not supported in rvv_vector"),
            )),
            syn::Stmt::Expr(expr) => Ok(Statement::Expr(TypedExpression::try_from(expr)?)),
            syn::Stmt::Semi(expr, _) => Ok(Statement::Semi(TypedExpression::try_from(expr)?)),
        }
    }
}

impl TryFrom<&syn::Block> for Block {
    type Error = Error;
    fn try_from(block: &syn::Block) -> Result<Block, Error> {
        let stmts = block
            .stmts
            .iter()
            .map(|stmt| Ok((Statement::try_from(stmt)?, stmt.span().into())))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Block {
            span: block.span().into(),
            brace_token: block.brace_token.span.into(),
            stmts,
        })
    }
}

impl TryFrom<&syn::FnArg> for FnArg {
    type Error = Error;
    fn try_from(fn_arg: &syn::FnArg) -> Result<FnArg, Error> {
        match fn_arg {
            syn::FnArg::Receiver(_) => Err((
                fn_arg.span().into(),
                anyhow!("method function is not supported in rvv_vector"),
            )),
            syn::FnArg::Typed(syn::PatType {
                pat,
                ty,
                colon_token,
                ..
            }) => {
                let (mutability, name) = match Pattern::try_from(&**pat)? {
                    Pattern::Ident { mutability, ident } => (mutability, ident),
                    _ => {
                        return Err((pat.span().into(), anyhow!("complex pattern in function argument is not supported in rvv_vector")));
                    }
                };
                Ok(FnArg {
                    span: fn_arg.span().into(),
                    mutability,
                    name,
                    colon_token: colon_token.span().into(),
                    ty: Box::new((Type::try_from(&**ty)?, ty.span().into())),
                })
            }
        }
    }
}

impl TryFrom<&syn::Signature> for Signature {
    type Error = Error;
    fn try_from(sig: &syn::Signature) -> Result<Signature, Error> {
        if let Some(constness) = sig.constness.as_ref() {
            return Err((
                constness.span().into(),
                anyhow!("const function is not supported by rvv_vector"),
            ));
        }
        if let Some(asyncness) = sig.asyncness.as_ref() {
            return Err((
                asyncness.span().into(),
                anyhow!("async function is not supported by rvv_vector"),
            ));
        }
        if let Some(unsafety) = sig.unsafety.as_ref() {
            return Err((
                unsafety.span().into(),
                anyhow!("unsafe function is not supported by rvv_vector"),
            ));
        }
        if let Some(abi) = sig.abi.as_ref() {
            return Err((
                abi.span().into(),
                anyhow!("extern \"C\" function is not supported by rvv_vector"),
            ));
        }
        if let Some(lt_token) = sig.generics.lt_token.as_ref() {
            return Err((
                sig.generics.span().into(),
                anyhow!("generic type parameter is not supported by rvv_vector"),
            ));
        }
        if let Some(variadic) = sig.variadic.as_ref() {
            return Err((
                variadic.span().into(),
                anyhow!("variadic argument is not supported by rvv_vector"),
            ));
        }
        let inputs = sig
            .inputs
            .iter()
            .map(FnArg::try_from)
            .collect::<Result<Vec<_>, Error>>()?;
        let output = (ReturnType::try_from(&sig.output)?, sig.output.span().into());
        Ok(Signature {
            span: sig.span().into(),
            fn_token: sig.fn_token.span.into(),
            paren_token: sig.paren_token.span.into(),
            ident: sig.ident.clone(),
            inputs,
            output,
        })
    }
}

impl TryFrom<&syn::ItemFn> for ItemFn {
    type Error = Error;

    fn try_from(item_fn: &syn::ItemFn) -> Result<ItemFn, Error> {
        Ok(ItemFn {
            span: item_fn.span().into(),
            vis: item_fn.vis.clone(),
            sig: Signature::try_from(&item_fn.sig)?,
            block: Block::try_from(&*item_fn.block)?,
        })
    }
}
