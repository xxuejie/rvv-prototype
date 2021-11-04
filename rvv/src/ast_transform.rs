use std::convert::TryFrom;

use anyhow::{anyhow, bail, Error};

use crate::ast::{
    BareFnArg, Block, Expression, FnArg, ItemFn, Pattern, ReturnType, Signature, Statement, Type,
    TypedExpression,
};

// ============================
// ==== impl TryFrom for T ====
// ============================
impl TryFrom<&syn::ReturnType> for ReturnType {
    type Error = Error;
    fn try_from(return_type: &syn::ReturnType) -> Result<ReturnType, Error> {
        match return_type {
            syn::ReturnType::Default => Ok(ReturnType::Default),
            syn::ReturnType::Type(_, ty) => {
                let ty = Box::new(Type::try_from(&**ty)?);
                Ok(ReturnType::Type(ty))
            }
        }
    }
}

impl TryFrom<&syn::BareFnArg> for BareFnArg {
    type Error = Error;
    fn try_from(bare_fn_arg: &syn::BareFnArg) -> Result<BareFnArg, Error> {
        let name = bare_fn_arg.name.as_ref().map(|(ident, _)| (*ident).clone());
        let ty = Type::try_from(&bare_fn_arg.ty)?;
        Ok(BareFnArg { name, ty })
    }
}

impl TryFrom<&syn::Type> for Type {
    type Error = Error;
    fn try_from(ty: &syn::Type) -> Result<Type, Error> {
        match ty {
            syn::Type::Array(syn::TypeArray { elem, len, ..}) => {
                let elem = Box::new(Type::try_from(&**elem)?);
                let len: TypedExpression = Expression::try_from(len)?.into();
                Ok(Type::Array { elem, len })
            },
            syn::Type::BareFn(syn::TypeBareFn { lifetimes, unsafety, abi, inputs, variadic, output, .. }) => {
                if lifetimes.is_some() {
                    bail!("lifetime in bare function type is not supported in rvv_vector");
                }
                if unsafety.is_some() {
                    bail!("unsafe bare function type is not supported in rvv_vector");
                }
                if abi.is_some() {
                    bail!("extern \"C\" in bare function type is not supported in rvv_vector");
                }
                if variadic.is_some() {
                    bail!("variadic argument in bare function type is not supported in rvv_vector");
                }
                let inputs = inputs.iter()
                    .map(BareFnArg::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                let output = ReturnType::try_from(output)?;
                Ok(Type::BareFn { inputs, output })
            },
            syn::Type::Group(_) => {
                Err(anyhow!("type contained within invisible delimiters is not supported in rvv_vector"))
            },
            syn::Type::ImplTrait(_) => {
                Err(anyhow!("impl Trait type is not supported in rvv_vector"))
            },
            syn::Type::Infer(_) => {
                Err(anyhow!("type should be inferred by the compiler is not supported in rvv_vector"))
            },
            syn::Type::Macro(_) => {
                Err(anyhow!("macro in the type position is not supported in rvv_vector"))
            },
            syn::Type::Never(_) => {
                Err(anyhow!("never type(!) is not supported in rvv_vector"))
            },
            syn::Type::Paren(syn::TypeParen{ elem, .. }) => {
                // pub struct TypeParen {
                //     pub paren_token: Paren,
                //     pub elem: Box<Type>,
                // }
                Ok(Type::try_from(&**elem)?)
            },
            syn::Type::Path(syn::TypePath { qself, path }) => {
                if qself.is_some() {
                    bail!("self-type in path type is not supported in rvv_vector");
                }
                Ok(Type::Path((*path).clone()))
            },
            syn::Type::Ptr(_) => {
                Err(anyhow!("raw pointer type is not supported in rvv_vector"))
            },
            syn::Type::Reference(syn::TypeReference{ lifetime, mutability, elem, .. }) => {
                let lifetime = lifetime.as_ref().map(|lifetime| lifetime.ident.clone());
                let mutability = mutability.is_some();
                let elem = Box::new(Type::try_from(&**elem)?);
                Ok(Type::Reference { mutability, lifetime, elem })
            },
            syn::Type::Slice(syn::TypeSlice{ elem, .. }) => {
                let elem = Box::new(Type::try_from(&**elem)?);
                Ok(Type::Slice(elem))
            },
            syn::Type::TraitObject(_) => {
                Err(anyhow!("trait object type is not supported in rvv_vector"))
            },
            syn::Type::Tuple(syn::TypeTuple { elems, .. }) => {
                let elems = elems.iter()
                    .map(Type::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Type::Tuple(elems))
            },
            syn::Type::Verbatim(_) => {
                Err(anyhow!("Tokens in type position that not interpreted by syn is not supported in rvv_vector"))
            },
            // some variants omitted
            ty => {
                Err(anyhow!("all other kind of type is not supported in rvv_vector: {:?}", ty))
            }
        }
    }
}

impl TryFrom<&syn::Pat> for Pattern {
    type Error = Error;
    fn try_from(pat: &syn::Pat) -> Result<Pattern, Error> {
        match pat {
            syn::Pat::Box(_) => {
                Err(anyhow!("box pattern is not supported in rvv_vector"))
            },
            syn::Pat::Ident(syn::PatIdent { by_ref, mutability, ident, subpat, .. }) => {
                if by_ref.is_some() {
                    bail!("ref pattern is not supported in rvv_vector");
                }
                if subpat.is_some() {
                    bail!("sub-pattern is not supported in rvv_vector");
                }
                let mutability = mutability.is_some();
                let ident = (*ident).clone();
                Ok(Pattern::Ident{ mutability, ident })
            },
            syn::Pat::Lit(_) => {
                Err(anyhow!("literal pattern is not supported in rvv_vector"))
            },
            syn::Pat::Macro(_) => {
                Err(anyhow!("macro in pattern position is not supported in rvv_vector"))
            },
            syn::Pat::Or(_) => {
                Err(anyhow!("pattern that matches more than one case is not supported in rvv_vector"))
            },
            syn::Pat::Path(syn::PatPath { qself, path, .. }) => {
                if qself.is_some() {
                    bail!("self-type in path pattern is not supported in rvv_vector");
                }
                Ok(Pattern::Path((*path).clone()))
            },
            syn::Pat::Range(syn::PatRange { lo, limits, hi, .. }) => {
                let lo = Box::new(Expression::try_from(&**lo)?.into());
                let hi = Box::new(Expression::try_from(&**hi)?.into());
                let limits = *limits;
                Ok(Pattern::Range { lo, limits, hi })
            },
            syn::Pat::Reference(_) => {
                Err(anyhow!("reference pattern is not supported in rvv_vector"))
            },
            syn::Pat::Rest(_) => {
                Err(anyhow!("dots in a tuple or slice pattern is not supported in rvv_vector"))
            },
            syn::Pat::Slice(_) => {
                Err(anyhow!("dynamically sized slice pattern is not supported in rvv_vector"))
            },
            syn::Pat::Struct(_) => {
                Err(anyhow!("struct or struct variant pattern is not supported in rvv_vector"))
            },
            syn::Pat::Tuple(_) => {
                Err(anyhow!("tuple pattern is not supported in rvv_vector"))
            },
            syn::Pat::TupleStruct(_) => {
                Err(anyhow!("tuple struct or tuple variant pattern is not supported in rvv_vector"))
            },
            syn::Pat::Type(syn::PatType { pat, ty, .. }) => {
                let pat = Box::new(Pattern::try_from(&**pat)?);
                let ty = Box::new(Type::try_from(&**ty)?);
                Ok(Pattern::Type { pat, ty })
            },
            syn::Pat::Verbatim(_) => {
                Err(anyhow!("Tokens in pattern position that not interpreted by syn is not supported in rvv_vector"))
            },
            syn::Pat::Wild(_) => {
                Ok(Pattern::Wild)
            },
            pat => {
                Err(anyhow!("all other kind of pattern is not supported in rvv_vector: {:?}", pat))
            }
        }
    }
}

impl TryFrom<&syn::Expr> for Expression {
    type Error = Error;
    fn try_from(expr: &syn::Expr) -> Result<Expression, Error> {
        match expr {
            syn::Expr::Array(expr_array) => {
                Ok(Expression::Array(expr_array.clone()))
            }
            syn::Expr::Assign(syn::ExprAssign { left, right, .. }) => {
                let left = Box::new(Expression::try_from(&**left)?.into());
                let right = Box::new(Expression::try_from(&**right)?.into());
                Ok(Expression::Assign { left, right})
            },
            syn::Expr::AssignOp(syn::ExprAssignOp { left, op, right, ..}) => {
                let left = Box::new(Expression::try_from(&**left)?.into());
                let right = Box::new(Expression::try_from(&**right)?.into());
                let op = *op;
                Ok(Expression::AssignOp { left, op, right})
            },
            syn::Expr::Async(_) => {
                Err(anyhow!("async block is not supported in rvv_vector"))
            },
            syn::Expr::Await(_) => {
                Err(anyhow!("await expression is not supported in rvv_vector"))
            },
            syn::Expr::Binary(syn::ExprBinary { left, op, right, ..}) => {
                let left = Box::new(Expression::try_from(&**left)?.into());
                let right = Box::new(Expression::try_from(&**right)?.into());
                let op = *op;
                Ok(Expression::Binary { left, op, right})
            },
            syn::Expr::Block(syn::ExprBlock { label, block, .. }) => {
                if label.is_some() {
                    bail!("label in blocked scope is not supported in rvv_vector");
                }
                Ok(Expression::Block(Block::try_from(block)?))
            },
            syn::Expr::Box(_) => {
                Err(anyhow!("box expression is not supported in rvv_vector"))
            },
            syn::Expr::Break(_) => {
                Ok(Expression::Break)
            },
            syn::Expr::Call(syn::ExprCall { func, args, .. }) => {
                let func = Box::new(Expression::try_from(&**func)?.into());
                let args = args.iter()
                    .map(Expression::try_from)
                    .map(|result| result.map(TypedExpression::from))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Expression::Call { func, args })
            },
            syn::Expr::Cast(syn::ExprCast { expr, ty, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                let ty = Box::new(Type::try_from(&**ty)?);
                Ok(Expression::Cast { expr, ty })
            },
            syn::Expr::Closure(_) => {
                Err(anyhow!("closure expression is not supported in rvv_vector"))
            },
            syn::Expr::Continue(_) => {
                Ok(Expression::Continue)
            },
            syn::Expr::Field(syn::ExprField { base, member, .. }) => {
                let base = Box::new(Expression::try_from(&**base)?.into());
                let member = (*member).clone();
                Ok(Expression::Field { base, member })
            },
            syn::Expr::ForLoop(syn::ExprForLoop { label, pat, expr, body, .. }) => {
                if label.is_some() {
                    bail!("label in for loop is not supported in rvv_vector");
                }
                let pat = Pattern::try_from(pat)?;
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                let body = Block::try_from(body)?;
                Ok(Expression::ForLoop { pat, expr, body })
            },
            syn::Expr::Group(_) => {
                Err(anyhow!("expression contained within invisible delimiters is not supported in rvv_vector"))
            },
            syn::Expr::If(syn::ExprIf { cond, then_branch, else_branch, ..}) => {
                let cond = Box::new(Expression::try_from(&**cond)?.into());
                let then_branch = Block::try_from(then_branch)?;
                let else_branch = else_branch
                    .as_ref()
                    .map::<Result<_, Error>, _>(|(_, expr)| Ok(Box::new(Expression::try_from(&**expr)?.into())))
                    .transpose()?;
                Ok(Expression::If { cond, then_branch, else_branch })
            },
            syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                let index = Box::new(Expression::try_from(&**index)?.into());
                Ok(Expression::Index { expr, index })
            },
            syn::Expr::Let(_) => {
                Err(anyhow!("let guard is not supported in rvv_vector"))
            },
            syn::Expr::Lit(syn::ExprLit{ lit, .. }) => {
                Ok(Expression::Lit((*lit).clone()))
            },
            syn::Expr::Loop(syn::ExprLoop{ label, body, .. }) => {
                if label.is_some() {
                    bail!("label in loop is not supported in rvv_vector");
                }
                let body = Block::try_from(body)?;
                Ok(Expression::Loop(body))
            },
            syn::Expr::Macro(syn::ExprMacro { mac, .. }) => {
                Ok(Expression::Macro((*mac).clone()))
            },
            syn::Expr::Match(_) => {
                Err(anyhow!("match expression is not supported in rvv_vector"))
            },
            syn::Expr::MethodCall(syn::ExprMethodCall { receiver, method, turbofish, args, .. }) => {
                if turbofish.is_some() {
                    bail!("explicit type parameters passed to a method call is not supported in rvv_vector");
                }
                let receiver = Box::new(Expression::try_from(&**receiver)?.into());
                let method = (*method).clone();
                let args = args.iter()
                    .map(Expression::try_from)
                    .map(|result| result.map(TypedExpression::from))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Expression::MethodCall { receiver, method, args })
            },
            syn::Expr::Paren(syn::ExprParen { expr, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                Ok(Expression::Paren(expr))
            },
            syn::Expr::Path(syn::ExprPath{ qself, path, .. }) => {
                if qself.is_some() {
                    bail!("explicit Self type in a qualified path is not supported in rvv_vector");
                }
                Ok(Expression::Path((*path).clone()))
            },
            syn::Expr::Range(syn::ExprRange { from, limits, to, .. }) => {
                let from = from.as_ref().map::<Result<_, Error>, _>(|expr| Ok(Box::new(Expression::try_from(&**expr)?.into()))).transpose()?;
                let limits = *limits;
                let to = to.as_ref().map::<Result<_, Error>, _>(|expr| Ok(Box::new(Expression::try_from(&**expr)?.into()))).transpose()?;
                Ok(Expression::Range { from, limits, to })
            },
            syn::Expr::Reference(syn::ExprReference{ mutability, expr, .. }) => {
                let mutability = mutability.is_some();
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                Ok(Expression::Reference { mutability, expr })
            },
            syn::Expr::Repeat(syn::ExprRepeat { expr, len, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                let len = Box::new(Expression::try_from(&**len)?.into());
                Ok(Expression::Repeat { expr, len })
            },
            syn::Expr::Return(syn::ExprReturn { expr, .. }) => {
                let expr_opt = expr
                    .as_ref()
                    .map::<Result<_, Error>, _>(|expr| Ok(Box::new(Expression::try_from(&**expr)?.into())))
                    .transpose()?;
                Ok(Expression::Return(expr_opt))
            },
            syn::Expr::Struct(_) => {
                Err(anyhow!("struct literal expression is not supported in rvv_vector"))
            },
            syn::Expr::Try(_) => {
                Err(anyhow!("try-expression is not supported in rvv_vector"))
            },
            syn::Expr::TryBlock(_) => {
                Err(anyhow!("try block is not supported in rvv_vector"))
            },
            syn::Expr::Tuple(_) => {
                Err(anyhow!("tuple expression is not supported in rvv_vector"))
            },
            syn::Expr::Type(_) => {
                Err(anyhow!("type ascription expression is not supported in rvv_vector"))
            },
            syn::Expr::Unary(syn::ExprUnary { op, expr, .. }) => {
                let op = *op;
                let expr = Box::new(Expression::try_from(&**expr)?.into());
                Ok(Expression::Unary { op, expr })
            },
            syn::Expr::Unsafe(_) => {
                Err(anyhow!("unsafe block is not supported in rvv_vector"))
            },
            syn::Expr::Verbatim(_) => {
                Err(anyhow!("Tokens in expression position that not interpreted by syn is not supported in rvv_vector"))
            },
            syn::Expr::While(_) => {
                Err(anyhow!("while loop is not supported in rvv_vector"))
            },
            syn::Expr::Yield(_) => {
                Err(anyhow!("yield expression is not supported in rvv_vector"))
            },
            expr => {
                Err(anyhow!("all other kind of expression is not supported in rvv_vector: {:?}", expr))
            }
        }
    }
}

impl TryFrom<&syn::Stmt> for Statement {
    type Error = Error;
    fn try_from(stmt: &syn::Stmt) -> Result<Statement, Error> {
        match stmt {
            syn::Stmt::Local(syn::Local { pat, init, .. }) => {
                if init.is_none() {
                    bail!(
                        "local let binding without init expression is not supported in rvv_vector"
                    );
                }
                let pat = Pattern::try_from(pat)?;
                match &pat {
                    Pattern::Ident { .. } => {}
                    Pattern::Type { pat, .. } => match &**pat {
                        Pattern::Ident { .. } => {}
                        _ => {
                            bail!("complex local let binding is not supported in rvv_vector");
                        }
                    },
                    _ => {
                        bail!("complex local let binding is not supported in rvv_vector");
                    }
                }
                let init = init
                    .as_ref()
                    .map(|(_, expr)| Expression::try_from(&**expr).map(Into::into))
                    .transpose()?
                    .unwrap();
                Ok(Statement::Local { pat, init })
            }
            syn::Stmt::Item(_) => Err(anyhow!("item definition is not supported in rvv_vector")),
            syn::Stmt::Expr(expr) => Ok(Statement::Expr(Expression::try_from(expr)?.into())),
            syn::Stmt::Semi(expr, _) => Ok(Statement::Semi(Expression::try_from(expr)?.into())),
        }
    }
}

impl TryFrom<&syn::Block> for Block {
    type Error = Error;
    fn try_from(block: &syn::Block) -> Result<Block, Error> {
        let stmts = block
            .stmts
            .iter()
            .map(Statement::try_from)
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Block { stmts })
    }
}

impl TryFrom<&syn::FnArg> for FnArg {
    type Error = Error;
    fn try_from(fn_arg: &syn::FnArg) -> Result<FnArg, Error> {
        match fn_arg {
            syn::FnArg::Receiver(_) => {
                Err(anyhow!("method function is not supported in rvv_vector"))
            }
            syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => {
                let (mutability, name) = match Pattern::try_from(&**pat)? {
                    Pattern::Ident { mutability, ident } => (mutability, ident),
                    _ => {
                        bail!("complex pattern in function argument is not supported in rvv_vector")
                    }
                };
                Ok(FnArg {
                    mutability,
                    name,
                    ty: Box::new(Type::try_from(&**ty)?),
                })
            }
        }
    }
}

impl TryFrom<&syn::Signature> for Signature {
    type Error = Error;
    fn try_from(sig: &syn::Signature) -> Result<Signature, Error> {
        if sig.constness.is_some() {
            bail!("const function is not supported by rvv_vector");
        }
        if sig.asyncness.is_some() {
            bail!("async function is not supported by rvv_vector");
        }
        if sig.unsafety.is_some() {
            bail!("unsafe function is not supported by rvv_vector");
        }
        if sig.abi.is_some() {
            bail!("extern \"C\" function is not supported by rvv_vector");
        }
        if sig.generics.lt_token.is_some() {
            bail!("generic type parameter is not supported by rvv_vector");
        }
        if sig.variadic.is_some() {
            bail!("variadic argument is not supported by rvv_vector");
        }
        let inputs = sig
            .inputs
            .iter()
            .map(FnArg::try_from)
            .collect::<Result<Vec<_>, Error>>()?;
        let output = ReturnType::try_from(&sig.output)?;
        Ok(Signature {
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
            vis: item_fn.vis.clone(),
            sig: Signature::try_from(&item_fn.sig)?,
            block: Block::try_from(&*item_fn.block)?,
        })
    }
}
