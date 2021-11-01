use hacspec::ast::{
    rvv_vectorSpan,
    Spanned,
    LocalIdent,
    TopLevelIdent,
    Ident,
    VarSet,
    Borrowing,
    ArraySize,
    Secrecy,
    TypVar,
    BaseTyp,
    Typ,
    Literal,
    UnOpKind,
    BinOpKind,
    Expression,
    Pattern,
    MutatedInfo,
    Fillable,
    Statement,
    Block,
    FuncSig,
    ExternalFuncSig,
    Item,
    ItemTag,
    ItemTagSet,
    DecoratedItem,
    Program,
};
use proc_macro2::Span;
use anyhow::{Result, bail, anyhow};

enum ExprTranslationResultMaybeQuestionMark {
    TransExpr(Expression, bool), // true if ends with question mark
    TransStmt(Statement),
}
enum ExprTranslationResult {
    TransExpr(Expression),
    TransStmt(Statement),
}

fn translate_toplevel_ident(ident: &syn::Ident) -> Spanned<TopLevelIdent> {
    (TopLevelIdent(ident.to_string()), ident.span().into())
}

fn translate_ident(ident: &syn::Ident) -> Spanned<Ident> {
    (Ident::Unresolved(ident.to_string()), ident.span().into())
}


fn translate_type_args(args: &syn::AngleBracketedGenericArguments) -> Result<Vec<Spanned<BaseTyp>>> {
    let span = args.lt_token.spans[0];
    args.args
        .iter()
        .map(|arg| {
            match arg {
                // pub enum GenericArgument {
                //     Lifetime(Lifetime),
                //     Type(Type),
                //     Binding(Binding),
                //     Constraint(Constraint),
                //     Const(Expr),
                // }
                syn::GenericArgument::Lifetime(_) => {
                    bail!("lifetime type parameters are not allowed in rvv_vectort: {:?}", span);
                }
                syn::GenericArgument::Type(ty) => {
                    let (type_arg, _) = translate_base_typ(ty, span)?;
                    Ok((type_arg, span))
                }
                syn::GenericArgument::Binding(binding) => {
                    bail!("associated type parameters are not allowed in rvv_vectort: {:?}", binding.ident.span());
                }
                syn::GenericArgument::Constraint(constraint) => {
                    bail!("associated type parameters are not allowed in rvv_vectort: {:?}", constraint.ident.span());
                }
                syn::GenericArgument::Const(expr) => {
                    bail!("const generics are not allowed in rvv_vector: {:?}", span);
                }
            }
        })
        .collect()
}

fn translate_base_typ(ty: &syn::Type, span: &Span) -> Result<Spanned<BaseTyp>> {
    // pub enum syn::Type {
    //     Array(TypeArray),
    //     BareFn(TypeBareFn),
    //     Group(TypeGroup),
    //     ImplTrait(TypeImplTrait),
    //     Infer(TypeInfer),
    //     Macro(TypeMacro),
    //     Never(TypeNever),
    //     Paren(TypeParen),
    //     Path(TypePath),
    //     Ptr(TypePtr),
    //     Reference(TypeReference),
    //     Slice(TypeSlice),
    //     TraitObject(TypeTraitObject),
    //     Tuple(TypeTuple),
    //     Verbatim(TokenStream),
    //     // some variants omitted
    // }
    match ty {
        syn::Type::Path(syn::TypePath { qself, path }) => {
            if qself.is_some() {
                bail!("trait associated types not allowed in rvv_vector: {:?}", span);
            }
            if path.segments.len() > 1 {
                bail!("multiple path segments not allowed in rvv_vector: {:?}", span);
            }
            match path.segments.first() {
                Some(seg) => {
                    match seg.arguments {
                        syn::PathArguments::None => {
                            let span = seg.ident.span();
                            match seg.ident.to_string().as_str() {
                                "u32" => Ok((BaseTyp::UInt32, span.into())),
                                "i32" => Ok((BaseTyp::Int32, span.into())),
                                "u8" => Ok((BaseTyp::UInt8, span.into())),
                                "i8" => Ok((BaseTyp::Int8, span.into())),
                                "u16" => Ok((BaseTyp::UInt16, span.into())),
                                "i16" => Ok((BaseTyp::Int16, span.into())),
                                "u64" => Ok((BaseTyp::UInt64, span.into())),
                                "i64" => Ok((BaseTyp::Int64, span.into())),
                                "u128" => Ok((BaseTyp::UInt128, span.into())),
                                "i128" => Ok((BaseTyp::Int128, span.into())),
                                "u256" => Ok((BaseTyp::UInt256, span.into())),
                                "bool" => Ok((BaseTyp::Bool, span.into())),
                                "usize" => Ok((BaseTyp::Usize, span.into())),
                                "isize" => Ok((BaseTyp::Isize, span.into())),
                                "Seq" => bail!("Seq expects a type argument: {:?}", span),
                                _ => {
                                    let name = translate_toplevel_ident(&seg.ident);
                                    Ok((BaseTyp::Named(name, None), span))
                                },
                            }
                        }
                        syn::PathArguments::AngleBracketed(arg) => {
                            let name = translate_toplevel_ident(&seg.ident);
                            let arg = translate_type_args(arg, span)?;
                            Ok((BaseTyp::Named(name, Some(arg)), span))
                        }
                        syn::PathArguments::Parenthesized(_) => {
                            bail!("parenthesized path arguments are not allowed in rvv_vector: {:?}", span);
                        }
                    }
                }
                None => bail!("empty path are not allowed in rvv_vector: {:?}", span),
            }
        }
        syn::Type::Tuple(syn::TypeTuple { paren_token, elems }) => {
            let span = paren_token.span;
            let rtys = elems
                .iter()
                .map(|ty| translate_base_typ(ty, span))
                .collect::<Result<Vec<_>>>()?;
            Ok((BaseTyp::Tuple(rtys), span.into()))
        }
        syn::Type::Reference(_) => {
            bail!("double references not allowed in rvv_vector");
        }
        _ => {
            bail!("type not allowed in rvv_vector: {:?}", span);
        }
    }
}


fn translate_typ(ty: &syn::Type, span: &Span) -> Result<Spanned<Typ>> {
    match ty {
        // Dereference
        syn::Type::Reference(type_ref) => {
            let span = type_ref.and_token.spans[0];
            if type_ref.lifetime.is_some() {
                bail!("lifetime annotations are not allowed in rvv_vector");
            } else if type_ref.is_mut() {
                bail!("mutable function arguments are not allowed");
            } else {
                translate_base_typ(type_ref.elem, span)
            }
        }
        _ => translate_base_typ(ty)
    }
}

fn translate_literal(lit: &syn::ExprLit, span: &Span) -> Result<Spanned<ExprTranslationResult>> {
    unimplemented!()
}

fn translate_expr_name(path: &syn::Path, span: &Span) -> Result<Spanned<ExprTranslationResult>> {
    unimplemented!()
}

fn translate_binop(x: &syn::BinOp) -> BinOpKind {
    unimplemented!()
}

fn translate_expr(expr: &syn::Expr, span: &Span) -> Result<Spanned<ExprTranslationResult>> {
    // pub enum Expr {
    //     Array(ExprArray),
    //     Assign(ExprAssign),
    //     AssignOp(ExprAssignOp),
    //     Async(ExprAsync),
    //     Await(ExprAwait),
    //     Binary(ExprBinary),
    //     Block(ExprBlock),
    //     Box(ExprBox),
    //     Break(ExprBreak),
    //     Call(ExprCall),
    //     Cast(ExprCast),
    //     Closure(ExprClosure),
    //     Continue(ExprContinue),
    //     Field(ExprField),
    //     ForLoop(ExprForLoop),
    //     Group(ExprGroup),
    //     If(ExprIf),
    //     Index(ExprIndex),
    //     Let(ExprLet),
    //     Lit(ExprLit),
    //     Loop(ExprLoop),
    //     Macro(ExprMacro),
    //     Match(ExprMatch),
    //     MethodCall(ExprMethodCall),
    //     Paren(ExprParen),
    //     Path(ExprPath),
    //     Range(ExprRange),
    //     Reference(ExprReference),
    //     Repeat(ExprRepeat),
    //     Return(ExprReturn),
    //     Struct(ExprStruct),
    //     Try(ExprTry),
    //     TryBlock(ExprTryBlock),
    //     Tuple(ExprTuple),
    //     Type(ExprType),
    //     Unary(ExprUnary),
    //     Unsafe(ExprUnsafe),
    //     Verbatim(TokenStream),
    //     While(ExprWhile),
    //     Yield(ExprYield),
    //     // some variants omitted
    // }

    match expr {
        syn::Expr::Binary(expr_binary) => {
            Ok((ExprTranslationResult::TransExpr(Expression::Binary(
                (translate_binop(&expr_binary.op, span.into())),
                Box::new(translate_expr_expects_exp(&expr_binary.left, span)?),
                Box::new(translate_expr_expects_exp(&expr_binary.right, span)?),
                None,
            ))))
        },
        syn::Expr::Unary(expr_unary) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Path(expr_path) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Call(expr_call) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::MethodCall(expr_methodcall) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Lit(expr_lit) => translate_literal(expr_lit, span),
        syn::Expr::Assign(expr_assign) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::If(expr_if) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::ForLoop(expr_forloop) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Index(expr_index) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Tuple(expr_tuple) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Struct(expr_struct) => {
            Err(anyhow!("structs are not supported yet in rvv_vector: {}", span));
        },
        syn::Expr::Box(expr_box) => {
            Err(anyhow!("boxing is not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Array(expr_array) => {
            // FIXME:
            unimplemented!()
        }
        syn::Expr::Cast(expr_cast) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Type(expr_type) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Let(expr_let) => {
            Err(anyhow!("inline lets are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::While(expr_while) => {
            Err(anyhow!("while loops are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Loop(expr_loop) => {
            Err(anyhow!("undecorated loops are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Match(expr_match) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Closure(expr_closure) => {
            Err(anyhow!("closures are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Block(expr_block) => {
            Err(anyhow!("inline blocks are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Async(expr_async) => {
            Err(anyhow!("async/await statements are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Await(expr_await) => {
            Err(anyhow!("async/await statements are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::TryBlock(expr_tryblock) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::AssignOp(expr_assignop) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Field(expr_field) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Range(expr_range) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Reference(expr_reference) => {
            // FIXME:
            unimplemented!()
        },
        syn::Expr::Break(expr_break) => {
            Err(anyhow!("break statements are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Continue(expr_continue) => {
            Err(anyhow!("early return statements are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Return(expr_return) => {
            Err(anyhow!("early return statements are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Macro(expr_macro) => {
            Err(anyhow!("macro calls are not allowed in rvv_vector: {}", span));
        },
        syn::Expr::Repeat(expr_repeat) => {
            Err(anyhow!("repeat statements are not allowed in rvv_vector: {}", span))
        },
        syn::Expr::Yield(expr_yield) => {
            Err(anyhow!("yield statements are not allowed in rvv_vector: {}", span))
        },
        syn::Expr::Paren(expr_paren) => translate_expr(&expr_paren.expr, &expr_paren.paren_token.span),
        syn::Expr::Try(expr_try) => {
            Err(anyhow!("question marks inside expressions are not allowed in rvv_vector: {}", span))
        },
        syn::Expr::Group(expr_group) => {
            Err(anyhow!("syn::ExprGroup are not allowed in rvv_vector: {}", span))
        },
        syn::Expr::Unsafe(expr_unsafe) => {
            Err(anyhow!("unsafe blocks are not allowed in rvv_vector: {}", span))
        },
        syn::Expr::Verbatim(token_stream) => {
            Err(anyhow!("Tokens in expression position not interpreted by Syn: {}", span))
        },
    }
}

fn translate_expr_expects_exp(expr: &syn::Expr, span: &Span) -> Result<Spanned<Expression>> {
    match translate_expr(expr, span)? {
        (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
        (ExprTranslationResult::TransStmt(_), span) => {
            Err(anyhow!("statements inside expressions are not allowed in rvv_vector: {}", span))
        }
    }
}

fn translate_struct_name(path: &syn::Path, span: &Span) -> Result<TopLevelIdent> {
    // FIXME:
    unimplemented!()
}

fn translate_expr_accepts_question_mark(
    expr: &syn::Expr,
    span: &Span,
) -> Result<Spanned<ExprTranslationResultMaybeQuestionMark>> {
    match expr {
        syn::Expr::Try(expr_try) => {
            let (result, span) = translate_expr(expr_try.expr, expr_try.question_token.spans[0])?;
            match result {
                ExprTranslationResult::TransExpr(e) => Ok((ExprTranslationResultMaybeQuestionMark::TransExpr(e, true), span)),
                ExprTranslationResult::TransStmt(_) => {
                    Err(anyhow!("question-marked blobs cannot contain statements in rvv_vector, only pure expressions: {}", span))
                }
            }
        }
        _ => {
            let (result, span) = translate_expr(expr, span)?;
            match result {
                ExprTranslationResult::TransExpr(e) => Ok((
                    ExprTranslationResultMaybeQuestionMark::TransExpr(e, false),
                    span,
                )),
                ExprTranslationResult::TransStmt(s) => {
                    Ok((ExprTranslationResultMaybeQuestionMark::TransStmt(s), span))
                }
            }
        }
    }
}
fn translate_array_decl() {}
fn translate_natural_integer_decl() {}
fn translate_simplified_natural_integer_decl() {}

fn translate_pattern(pat: &syn::Pat, span: &Span) -> Result<(Spanned<Pattern>, Option<Spanned<Typ>>)> {
    match pat {
        syn::Pat::Ident(pat_ident) => {
            // pub struct PatIdent {
            //     pub attrs: Vec<Attribute>,
            //     pub by_ref: Option<Ref>,
            //     pub mutability: Option<Mut>,
            //     pub ident: Ident,
            //     pub subpat: Option<(At, Box<Pat>)>,
            // }
            if pat_ident.by_ref.is_some() {
                bail!("pattern not allowed in rvv_vector let bindings: {}", rvv_vector::from(span));
            }
            if pat_ident.subpat.is_some() {
                bail!("pattern not allowed in rvv_vector let bindings: {}", rvv_vector::from(span));
            }
            let (ident, span) = translate_ident(pat_ident.ident);
            Ok(((Pattern::IdentPat(ident), span), None))
        }
        syn::Pat::Type(pat_type) => {
            let (pattern, typ_opt) = translate_pattern(pat_type.pat, pat_type.colon_token.spans[0])?;
            if type_opt.is_some() {
                bail!("pattern not allowed in rvv_vector let bindings: {}", rvv_vector::from(span));
            }
            let typ = translate_typ(pat_type.ty)?;
            Ok(pattern, Some(typ))
        }
        syn::Pat::Tuple(pat_tuple) => {
            let span = pat_tuple.paren_token.span;
            let pats = pat_tuple
                .elems
                .iter()
                .map(|pat| translate_pattern(pat, &span))
                .collect::<Result<Vec<_>>>()?;
            Ok((Pattern::Tuple(pats), span))
        }
        syn::Pat::TupleStruct(pat_tuple_struct) => {
            let struct_name = translate_struct_name(&pat_tuple_struct.path, span)?;
            let ts_span = pat_tuple_struct.pat.paren_token.span;
            let pattern = if pat_tuple_struct.pat.elems.len() == 1 {
                translate_pattern(pat_tuple_struct.pat.elems.first().unwrap(), ts_span)?
            } else {
                let pats = pat_tuple_struct.pat.
                    .elems
                    .iter()
                    .map(|pat| translate_pattern(pat, &ts_span))
                    .collect::<Result<Vec<_>>>()?;
                (Pattern::Tuple(pats), ts_span)
            };
            Ok((Pattern::SingleCaseEnum((struct_name, span.into()), Box::new(pattern))))
        }
        syn::Pat::Wild(pat_wild) => {
            Ok((Pattern::WildCard, span.into()))
        }
        _ => {
            bail!("pattern not allowed in rvv_vector let bindings: {}", rvv_vector::from(span));
        }
    }
}

fn translate_statement(stmt: &syn::Stmt) -> Result<Spanned<Statement>> {
    match stmt {
        syn::Stmt::Local(syn::Local{ pat, init, let_token, .. }) => {
            // let x: Type = a.parse();
            let span = &let_token.span;
            let (pat, ty) = translate_pattern(pat, span)?;
            match init {
                None => bail!("let-bindings without initialization are not allowed in rvv_vector: {}", span);
                Some((eq, expr)) => {}
            }
        }
        syn::Stmt::Item(item) => bail!("block-local items are not allowed in rvv_vector"),
        syn::Stmt::Expr(expr) => {
        }
        syn::Stmt::Semi(expr, _semi) => {
        }
    }
}

fn translate_block(block: &syn::Block) -> Result<Spanned<Block>> {
    let span = block.brace_token.span;
    let stmts = block
        .stmts
        .iter()
        .map(|stmt| translate_statement(stmt))
        .collect::<Result<Vec<_>>>()?;
    Ok((
        Block {
            stmts,
            return_typ: None,
            mutated: None,
            contains_question_mark: None,
            // We initialize these fields to None as they are
            // to be filled by the typechecker
        },
        span.into(),
    ))
}

fn translate_item(item: &syn::Item) -> Result<Item> {
    match item {
        syn::Item::Const(item) => {
            unimplemented!()
        }
        syn::Item::Enum(item) => {
            unimplemented!()
        }
        syn::Item::ExternCrate(item) => {
            unimplemented!()
        }
        /*
        pub struct Signature {
            constness: Option<Const>,
            asyncness: Option<Async>,
            unsafety: Option<Unsafe>,
            abi: Option<Abi>,
            fn_token: Fn,
            ident: Ident,
            generics: Generics,
            paren_token: Paren,
            inputs: Punctuated<FnArg, Comma>,
            variadic: Option<Variadic>,
            output: ReturnType,
        }
        */
        syn::Item::Fn(syn::ItemFn {sig, block, ..}) => {
            let sig_span = rvv_vectorSpan::from(sig.ident.span());
            if sig.unsafety.is_some() {
                bail!("unsafe functions not allowed in rvv_vector: {}", sig_span);
            }
            if sig.asyncness.is_some() {
                bail!("async functions not allowed in rvv_vector: {}", sig_span);
            }
            if sig.constness.is_some() {
                bail!("const functions not allowed in rvv_vector: {}", sig_span);
            }
            if sig.abi.is_some() {
                bail!("extern functions not allowed in rvv_vector: {}", sig_span);
            }
            if sig.variadic.is_some() {
                bail!("variadic functions not allowed in rvv_vector: {}", sig_span);
            }
            if !sig.generics.params.is_empty() {
                bail!("generics are not allowed in rvv_vector: {}", sig_span);
            }
            let fn_inputs = sig
                .inputs
                .iter()
                .map(|(fn_arg, _comma)| {
                    match fn_arg {
                        syn::FnArg::Typed(syn::PatType{pat, ty, ..}) => {
                            match &**pat {
                                syn::Pat::Ident(pat) if pat.by_ref.is_none() && pat.subpat.is_none() => {
                                    let id = translate_ident(&pat.ident);
                                    let ty = translate_typ(&ty, pat.ident.span());
                                    Ok((id, ty))
                                }
                                _ => {
                                    Err(anyhow!("pattern destructuring in function arguments not allowed in rvv_vector"))
                                }
                            }
                        }
                        _ => {
                            Err(anyhow!("pattern destructuring in function arguments not allowed in rvv_vector"))
                        }
                    }
                })
                .collect::<Result<Vec<(Spanned<Ident>, Spanned<Typ>)>>>()?;
            let fn_output = match sig.output {
                syn::ReturnType::Default => (BaseTyp::Unit, sig_span.into()),
                syn::ReturnType::Type(arrow, ty) => translate_base_typ(ty, arrow.spans[1])?,
            };
            let fn_body: Spanned<Block> = translate_block(block)
        }
        syn::Item::ForeignMod(item) => {
            unimplemented!()
        }
        syn::Item::Impl(item) => {
            unimplemented!()
        }
        syn::Item::Macro(item) => {
            unimplemented!()
        }
        syn::Item::Macro2(item) => {
            unimplemented!()
        }
        syn::Item::Mod(item) => {
            unimplemented!()
        }
        syn::Item::Static(item) => {
            unimplemented!()
        }
        syn::Item::Struct(item) => {
            unimplemented!()
        }
        syn::Item::Trait(item) => {
            unimplemented!()
        }
        syn::Item::TraitAlias(item) => {
            unimplemented!()
        }
        syn::Item::Type(item) => {
            unimplemented!()
        }
        syn::Item::Union(item) => {
            unimplemented!()
        }
        syn::Item::Use(item) => {
            unimplemented!()
        }
        syn::Item::Verbatim(token_stream) => {
            unimplemented!()
        }
    }
}
