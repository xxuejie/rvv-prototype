use hacspec::ast::{
    HacspecSpan,
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
use anyhow::{Result, bail};

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
                    bail!("lifetime type parameters are not allowed in Hacspect: {:?}", span);
                }
                syn::GenericArgument::Type(ty) => {
                    let (type_arg, _) = translate_base_typ(ty, span)?;
                    Ok((type_arg, span))
                }
                syn::GenericArgument::Binding(binding) => {
                    bail!("associated type parameters are not allowed in Hacspect: {:?}", binding.ident.span());
                }
                syn::GenericArgument::Constraint(constraint) => {
                    bail!("associated type parameters are not allowed in Hacspect: {:?}", constraint.ident.span());
                }
                syn::GenericArgument::Const(expr) => {
                    bail!("const generics are not allowed in Hacspec: {:?}", span);
                }
            }
        })
        .collect()
}

fn translate_base_typ(ty: &syn::Type, span: &syn::Span) -> Result<Spanned<BaseTyp>> {
    // pub enum Type {
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
                bail!("trait associated types not allowed in Hacspec: {:?}", span);
            }
            if path.segments.len() > 1 {
                bail!("multiple path segments not allowed in Hacspec: {:?}", span);
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
                                "i256" => Ok((BaseTyp::Int256, span.into())),
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
                            bail!("parenthesized path arguments are not allowed in Hacspec: {:?}", span);
                        }
                    }
                }
                None => bail!("empty path are not allowed in Hacspec: {:?}", span),
            }
        }
        syn::Type::Tuple(tuple) => {
        }
        syn::Type::Reference(_) => {
            bail!("double references not allowed in Hacspec");
        }
        _ => {
            bail!("type not allowed in Hacspec: {:?}", span);
        }
    }
}


fn translate_typ(ty: &syn::Type, span: &syn::Span) -> Result<Spanned<Typ>> {
    match ty {
        // Dereference
        syn::Type::Reference(type_ref) => {
            let span = type_ref.and_token.spans[0];
            if type_ref.lifetime.is_some() {
                bail!("lifetime annotations are not allowed in Hacspec");
            } else if type_ref.is_mut() {
                bail!("mutable function arguments are not allowed");
            } else {
                translate_base_typ(type_ref.elem, span)
            }
        }
        _ => translate_base_typ(ty)
    }
}
fn translate_expr_expects_exp() {}
fn translate_array_decl() {}
fn translate_natural_integer_decl() {}
fn translate_simplified_natural_integer_decl() {}

fn translate_pattern(pat: &syn::Pat, span: &syn::Span) -> Result<(Spanned<Pattern>, Option<Spanned<Typ>>)> {
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
                bail!("pattern not allowed in Hacspec let bindings: {}", Hacspec::from(span));
            }
            if pat_ident.subpat.is_some() {
                bail!("pattern not allowed in Hacspec let bindings: {}", Hacspec::from(span));
            }
            let (ident, span) = translate_ident(pat_ident.ident);
            Ok(((Pattern::IdentPat(ident), span), None))
        }
        syn::Pat::Type(pat_type) => {
            let (pattern, typ_opt) = translate_pattern(pat_type.pat, pat_type.colon_token.spans[0])?;
            if type_opt.is_some() {
                bail!("pattern not allowed in Hacspec let bindings: {}", Hacspec::from(span));
            }
            let typ = translate_typ(pat_type.ty)?;
            Ok(pattern, Some(typ))
        }
        syn::Pat::Tuple(pat_tuple) => {
        }
        syn::Pat::TupleStruct(pat_tuple_struct) => {
        }
        syn::Pat::Wild(pat_wild) => {
        }
        _ => {
            bail!("pattern not allowed in Hacspec let bindings: {}", Hacspec::from(span));
        }
    }
}

fn translate_statement(stmt: &syn::Stmt) -> Result<Spanned<Statement>> {
    match stmt {
        syn::Stmt::Local(syn::Local{ pat, init, let_token, .. }) => {
            // let x: Type = a.parse();
            let (pat, ty) = translate_pattern(pat, &let_token.span)?;
        }
        syn::Stmt::Item(item) => bail!("block-local items are not allowed in Hacspec"),
        syn::Stmt::Expr(expr) => {
        }
        syn::Stmt::Semi(expr, _semi) => {
        }
    }
}

fn translate_block(block: &syn::Block) -> Result<Spanned<Block>> {
    let stmts = block
        .stmts
        .iter()
        .map()

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
            let sig_span = HacspecSpan::from(sig.ident.span());
            if sig.unsafety.is_some() {
                bail!("unsafe functions not allowed in Hacspec: {}", sig_span);
            }
            if sig.asyncness.is_some() {
                bail!("async functions not allowed in Hacspec: {}", sig_span);
            }
            if sig.constness.is_some() {
                bail!("const functions not allowed in Hacspec: {}", sig_span);
            }
            if sig.abi.is_some() {
                bail!("extern functions not allowed in Hacspec: {}", sig_span);
            }
            if sig.variadic.is_some() {
                bail!("variadic functions not allowed in Hacspec: {}", sig_span);
            }
            if !sig.generics.params.is_empty() {
                bail!("generics are not allowed in Hacspec: {}", sig_span);
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
                                    Err(anyhow!("pattern destructuring in function arguments not allowed in Hacspec"))
                                }
                            }
                        }
                        _ => {
                            Err(anyhow!("pattern destructuring in function arguments not allowed in Hacspec"))
                        }
                    }
                })
                .collect::<Result<Vec<(Spanned<Ident>, Spanned<Typ>)>>>()?;
            let fn_output = match sig.output {
                syn::ReturnType::Default => (BaseTyp::Unit, sig_span.into()),
                syn::ReturnType::Type(arrow, ty) => translate_base_typ(ty, arrow.spans[1])?,
            };
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
