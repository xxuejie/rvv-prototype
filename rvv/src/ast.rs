use core::cmp::{Eq, Ord, Ordering, PartialEq};
use core::hash::{Hash, Hasher};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

use anyhow::{anyhow, bail, Error};
use proc_macro2::{Span as SynSpan, TokenStream};
use quote::ToTokens;
use syn::token;

pub struct Span(pub SynSpan);

impl Ord for Span {
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(
            &(self.0.start(), self.0.end()),
            &(other.0.start(), other.0.end()),
        )
    }
}
impl PartialOrd for Span {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for Span {
    fn eq(&self, other: &Self) -> bool {
        (self.0.start(), self.0.end()).eq(&(other.0.start(), other.0.end()))
    }
}
impl Eq for Span {}

impl Hash for Span {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (
            self.0.start().line,
            self.0.start().column,
            self.0.end().line,
            self.0.end().column,
        )
            .hash(state)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}-{}:{}",
            self.0.start().column,
            self.0.start().line,
            self.0.end().column,
            self.0.end().line,
        )
    }
}

impl From<SynSpan> for Span {
    fn from(x: SynSpan) -> Span {
        Span(x)
    }
}

pub type Spanned<T> = (T, Span);

// pub struct Lifetime {
//     pub apostrophe: Span,
//     pub ident: Ident,
// }

// pub struct BareFnArg {
//     pub attrs: Vec<Attribute>,
//     pub name: Option<(Ident, Colon)>,
//     pub ty: Type,
// }
// An argument in a function type: the usize in fn(usize) -> bool.
pub struct BareFnArg {
    name: Option<syn::Ident>,
    ty: Type,
}

// pub enum ReturnType {
//     Default,
//     Type(RArrow, Box<Type>),
// }
pub enum ReturnType {
    Default,
    Type(Box<Type>),
}

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
pub enum Type {
    // pub struct TypeArray {
    //     pub bracket_token: Bracket,
    //     pub elem: Box<Type>,
    //     pub semi_token: Semi,
    //     pub len: Expr,
    // }
    // A fixed size array type: [T; n].
    Array {
        elem: Box<Type>,
        len: Expression,
    },

    // pub struct TypeBareFn {
    //     pub lifetimes: Option<BoundLifetimes>,
    //     pub unsafety: Option<Unsafe>,
    //     pub abi: Option<Abi>,
    //     pub fn_token: Fn,
    //     pub paren_token: Paren,
    //     pub inputs: Punctuated<BareFnArg, Comma>,
    //     pub variadic: Option<Variadic>,
    //     pub output: ReturnType,
    // }
    // A bare function type: fn(usize) -> bool.
    BareFn {
        inputs: Vec<BareFnArg>,
        output: ReturnType,
    },

    // pub struct TypePath {
    //     pub qself: Option<QSelf>,
    //     pub path: Path,
    // }
    // A path like std::slice::Iter, optionally qualified with a self-type as in <Vec<T> as SomeTrait>::Associated.
    Path(syn::Path),

    // pub struct TypeReference {
    //     pub and_token: And,
    //     pub lifetime: Option<Lifetime>,
    //     pub mutability: Option<Mut>,
    //     pub elem: Box<Type>,
    // }
    // A reference type: &'a T or &'a mut T.
    Reference {
        lifetime: Option<syn::Ident>,
        mutability: bool,
        elem: Box<Type>,
    },

    // pub struct TypeSlice {
    //     pub bracket_token: Bracket,
    //     pub elem: Box<Type>,
    // }
    // A dynamically sized slice type: [T].
    Slice(Box<Type>),

    // pub struct TypeTuple {
    //     pub paren_token: Paren,
    //     pub elems: Punctuated<Type, Comma>,
    // }
    // A tuple type: (A, B, C, String).
    Tuple(Vec<Type>),
}

// pub enum Pat {
//     Box(PatBox),
//     Ident(PatIdent),
//     Lit(PatLit),
//     Macro(PatMacro),
//     Or(PatOr),
//     Path(PatPath),
//     Range(PatRange),
//     Reference(PatReference),
//     Rest(PatRest),
//     Slice(PatSlice),
//     Struct(PatStruct),
//     Tuple(PatTuple),
//     TupleStruct(PatTupleStruct),
//     Type(PatType),
//     Verbatim(TokenStream),
//     Wild(PatWild),
//     // some variants omitted
// }
pub enum Pattern {
    // pub struct PatIdent {
    //     pub attrs: Vec<Attribute>,
    //     pub by_ref: Option<Ref>,
    //     pub mutability: Option<Mut>,
    //     pub ident: Ident,
    //     pub subpat: Option<(At, Box<Pat>)>,
    // }
    // A pattern that binds a new variable: mut binding.
    Ident {
        mutability: bool,
        ident: syn::Ident,
    },

    // pub struct PatType {
    //     pub attrs: Vec<Attribute>,
    //     pub pat: Box<Pat>,
    //     pub colon_token: Colon,
    //     pub ty: Box<Type>,
    // }
    // A type ascription pattern: foo: f64.
    Type {
        pat: Box<Pattern>,
        ty: Box<Type>,
    },

    // pub struct PatRange {
    //     pub attrs: Vec<Attribute>,
    //     pub lo: Box<Expr>,
    //     pub limits: RangeLimits,
    //     pub hi: Box<Expr>,
    // }
    // A range pattern: 1..=2.
    Range {
        lo: Box<Expression>,
        limits: syn::RangeLimits,
        hi: Box<Expression>,
    },

    // pub struct PatPath {
    //     pub attrs: Vec<Attribute>,
    //     pub qself: Option<QSelf>,
    //     pub path: Path,
    // }
    // A path pattern like Color::Red
    Path(syn::Path),

    // pub struct PatWild {
    //     pub attrs: Vec<Attribute>,
    //     pub underscore_token: Underscore,
    // }
    // A pattern that matches any value: _.
    Wild,
}

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
pub enum Expression {
    // pub struct ExprArray {
    //     pub attrs: Vec<Attribute>,
    //     pub bracket_token: Bracket,
    //     pub elems: Punctuated<Expr, Comma>,
    // }
    // A slice literal expression: [a, b, c, d].
    Array(syn::ExprArray),

    // pub struct ExprAssign {
    //     pub attrs: Vec<Attribute>,
    //     pub left: Box<Expr>,
    //     pub eq_token: Eq,
    //     pub right: Box<Expr>,
    // }
    // An assignment expression: a = compute().
    Assign {
        left: Box<Expression>,
        right: Box<Expression>,
    },

    // pub struct ExprAssignOp {
    //     pub attrs: Vec<Attribute>,
    //     pub left: Box<Expr>,
    //     pub op: BinOp,
    //     pub right: Box<Expr>,
    // }
    // A compound assignment expression: counter += 1.
    AssignOp {
        left: Box<Expression>,
        op: syn::BinOp,
        right: Box<Expression>,
    },

    // pub struct ExprBinary {
    //     pub attrs: Vec<Attribute>,
    //     pub left: Box<Expr>,
    //     pub op: BinOp,
    //     pub right: Box<Expr>,
    // }
    // A binary operation: a + b, a * b.
    Binary {
        left: Box<Expression>,
        op: syn::BinOp,
        right: Box<Expression>,
    },

    // pub struct ExprType {
    //     pub attrs: Vec<Attribute>,
    //     pub expr: Box<Expr>,
    //     pub colon_token: Colon,
    //     pub ty: Box<Type>,
    // }
    // TODO: A type ascription expression: foo: f64.
    // Type {
    //     expr: Box<Expression>,
    //     ty: Box<syn::Type>,
    // },

    // pub struct ExprCall {
    //     pub attrs: Vec<Attribute>,
    //     pub func: Box<Expr>,
    //     pub paren_token: Paren,
    //     pub args: Punctuated<Expr, Comma>,
    // }
    // A function call expression: invoke(a, b).
    Call {
        func: Box<Expression>,
        args: Vec<Expression>,
    },

    // pub struct ExprMethodCall {
    //     pub attrs: Vec<Attribute>,
    //     pub receiver: Box<Expr>,
    //     pub dot_token: Dot,
    //     pub method: Ident,
    //     pub turbofish: Option<MethodTurbofish>,
    //     pub paren_token: Paren,
    //     pub args: Punctuated<Expr, Comma>,
    // }
    // A method call expression: x.foo::<T>(a, b).
    MethodCall {
        receiver: Box<Expression>,
        method: syn::Ident,
        args: Vec<Expression>,
    },

    // pub struct ExprMacro {
    //     pub attrs: Vec<Attribute>,
    //     pub mac: Macro,
    // }
    // A macro invocation expression: format!("{}", q).
    Macro(syn::Macro),

    // pub struct ExprUnary {
    //     pub attrs: Vec<Attribute>,
    //     pub op: UnOp,
    //     pub expr: Box<Expr>,
    // }
    // A unary operation: !x, *x.
    Unary {
        op: syn::UnOp,
        expr: Box<Expression>,
    },

    // pub struct ExprField {
    //     pub attrs: Vec<Attribute>,
    //     pub base: Box<Expr>,
    //     pub dot_token: Dot,
    //     pub member: Member,
    // }
    // Access of a named struct field (obj.k) or unnamed tuple struct field (obj.0).
    Field {
        base: Box<Expression>,
        member: syn::Member,
    },

    // pub struct ExprCast {
    //     pub attrs: Vec<Attribute>,
    //     pub expr: Box<Expr>,
    //     pub as_token: As,
    //     pub ty: Box<Type>,
    // }
    // A cast expression: foo as f64.
    Cast {
        expr: Box<Expression>,
        ty: Box<Type>,
    },

    // pub struct ExprRepeat {
    //     pub attrs: Vec<Attribute>,
    //     pub bracket_token: Bracket,
    //     pub expr: Box<Expr>,
    //     pub semi_token: Semi,
    //     pub len: Box<Expr>,
    // }
    // An array literal constructed from one repeated element: [0u8; N].
    Repeat {
        expr: Box<Expression>,
        len: Box<Expression>,
    },

    // pub struct ExprLit {
    //     pub attrs: Vec<Attribute>,
    //     pub lit: Lit,
    // }
    // A literal in place of an expression: 1, "foo".
    Lit(syn::Lit),

    // pub struct ExprParen {
    //     pub attrs: Vec<Attribute>,
    //     pub paren_token: Paren,
    //     pub expr: Box<Expr>,
    // }
    // A parenthesized expression: (a + b).
    Paren(Box<Expression>),

    // pub struct ExprReference {
    //     pub attrs: Vec<Attribute>,
    //     pub and_token: And,
    //     pub raw: Reserved,
    //     pub mutability: Option<Mut>,
    //     pub expr: Box<Expr>,
    // }
    // A referencing operation: &a or &mut a.
    Reference {
        mutability: bool,
        expr: Box<Expression>,
    },

    // pub struct ExprIndex {
    //     pub attrs: Vec<Attribute>,
    //     pub expr: Box<Expr>,
    //     pub bracket_token: Bracket,
    //     pub index: Box<Expr>,
    // }
    // A square bracketed indexing expression: vector[2].
    Index {
        expr: Box<Expression>,
        index: Box<Expression>,
    },

    // pub struct ExprPath {
    //     pub attrs: Vec<Attribute>,
    //     pub qself: Option<QSelf>,
    //     pub path: Path,
    // }
    // A path like std::mem::replace possibly containing generic parameters and a qualified self-type.
    Path(syn::Path),

    // ==== control flow ====
    // pub struct ExprBreak {
    //     pub attrs: Vec<Attribute>,
    //     pub break_token: Break,
    //     pub label: Option<Lifetime>,
    //     pub expr: Option<Box<Expr>>,
    // }
    // A break.
    Break,

    // pub struct ExprContinue {
    //     pub attrs: Vec<Attribute>,
    //     pub continue_token: Continue,
    //     pub label: Option<Lifetime>,
    // }
    // A continue.
    Continue,

    // pub struct ExprReturn {
    //     pub attrs: Vec<Attribute>,
    //     pub return_token: Return,
    //     pub expr: Option<Box<Expr>>,
    // }
    // A return.
    Return(Option<Box<Expression>>),

    // pub struct ExprBlock {
    //     pub attrs: Vec<Attribute>,
    //     pub label: Option<Label>,
    //     pub block: Block,
    // }
    // A blocked scope: { ... }.
    Block(Block),

    // pub struct ExprIf {
    //     pub attrs: Vec<Attribute>,
    //     pub if_token: If,
    //     pub cond: Box<Expr>,
    //     pub then_branch: Block,
    //     pub else_branch: Option<(Else, Box<Expr>)>,
    // }
    // An if expression with an optional else block: if expr { ... } else { ... }.
    If {
        cond: Box<Expression>,
        then_branch: Block,
        else_branch: Option<Box<Expression>>,
    },

    // pub struct ExprLoop {
    //     pub attrs: Vec<Attribute>,
    //     pub label: Option<Label>,
    //     pub loop_token: Loop,
    //     pub body: Block,
    // }
    Loop(Block),

    // pub struct ExprForLoop {
    //     pub attrs: Vec<Attribute>,
    //     pub label: Option<Label>,
    //     pub for_token: For,
    //     pub pat: Pat,
    //     pub in_token: In,
    //     pub expr: Box<Expr>,
    //     pub body: Block,
    // }
    // for pat in expr { ... }
    ForLoop {
        pat: Pattern,
        expr: Box<Expression>,
        body: Block,
    },
}

// pub enum Stmt {
//     Local(Local),
//     Item(Item),
//     Expr(Expr),
//     Semi(Expr, Semi),
// }
pub enum Statement {
    // pub struct Local {
    //     pub attrs: Vec<Attribute>,
    //     pub let_token: Let,
    //     pub pat: Pat,
    //     pub init: Option<(Eq, Box<Expr>)>,
    //     pub semi_token: Semi,
    // }
    // A local (let) binding.
    Local { pat: Pattern, init: Expression },

    // Expr without trailing semicolon. (as return value)
    Expr(Expression),
    // Expression with trailing semicolon.
    Semi(Expression),
}

// pub struct Block {
//     pub brace_token: Brace,
//     pub stmts: Vec<Stmt>,
// }
// A braced block containing Rust statements.
pub struct Block {
    pub stmts: Vec<Statement>,
}

// pub struct PatType {
//     pub attrs: Vec<Attribute>,
//     pub pat: Box<Pat>,
//     pub colon_token: Colon,
//     pub ty: Box<Type>,
// }
// pub enum FnArg {
//     Receiver(Receiver),
//     Typed(PatType),
// }
pub struct FnArg {
    pat: Box<Pattern>,
    ty: Box<Type>,
}

// pub struct Signature {
//     pub constness: Option<Const>,
//     pub asyncness: Option<Async>,
//     pub unsafety: Option<Unsafe>,
//     pub abi: Option<Abi>,
//     pub fn_token: Fn,
//     pub ident: Ident,
//     pub generics: Generics,
//     pub paren_token: Paren,
//     pub inputs: Punctuated<FnArg, Comma>,
//     pub variadic: Option<Variadic>,
//     pub output: ReturnType,
// }
// A function signature in a implementation: fn initialize(a: T).
pub struct Signature {
    pub ident: syn::Ident,
    pub inputs: Vec<FnArg>,
    pub output: ReturnType,
}

// pub struct ItemFn {
//     pub attrs: Vec<Attribute>,
//     pub vis: Visibility,
//     pub sig: Signature,
//     pub block: Box<Block>,
// }
// A free-standing function: fn process(n: usize) -> Result<()> { ... }.
pub struct ItemFn {
    pub vis: syn::Visibility,
    pub sig: Signature,
    pub block: Block,
}

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
                let len = Expression::try_from(len)?;
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
                let lo = Box::new(Expression::try_from(&**lo)?);
                let hi = Box::new(Expression::try_from(&**hi)?);
                let limits = (*limits).clone();
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
                let left = Box::new(Expression::try_from(&**left)?);
                let right = Box::new(Expression::try_from(&**right)?);
                Ok(Expression::Assign { left, right})
            },
            syn::Expr::AssignOp(syn::ExprAssignOp { left, op, right, ..}) => {
                let left = Box::new(Expression::try_from(&**left)?);
                let right = Box::new(Expression::try_from(&**right)?);
                let op = (*op).clone();
                Ok(Expression::AssignOp { left, op, right})
            },
            syn::Expr::Async(_) => {
                Err(anyhow!("async block is not supported in rvv_vector"))
            },
            syn::Expr::Await(_) => {
                Err(anyhow!("await expression is not supported in rvv_vector"))
            },
            syn::Expr::Binary(syn::ExprBinary { left, op, right, ..}) => {
                let left = Box::new(Expression::try_from(&**left)?);
                let right = Box::new(Expression::try_from(&**right)?);
                let op = (*op).clone();
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
                let func = Box::new(Expression::try_from(&**func)?);
                let args = args.iter()
                    .map(Expression::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Expression::Call { func, args })
            },
            syn::Expr::Cast(syn::ExprCast { expr, ty, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?);
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
                let base = Box::new(Expression::try_from(&**base)?);
                let member = (*member).clone();
                Ok(Expression::Field { base, member })
            },
            syn::Expr::ForLoop(syn::ExprForLoop { label, pat, expr, body, .. }) => {
                if label.is_some() {
                    bail!("label in for loop is not supported in rvv_vector");
                }
                let pat = Pattern::try_from(pat)?;
                let expr = Box::new(Expression::try_from(&**expr)?);
                let body = Block::try_from(body)?;
                Ok(Expression::ForLoop { pat, expr, body })
            },
            syn::Expr::Group(_) => {
                Err(anyhow!("expression contained within invisible delimiters is not supported in rvv_vector"))
            },
            syn::Expr::If(syn::ExprIf { cond, then_branch, else_branch, ..}) => {
                let cond = Box::new(Expression::try_from(&**cond)?);
                let then_branch = Block::try_from(then_branch)?;
                let else_branch = else_branch
                    .as_ref()
                    .map::<Result<_, Error>, _>(|(_, expr)| Ok(Box::new(Expression::try_from(&**expr)?)))
                    .transpose()?;
                Ok(Expression::If { cond, then_branch, else_branch })
            },
            syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?);
                let index = Box::new(Expression::try_from(&**index)?);
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
                let receiver = Box::new(Expression::try_from(&**receiver)?);
                let method = (*method).clone();
                let args = args.iter()
                    .map(Expression::try_from)
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Expression::MethodCall { receiver, method, args })
            },
            syn::Expr::Paren(syn::ExprParen { expr, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?);
                Ok(Expression::Paren(expr))
            },
            syn::Expr::Path(syn::ExprPath{ qself, path, .. }) => {
                if qself.is_some() {
                    bail!("explicit Self type in a qualified path is not supported in rvv_vector");
                }
                Ok(Expression::Path((*path).clone()))
            },
            syn::Expr::Range(_) => {
                Err(anyhow!("range expression is not supported in rvv_vector"))
            },
            syn::Expr::Reference(syn::ExprReference{ mutability, expr, .. }) => {
                let mutability = mutability.is_some();
                let expr = Box::new(Expression::try_from(&**expr)?);
                Ok(Expression::Reference { mutability, expr })
            },
            syn::Expr::Repeat(syn::ExprRepeat { expr, len, .. }) => {
                let expr = Box::new(Expression::try_from(&**expr)?);
                let len = Box::new(Expression::try_from(&**len)?);
                Ok(Expression::Repeat { expr, len })
            },
            syn::Expr::Return(syn::ExprReturn { expr, .. }) => {
                let expr_opt = expr
                    .as_ref()
                    .map::<Result<_, Error>, _>(|expr| Ok(Box::new(Expression::try_from(&**expr)?)))
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
                let op = (*op).clone();
                let expr = Box::new(Expression::try_from(&**expr)?);
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
                let init = init
                    .as_ref()
                    .map(|(_, expr)| Expression::try_from(&**expr))
                    .transpose()?
                    .unwrap();
                Ok(Statement::Local { pat, init })
            }
            syn::Stmt::Item(_) => Err(anyhow!("item definition is not supported in rvv_vector")),
            syn::Stmt::Expr(expr) => Ok(Statement::Expr(Expression::try_from(expr)?)),
            syn::Stmt::Semi(expr, _) => Ok(Statement::Semi(Expression::try_from(expr)?)),
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
            syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => Ok(FnArg {
                pat: Box::new(Pattern::try_from(&**pat)?),
                ty: Box::new(Type::try_from(&**ty)?),
            }),
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

// =============================
// ==== impl ToTokens for T ====
// =============================

#[derive(Default)]
pub struct Registers {
    pub category: &'static str,
    pub max_number: u8,
    pub last_number: u8,
    // ident_name => (register_number, is_function_argument)
    pub mapping: HashMap<String, (u8, bool)>,
}

impl Registers {
    pub fn new(category: &'static str, max_number: u8) -> Registers {
        Registers {
            category,
            max_number,
            last_number: 0,
            mapping: HashMap::default(),
        }
    }

    pub fn next_register(&mut self) -> Option<u8> {
        if self.last_number < self.max_number {
            self.last_number += 1;
            let tmp_var_name = format!("__tmp_{}_var{}", self.category, self.last_number);
            self.mapping.insert(tmp_var_name, (self.last_number, false));
            return Some(self.last_number);
        }
        None
    }

    pub fn search_reg(&self, reg: u8) -> Option<(String, bool)> {
        for (name, (number, is_fn_arg)) in &self.mapping {
            if *number == reg {
                return Some((name.clone(), *is_fn_arg));
            }
        }
        None
    }

    pub fn get_reg(&self, var_name: &str) -> Result<(u8, bool), String> {
        self.mapping
            .get(var_name)
            .cloned()
            .ok_or_else(|| format!("Unrecognized {} variable name: {}", self.category, var_name))
    }

    pub fn insert(&mut self, var_name: String, value: (u8, bool)) {
        self.mapping.insert(var_name, value);
    }
}

pub struct Context {
    // vector registers
    v_registers: Registers,
    // general registers
    x_registers: Registers,
}

pub trait ToTokenStream {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context);
    fn to_token_stream(&self, context: &mut Context) -> TokenStream {
        let mut tokens = TokenStream::new();
        self.to_tokens(&mut tokens, context);
        tokens
    }
    fn into_token_stream(self, context: &mut Context) -> TokenStream
    where
        Self: Sized,
    {
        self.to_token_stream(context)
    }
}

impl ToTokenStream for ReturnType {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            ReturnType::Default => {}
            ReturnType::Type(ty) => {
                token::RArrow::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
        }
    }
}
impl ToTokenStream for BareFnArg {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        if let Some(ident) = self.name.as_ref() {
            ident.to_tokens(tokens);
            token::Colon::default().to_tokens(tokens);
        }
        self.ty.to_tokens(tokens, context);
    }
}
impl ToTokenStream for Type {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Type::Array { elem, len } => {
                token::Bracket::default().surround(tokens, |inner| {
                    elem.to_tokens(inner, context);
                    token::Semi::default().to_tokens(inner);
                    len.to_tokens(inner, context);
                });
            }
            Type::BareFn { inputs, output } => {
                token::Fn::default().to_tokens(tokens);
                token::Paren::default().surround(tokens, |inner| {
                    for input in inputs {
                        input.to_tokens(inner, context);
                    }
                });
                output.to_tokens(tokens, context);
            }
            Type::Path(path) => {
                path.to_tokens(tokens);
            }
            Type::Reference {
                lifetime,
                mutability,
                elem,
            } => {
                token::And::default().to_tokens(tokens);
                if let Some(lifetime) = lifetime {
                    lifetime.to_tokens(tokens);
                }
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                elem.to_tokens(tokens, context);
            }
            Type::Slice(ty) => {
                token::Bracket::default().surround(tokens, |inner| {
                    ty.to_tokens(inner, context);
                });
            }
            Type::Tuple(types) => token::Paren::default().surround(tokens, |inner| {
                for (idx, ty) in types.iter().enumerate() {
                    ty.to_tokens(inner, context);
                    if idx != types.len() - 1 {
                        token::Comma::default().to_tokens(inner);
                    }
                }
            }),
        }
    }
}
impl ToTokenStream for Pattern {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Pattern::Ident { mutability, ident } => {
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                ident.to_tokens(tokens);
            }
            Pattern::Type { pat, ty } => {
                pat.to_tokens(tokens, context);
                token::Colon::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
            Pattern::Range { lo, limits, hi } => {
                lo.to_tokens(tokens, context);
                match limits {
                    syn::RangeLimits::HalfOpen(inner) => {
                        inner.to_tokens(tokens);
                    }
                    syn::RangeLimits::Closed(inner) => {
                        inner.to_tokens(tokens);
                    }
                }
                hi.to_tokens(tokens, context);
            }
            Pattern::Path(path) => {
                path.to_tokens(tokens);
            }
            Pattern::Wild => {
                token::Underscore::default().to_tokens(tokens);
            }
        }
    }
}
impl ToTokenStream for Expression {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Expression::Array(arr) => {
                arr.to_tokens(tokens);
            }
            Expression::Assign { left, right } => {
                left.to_tokens(tokens, context);
                token::Eq::default().to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::AssignOp { left, op, right } => {
                // FIXME: use rvv assembler
                left.to_tokens(tokens, context);
                op.to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::Binary { left, op, right } => {
                // FIXME: use rvv assembler
                left.to_tokens(tokens, context);
                op.to_tokens(tokens);
                right.to_tokens(tokens, context);
            }
            Expression::Call { func, args } => {
                func.to_tokens(tokens, context);
                token::Paren::default().surround(tokens, |inner| {
                    for (idx, ty) in args.iter().enumerate() {
                        ty.to_tokens(inner, context);
                        if idx != args.len() - 1 {
                            token::Comma::default().to_tokens(inner);
                        }
                    }
                });
            }
            Expression::MethodCall {
                receiver,
                method,
                args,
            } => {
                // FIXME: use rvv assembler
                receiver.to_tokens(tokens, context);
                token::Dot::default().to_tokens(tokens);
                method.to_tokens(tokens);
                token::Paren::default().surround(tokens, |inner| {
                    for (idx, ty) in args.iter().enumerate() {
                        ty.to_tokens(inner, context);
                        if idx != args.len() - 1 {
                            token::Comma::default().to_tokens(inner);
                        }
                    }
                });
            }
            Expression::Macro(mac) => {
                mac.to_tokens(tokens);
            }
            Expression::Unary { op, expr } => {
                op.to_tokens(tokens);
                expr.to_tokens(tokens, context);
            }
            Expression::Field { base, member } => {
                base.to_tokens(tokens, context);
                token::Dot::default().to_tokens(tokens);
                member.to_tokens(tokens);
            }
            Expression::Cast { expr, ty } => {
                expr.to_tokens(tokens, context);
                token::As::default().to_tokens(tokens);
                ty.to_tokens(tokens, context);
            }
            Expression::Repeat { expr, len } => {
                token::Bracket::default().surround(tokens, |inner| {
                    expr.to_tokens(inner, context);
                    token::Semi::default().to_tokens(inner);
                    len.to_tokens(inner, context);
                });
            }
            Expression::Lit(lit) => {
                lit.to_tokens(tokens);
            }
            Expression::Paren(expr) => {
                token::Paren::default().surround(tokens, |inner| {
                    expr.to_tokens(inner, context);
                });
            }
            Expression::Reference { mutability, expr } => {
                token::And::default().to_tokens(tokens);
                if *mutability {
                    token::Mut::default().to_tokens(tokens);
                }
                expr.to_tokens(tokens, context);
            }
            Expression::Index { expr, index } => {
                expr.to_tokens(tokens, context);
                token::Bracket::default().surround(tokens, |inner| {
                    index.to_tokens(inner, context);
                });
            }
            Expression::Path(path) => {
                path.to_tokens(tokens);
            }
            Expression::Break => {
                token::Break::default().to_tokens(tokens);
            }
            Expression::Continue => {
                token::Continue::default().to_tokens(tokens);
            }
            Expression::Return(expr_opt) => {
                token::Return::default().to_tokens(tokens);
                if let Some(expr) = expr_opt.as_ref() {
                    expr.to_tokens(tokens, context);
                }
            }
            Expression::Block(block) => {
                block.to_tokens(tokens, context);
            }
            Expression::If {
                cond,
                then_branch,
                else_branch,
            } => {
                token::If::default().to_tokens(tokens);
                cond.to_tokens(tokens, context);
                then_branch.to_tokens(tokens, context);
                if let Some(expr) = else_branch.as_ref() {
                    token::Else::default().to_tokens(tokens);
                    expr.to_tokens(tokens, context);
                }
            }
            Expression::Loop(body) => {
                token::Loop::default().to_tokens(tokens);
                body.to_tokens(tokens, context);
            }
            Expression::ForLoop { pat, expr, body } => {
                token::For::default().to_tokens(tokens);
                pat.to_tokens(tokens, context);
                token::In::default().to_tokens(tokens);
                expr.to_tokens(tokens, context);
                body.to_tokens(tokens, context);
            }
        }
    }
}
impl ToTokenStream for Statement {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        match self {
            Statement::Local { pat, init } => {
                token::Let::default().to_tokens(tokens);
                pat.to_tokens(tokens, context);
                token::Eq::default().to_tokens(tokens);
                init.to_tokens(tokens, context);
                token::Semi::default().to_tokens(tokens);
            }
            Statement::Expr(expr) => {
                expr.to_tokens(tokens, context);
            }
            Statement::Semi(expr) => {
                expr.to_tokens(tokens, context);
                token::Semi::default().to_tokens(tokens);
            }
        }
    }
}
impl ToTokenStream for Block {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        token::Brace::default().surround(tokens, |inner| {
            for stmt in &self.stmts {
                stmt.to_tokens(inner, context);
            }
        })
    }
}
impl ToTokenStream for FnArg {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        self.pat.to_tokens(tokens, context);
        token::Colon::default().to_tokens(tokens);
        self.ty.to_tokens(tokens, context);
    }
}
impl ToTokenStream for Signature {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        token::Fn::default().to_tokens(tokens);
        self.ident.to_tokens(tokens);
        token::Paren::default().surround(tokens, |inner| {
            for (idx, input) in self.inputs.iter().enumerate() {
                input.to_tokens(inner, context);
                if idx != self.inputs.len() - 1 {
                    token::Comma::default().to_tokens(inner);
                }
            }
        });
        self.output.to_tokens(tokens, context);
    }
}
impl ToTokenStream for ItemFn {
    fn to_tokens(&self, tokens: &mut TokenStream, context: &mut Context) {
        self.vis.to_tokens(tokens);
        self.sig.to_tokens(tokens, context);
        self.block.to_tokens(tokens, context);
    }
}
