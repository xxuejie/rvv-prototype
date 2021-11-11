use core::cmp::{Eq, Ord, Ordering, PartialEq};
use core::hash::{Hash, Hasher};
use std::collections::HashMap;
use std::fmt;

use anyhow::{anyhow, bail, Error};
use proc_macro2::Span as Span2;
use syn::token;

#[derive(Debug, Clone, Copy)]
pub struct Span(pub Span2);

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

impl From<Span2> for Span {
    fn from(x: Span2) -> Span {
        Span(x)
    }
}
impl Into<Span2> for Span {
    fn into(self) -> Span2 {
        self.0
    }
}

impl Default for Span {
    fn default() -> Span {
        Span2::call_site().into()
    }
}

pub type WithSpan<T> = (T, Span);

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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct BareFnArg {
    pub span: Span,

    pub name: Option<(syn::Ident, Span)>,
    pub ty: WithSpan<Type>,
}

// pub enum ReturnType {
//     Default,
//     Type(RArrow, Box<Type>),
// }
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ReturnType {
    Default,
    Type(Span, Box<WithSpan<Type>>),
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Type {
    // pub struct TypeArray {
    //     pub bracket_token: Bracket,
    //     pub elem: Box<Type>,
    //     pub semi_token: Semi,
    //     pub len: Expr,
    // }
    // A fixed size array type: [T; n].
    Array {
        bracket_token: Span,
        elem: Box<Type>,
        semi_token: Span,
        len: TypedExpression,
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
        fn_token: Span,
        paren_token: Span,
        inputs: Vec<BareFnArg>,
        output: WithSpan<ReturnType>,
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
        and_token: Span,
        lifetime: Option<syn::Ident>,
        mutability: Option<Span>,
        elem: Box<WithSpan<Type>>,
    },

    // pub struct TypeSlice {
    //     pub bracket_token: Bracket,
    //     pub elem: Box<Type>,
    // }
    // A dynamically sized slice type: [T].
    Slice {
        bracket_token: Span,
        elem: Box<WithSpan<Type>>,
    },

    // pub struct TypeTuple {
    //     pub paren_token: Paren,
    //     pub elems: Punctuated<Type, Comma>,
    // }
    // A tuple type: (A, B, C, String).
    Tuple {
        paren_token: Span,
        elems: Vec<WithSpan<Type>>,
    },
}

impl Type {
    pub fn into_ref(
        self,
        and_token: Span,
        lifetime: Option<syn::Ident>,
        mutability: Option<Span>,
        span: Span,
    ) -> Type {
        Type::Reference {
            and_token,
            lifetime,
            mutability,
            elem: Box::new((self, span)),
        }
    }
    pub fn into_deref(self) -> Option<(Option<Span>, Box<WithSpan<Type>>)> {
        match self {
            Type::Reference {
                mutability, elem, ..
            } => Some((mutability, elem)),
            _ => None,
        }
    }
    pub fn is_ref(&self) -> bool {
        match self {
            Type::Reference { .. } => true,
            _ => false,
        }
    }

    pub fn type_ident(&self) -> Option<&syn::Ident> {
        match self {
            Type::Path(path) => path.get_ident(),
            Type::Reference { elem, .. } => elem.0.type_ident(),
            _ => None,
        }
    }
    pub fn type_name(&self) -> Option<String> {
        self.type_ident().map(|ident| ident.to_string())
    }

    pub fn unit() -> Type {
        Type::Tuple {
            paren_token: Span::default(),
            elems: Vec::new(),
        }
    }

    pub fn primitive(name: &'static str) -> Type {
        let mut segments = syn::punctuated::Punctuated::new();
        segments.push_value(syn::PathSegment {
            ident: syn::Ident::new(name, Span::default().into()),
            arguments: syn::PathArguments::None,
        });
        let path = syn::Path {
            leading_colon: None,
            segments,
        };
        Type::Path(path)
    }
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
        mutability: Option<Span>,
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
        pat: Box<WithSpan<Pattern>>,
        colon_token: Span,
        ty: Box<WithSpan<Type>>,
    },

    // pub struct PatRange {
    //     pub attrs: Vec<Attribute>,
    //     pub lo: Box<Expr>,
    //     pub limits: RangeLimits,
    //     pub hi: Box<Expr>,
    // }
    // A range pattern: 1..=2.
    Range {
        lo: Box<TypedExpression>,
        limits: syn::RangeLimits,
        hi: Box<TypedExpression>,
    },

    // pub struct PatReference {
    //     pub attrs: Vec<Attribute>,
    //     pub and_token: And,
    //     pub mutability: Option<Mut>,
    //     pub pat: Box<Pat>,
    // }
    // Reference {
    //     mutability: bool,
    //     pat: Box<Pattern>,
    // },

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
    Wild(Span),
}

// Type information can come from:
//    1. function arguments
//    2. local let binding
//    3. type cast
//    4. type infer
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TypedExpression {
    pub expr: WithSpan<Expression>,
    pub id: usize,
    pub ty: Option<Box<WithSpan<Type>>>,
}

impl TypedExpression {
    pub fn type_name(&self) -> Option<String> {
        self.ty.as_ref().and_then(|ty| ty.0.type_name())
    }
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
        left: Box<TypedExpression>,
        eq_token: Span,
        right: Box<TypedExpression>,
    },

    // pub struct ExprAssignOp {
    //     pub attrs: Vec<Attribute>,
    //     pub left: Box<Expr>,
    //     pub op: BinOp,
    //     pub right: Box<Expr>,
    // }
    // A compound assignment expression: counter += 1.
    AssignOp {
        left: Box<TypedExpression>,
        op: syn::BinOp,
        right: Box<TypedExpression>,
    },

    // pub struct ExprBinary {
    //     pub attrs: Vec<Attribute>,
    //     pub left: Box<Expr>,
    //     pub op: BinOp,
    //     pub right: Box<Expr>,
    // }
    // A binary operation: a + b, a * b.
    Binary {
        left: Box<TypedExpression>,
        op: syn::BinOp,
        right: Box<TypedExpression>,
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
        func: Box<TypedExpression>,
        paren_token: Span,
        args: Vec<TypedExpression>,
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
        receiver: Box<TypedExpression>,
        dot_token: Span,
        method: syn::Ident,
        paren_token: Span,
        args: Vec<TypedExpression>,
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
        expr: Box<TypedExpression>,
    },

    // pub struct ExprField {
    //     pub attrs: Vec<Attribute>,
    //     pub base: Box<Expr>,
    //     pub dot_token: Dot,
    //     pub member: Member,
    // }
    // Access of a named struct field (obj.k) or unnamed tuple struct field (obj.0).
    Field {
        base: Box<TypedExpression>,
        dot_token: Span,
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
        expr: Box<TypedExpression>,
        as_token: Span,
        ty: Box<WithSpan<Type>>,
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
        bracket_token: Span,
        expr: Box<TypedExpression>,
        semi_token: Span,
        len: Box<TypedExpression>,
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
    Paren {
        paren_token: Span,
        expr: Box<TypedExpression>,
    },

    // pub struct ExprReference {
    //     pub attrs: Vec<Attribute>,
    //     pub and_token: And,
    //     pub raw: Reserved,
    //     pub mutability: Option<Mut>,
    //     pub expr: Box<Expr>,
    // }
    // A referencing operation: &a or &mut a.
    Reference {
        and_token: Span,
        mutability: Option<Span>,
        expr: Box<TypedExpression>,
    },

    // pub struct ExprIndex {
    //     pub attrs: Vec<Attribute>,
    //     pub expr: Box<Expr>,
    //     pub bracket_token: Bracket,
    //     pub index: Box<Expr>,
    // }
    // A square bracketed indexing expression: vector[2].
    Index {
        expr: Box<TypedExpression>,
        bracket_token: Span,
        index: Box<TypedExpression>,
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
    Break(Span),

    // pub struct ExprContinue {
    //     pub attrs: Vec<Attribute>,
    //     pub continue_token: Continue,
    //     pub label: Option<Lifetime>,
    // }
    // A continue.
    Continue(Span),

    // pub struct ExprReturn {
    //     pub attrs: Vec<Attribute>,
    //     pub return_token: Return,
    //     pub expr: Option<Box<Expr>>,
    // }
    // A return.
    Return {
        return_token: Span,
        expr: Option<Box<TypedExpression>>,
    },

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
        if_token: Span,
        cond: Box<TypedExpression>,
        then_branch: Block,
        else_branch: Option<(Span, Box<TypedExpression>)>,
    },

    // pub struct ExprRange {
    //     pub attrs: Vec<Attribute>,
    //     pub from: Option<Box<Expr>>,
    //     pub limits: RangeLimits,
    //     pub to: Option<Box<Expr>>,
    // }
    // A range expression: 1..2, 1.., ..2, 1..=2, ..=2.
    Range {
        from: Option<Box<TypedExpression>>,
        limits: syn::RangeLimits,
        to: Option<Box<TypedExpression>>,
    },

    // pub struct ExprLoop {
    //     pub attrs: Vec<Attribute>,
    //     pub label: Option<Label>,
    //     pub loop_token: Loop,
    //     pub body: Block,
    // }
    Loop {
        loop_token: Span,
        body: Block,
    },

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
        for_token: Span,
        pat: WithSpan<Pattern>,
        in_token: Span,
        expr: Box<TypedExpression>,
        body: Block,
    },
}

impl Expression {
    pub fn get_literal(&self) -> Option<&syn::Lit> {
        match self {
            Expression::Lit(lit) => Some(lit),
            _ => None,
        }
    }

    pub fn var_ident(&self) -> Option<&syn::Ident> {
        match self {
            Expression::Path(path) => path.get_ident(),
            _ => None,
        }
    }
    pub fn var_name(&self) -> Option<String> {
        self.var_ident().map(|ident| ident.to_string())
    }
}

// pub enum Stmt {
//     Local(Local),
//     Item(Item),
//     Expr(Expr),
//     Semi(Expr, Semi),
// }
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Statement {
    // pub struct Local {
    //     pub attrs: Vec<Attribute>,
    //     pub let_token: Let,
    //     pub pat: Pat,
    //     pub init: Option<(Eq, Box<Expr>)>,
    //     pub semi_token: Semi,
    // }
    // A local (let) binding.
    Local {
        let_token: Span,
        pat: WithSpan<Pattern>,
        eq_token: Span,
        init: TypedExpression,
        semi_token: Span,
    },

    // Expr without trailing semicolon. (as return value)
    Expr(TypedExpression),
    // Expression with trailing semicolon.
    Semi(TypedExpression),
}

// pub struct Block {
//     pub brace_token: Brace,
//     pub stmts: Vec<Stmt>,
// }
// A braced block containing Rust statements.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Block {
    pub span: Span,

    pub brace_token: Span,
    pub stmts: Vec<WithSpan<Statement>>,
}

impl Block {
    pub fn get_type(&self) -> Option<Box<WithSpan<Type>>> {
        if let Some((stmt, _span)) = self.stmts.last() {
            if let Statement::Expr(expr) = stmt {
                return expr.ty.clone();
            }
        }
        Some(Box::new((Type::unit(), Span::default())))
    }
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FnArg {
    pub span: Span,

    pub mutability: Option<Span>,
    pub name: syn::Ident,
    pub colon_token: Span,
    pub ty: Box<WithSpan<Type>>,
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Signature {
    pub span: Span,

    pub fn_token: Span,
    pub paren_token: Span,
    pub ident: syn::Ident,
    pub inputs: Vec<FnArg>,
    pub output: WithSpan<ReturnType>,
}

// pub struct ItemFn {
//     pub attrs: Vec<Attribute>,
//     pub vis: Visibility,
//     pub sig: Signature,
//     pub block: Box<Block>,
// }
// A free-standing function: fn process(n: usize) -> Result<()> { ... }.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ItemFn {
    pub span: Span,

    pub vis: syn::Visibility,
    pub sig: Signature,
    pub block: Block,
}
