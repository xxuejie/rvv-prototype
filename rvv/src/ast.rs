use core::cmp::{Eq, Ord, Ordering, PartialEq};
use core::hash::{Hash, Hasher};
use std::convert::TryFrom;
use std::fmt;

use anyhow::{anyhow, bail, Error};
use proc_macro2::Span as SynSpan;

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
    Path {
        path: syn::Path,
    },

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
        ty: Box<syn::Type>,
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
    Path {
        path: syn::Path,
    },

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
    Local {
        pat: Pattern,
        init: Option<Expression>,
    },

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
    pub inputs: Vec<(Pattern, syn::Type)>,
    pub output: syn::ReturnType,
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

impl TryFrom<&syn::Pat> for Pattern {
    type Error = Error;
    fn try_from(expr: &syn::Pat) -> Result<Pattern, Error> {
        unimplemented!()
    }
}

impl TryFrom<&syn::Expr> for Expression {
    type Error = Error;
    fn try_from(expr: &syn::Expr) -> Result<Expression, Error> {
        unimplemented!()
    }
}

impl TryFrom<&syn::Stmt> for Statement {
    type Error = Error;
    fn try_from(stmt: &syn::Stmt) -> Result<Statement, Error> {
        unimplemented!()
    }
}

impl TryFrom<&syn::Block> for Block {
    type Error = Error;
    fn try_from(block: &syn::Block) -> Result<Block, Error> {
        unimplemented!()
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
        unimplemented!()
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
