//! A Grammer for Lox expressions
//!
//! Legend:
//! CAPITALIZE -- terminal symbol; literal.
//! x -> a ;   -- definition of x (non-terminal)
//!
//! ## Expressions:
//!
//! expression  -> equality ;
//! equality    -> comparison ( ("!=" | "==") comparison )* ;
//! comparison  -> term ( (">" | ">=" | "<" | "<=") term )* ;
//! term        -> factor ( ("-" | "+") factor )* ;
//! factor      -> unary ( ("/" | "*") unary )* ;
//! unary       -> ( "-" | "!" ) unary | primary ;
//! primary     -> literal | "(" expression ")" ;
//! literal     -> NUMBER | STRING | "true" | "false" | "nil" ;
use std::fmt;

use crate::span::Span;

#[derive(Debug, PartialEq, Eq)]
pub enum UnOp {
    Minus,
    Not,
}

#[derive(Debug, PartialEq)]
pub enum NumberKind {
    Integer(u32),
    Float(f32),
}

#[derive(Debug, PartialEq)]
pub enum Literal<'s> {
    Number(NumberKind),
    String(&'s str),
    True,
    False,
    Nil,
}

#[derive(Debug, PartialEq)]
pub enum Primary<'s> {
    Literal(Literal<'s>),
    /// grouped expression "(" expr ")"
    Grouped(Box<Expr<'s>>),
}

#[derive(Debug, PartialEq)]
pub enum UnaryKind<'s> {
    UnOp {
        op: Option<UnOp>,
        unary: Box<Unary<'s>>,
    },
    Primary(Primary<'s>),
}

#[derive(Debug, PartialEq)]
pub struct Unary<'s> {
    pub kind: UnaryKind<'s>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum FactorOp {
    Div,
    Mul,
}

#[derive(Debug, PartialEq)]
pub struct Factor<'s> {
    pub lhs: Unary<'s>,
    pub rhs: Option<(FactorOp, Unary<'s>)>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum TermOp {
    Plus,
    Minus,
}

#[derive(Debug, PartialEq)]
pub struct Term<'s> {
    pub lhs: Factor<'s>,
    pub rhs: Option<(TermOp, Factor<'s>)>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum Compare {
    Lt,
    Leq,
    Gt,
    Geq,
}

#[derive(Debug, PartialEq)]
pub struct Comparison<'s> {
    pub lhs: Term<'s>,
    pub rhs: Option<(Compare, Term<'s>)>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum EqOp {
    Eq,
    Neq,
}

#[derive(Debug, PartialEq)]
pub struct Equality<'s> {
    pub lhs: Comparison<'s>,
    pub rhs: Option<(EqOp, Comparison<'s>)>,
    pub span: Span,
}

#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub enum ExprKind<'s> {
    Equality(Equality<'s>),
}

#[derive(Debug, PartialEq)]
pub struct Expr<'s> {
    pub kind: ExprKind<'s>,
    pub span: Span,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let token = match self {
            UnOp::Minus => "-",
            UnOp::Not => "!",
        };

        write!(f, "{token}")
    }
}

impl<'s> fmt::Display for Literal<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Literal::*;

        let token = match self {
            Number(kind) => match kind {
                NumberKind::Integer(n) => return write!(f, "{n}"),
                NumberKind::Float(n) => return write!(f, "{n}"),
            },
            String(s) => s,
            True => "true",
            False => "false",
            Nil => "nil",
        };

        write!(f, "{token}")
    }
}

impl<'s> fmt::Display for Primary<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Primary::Literal(ref lit) => lit.fmt(f),
            Primary::Grouped(box expr) => expr.fmt(f),
        }
    }
}

impl<'s> fmt::Display for Unary<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            UnaryKind::UnOp { op, unary } => match op {
                Some(op) => write!(f, "{}{}", op, unary),
                None => write!(f, "{}", unary),
            },
            UnaryKind::Primary(primary) => primary.fmt(f),
        }
    }
}

impl fmt::Display for FactorOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            FactorOp::Div => "/",
            FactorOp::Mul => "*",
        };
        write!(f, "{op}")
    }
}

impl fmt::Display for TermOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            TermOp::Plus => "+",
            TermOp::Minus => "-",
        };
        write!(f, "{op}")
    }
}

impl fmt::Display for Compare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Compare::*;
        let op = match self {
            Lt => "<",
            Leq => "<=",
            Gt => ">",
            Geq => ">=",
        };
        write!(f, "{op}")
    }
}

impl fmt::Display for EqOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            EqOp::Eq => "==",
            EqOp::Neq => "!=",
        };
        write!(f, "{op}")
    }
}

// macro to impl fmt::Display for struct s.t. lhs and optional rhs.
macro_rules! impl_display {
    ($strukt:ident) => {
        impl<'s> ::std::fmt::Display for $strukt<'s> {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                match &self.rhs {
                    None => write!(f, "{}", self.lhs),
                    Some((op, rhs)) => write!(f, "{} {} {}", self.lhs, op, rhs),
                }
            }
        }
    };
}

impl_display!(Factor);
impl_display!(Term);
impl_display!(Comparison);
impl_display!(Equality);

impl<'s> fmt::Display for Expr<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ExprKind::Equality(ref equality) => equality.fmt(f),
        }
    }
}
