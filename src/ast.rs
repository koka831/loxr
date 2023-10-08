//! A Grammer for Lox expressions
//!
//! Legend:
//! CAPITALIZE -- terminal symbol; literal.
//! x -> a ;   -- definition of x (non-terminal)
//!
//!
//! expression  -> literal | unary | binary | grouping ;
//! literal     -> NUMBER | STRING | "true" | "false" | "nil" ;
//! grouping    -> "(" expression ")" ;
//! unary       -> ( "-" | "!" ) expression ;
//! binary      -> expression operator expression
//! operator    -> "==" | "!=" | "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/" ;
use std::fmt;

use crate::span::Span;

#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    /// "=="
    Equal,
    /// "!="
    NotEqual,
    /// "<"
    Lt,
    /// "<="
    Leq,
    /// ">"
    Gt,
    /// ">="
    Geq,
    Plus,
    Minus,
    Mul,
    Div,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinOp::*;

        let token = match self {
            Equal => "==",
            NotEqual => "!=",
            Lt => "<",
            Leq => "<=",
            Gt => ">",
            Geq => ">=",
            Plus => "+",
            Minus => "-",
            Mul => "*",
            Div => "/",
        };

        write!(f, "{token}")
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnOp {
    Minus,
    Not,
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

pub enum NumberKind {
    Integer(u32),
    Float(f32),
}

pub enum Literal<'s> {
    Number(NumberKind),
    String(&'s str),
    True,
    False,
    Nil,
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

pub struct Binary<'s> {
    pub lhs: Box<Expr<'s>>,
    pub op: BinOp,
    pub rhs: Box<Expr<'s>>,
}

impl<'s> fmt::Display for Binary<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.op, self.rhs)
    }
}

pub struct Unary<'s> {
    pub op: UnOp,
    pub rhs: Box<Expr<'s>>,
}

impl<'s> fmt::Display for Unary<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.op, self.rhs)
    }
}

pub enum ExprKind<'s> {
    Literal(Literal<'s>),
    BinOp(Binary<'s>),
    UnOp(Unary<'s>),
    Group(Box<Expr<'s>>),
}

pub struct Expr<'s> {
    pub kind: ExprKind<'s>,
    pub span: Span,
}

impl<'s> fmt::Display for Expr<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExprKind::*;

        match self.kind {
            Literal(ref lit) => lit.fmt(f),
            BinOp(ref binary) => binary.fmt(f),
            UnOp(ref unary) => unary.fmt(f),
            Group(box ref expr) => write!(f, "({})", expr),
        }
    }
}
