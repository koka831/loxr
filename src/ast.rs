//! A Grammer for Lox expressions
//!
//! Legend:
//! CAPITALIZE -- terminal symbol; literal.
//! x -> a ;   -- definition of x (non-terminal)
//!
//! ## Expressions:
//!
//! expr        -> unary | binary | grouped | literal ;
//! unary       -> ( "-" | "!" ) expr ;
//! binary      -> expr ( "!=" | "==" | ">" | ">=" | "<" | "<=" | "-" | "+" | "/" | "*") expr ;
//! grouped     -> "(" expr ")" ;
//! literal     -> NUMBER | STRING | "true" | "false" | "nil" ;
use std::fmt;

use crate::span::Span;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnOp {
    Minus,
    Not,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Literal<'s> {
    Integer(i32),
    Float(f32),
    String(&'s str),
    True,
    False,
    Nil,
}

impl<'s> Literal<'s> {
    pub fn from_boolean(b: bool) -> Literal<'s> {
        if b {
            Literal::True
        } else {
            Literal::False
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    /// !=
    Neq,
    /// ==
    Eq,
    /// >
    Gt,
    /// >=
    Geq,
    /// <
    Lt,
    /// <=
    Leq,
    /// -
    Minus,
    /// +
    Plus,
    /// /
    Div,
    /// *
    Mul,
}

#[derive(Debug, PartialEq)]
/// undividable element of `Expr`
pub enum Term<'s> {
    Grouped(Box<Expr<'s>>),
    Literal(Literal<'s>),
}

#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub enum ExprKind<'s> {
    Binary(BinOp, Box<Expr<'s>>, Box<Expr<'s>>),
    Unary(UnOp, Box<Expr<'s>>),
    Term(Term<'s>),
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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinOp::*;

        let token = match self {
            Neq => "!=",
            Eq => "==",
            Gt => ">",
            Geq => ">=",
            Lt => "<",
            Leq => "<=",
            Minus => "-",
            Plus => "+",
            Div => "/",
            Mul => "*",
        };

        write!(f, "{token}")
    }
}

impl<'s> fmt::Display for Literal<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Literal::*;

        let token = match self {
            Integer(n) => return write!(f, "{n}"),
            Float(n) => return write!(f, "{n}"),
            String(s) => s,
            True => "true",
            False => "false",
            Nil => "nil",
        };

        write!(f, "{token}")
    }
}

impl<'s> fmt::Display for Term<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Grouped(box expr) => write!(f, "({expr})"),
            Term::Literal(lit) => lit.fmt(f),
        }
    }
}

impl<'s> fmt::Display for Expr<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Unary(op, box expr) => {
                write!(f, "{op}{expr}")
            }
            ExprKind::Binary(op, box lhs, box rhs) => {
                write!(f, "{lhs} {op} {rhs}")
            }
            ExprKind::Term(term) => term.fmt(f),
        }
    }
}
