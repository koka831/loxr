//! A Grammer for Lox expressions
//!
//! Legend:
//! CAPITALIZE -- terminal symbol; literal.
//! x -> a ;   -- definition of x (non-terminal)
//!
//! ## Expressions:
//!
//! expr        -> unary | binary | term | assignment ;
//! term        -> grouped | ident | literal | call ;
//! unary       -> ( "-" | "!" ) expr ;
//! call        -> term "(" ( expr ( "," expr )* )? ")" ;
//! binary      -> expr (
//!                  "!=" | "==" | ">" | ">=" | "<" | "<=" | "-" | "+" | "/" | "*" | "and" | "or"
//!                ) expr ;
//! grouped     -> "(" expr ")" ;
//! assignment  -> ident "=" expr ;
//! literal     -> NUMBER | STRING | "true" | "false" | "nil" ;
//!
//! ## Statements:
//!
//! program     -> statement* EOF ;
//!
//! statement   -> expression ";" ;
//!             | "print" expression ";" ;
//!             | "fun" ident "(" ( ident ( "," ident )* )? ")" block stmt ;
//!             | "var" ident "=" expression ";" ;
//!             | "{" statement* "}" ;
//!             | "if" "(" ")" statement ( "else" statement )? ;
//!             | "while" "(" expression ")" statement ;
//!             | "for" "(" (DeclVar | expr stmt | ";") expression? ";" expression? ")" statement ;
//!             | "return" expression? ";" ;
use std::{fmt, rc::Rc};

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
    pub fn truthy(&self) -> bool {
        !self.falsy()
    }

    pub fn falsy(&self) -> bool {
        matches!(self, Literal::False | Literal::Nil)
    }
}

impl<'s> From<bool> for Literal<'s> {
    fn from(value: bool) -> Self {
        if value {
            Literal::True
        } else {
            Literal::False
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    /// "and"
    And,
    /// "or"
    Or,
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
    Ident(Ident<'s>),
    FnCall {
        callee: Ident<'s>,
        arguments: Vec<Expr<'s>>,
    },
}

#[derive(Debug, PartialEq)]
pub enum ExprKind<'s> {
    Binary(BinOp, Box<Expr<'s>>, Box<Expr<'s>>),
    Unary(UnOp, Box<Expr<'s>>),
    Term(Term<'s>),
    // assign a value to a defined variable.
    Assign {
        name: Ident<'s>,
        expr: Box<Expr<'s>>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Expr<'s> {
    pub kind: ExprKind<'s>,
    pub span: Span,
}

impl<'s> Expr<'s> {
    pub fn nil() -> Self {
        Expr {
            kind: ExprKind::Term(Term::Literal(Literal::Nil)),
            span: Span::new(0, 0),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Ident<'s>(pub &'s str);

#[derive(Debug, PartialEq, Clone)]
pub struct Fn<'a> {
    pub name: Ident<'a>,
    pub params: Vec<Ident<'a>>,
    pub body: Vec<Rc<Stmt<'a>>>,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind<'s> {
    /// expression ;
    /// used for call an expression with side-effect.
    Expr(Expr<'s>),
    /// print expression ;
    Print(Expr<'s>),
    /// function declaration
    /// fun ident ( params ) { stmt }
    DefFun(Fn<'s>),
    /// variable declaration
    /// var ident ( = expr )? ;
    DeclVar {
        name: Ident<'s>,
        initializer: Rc<Expr<'s>>,
    },
    Block(Vec<Rc<Stmt<'s>>>),
    /// if ( expr ) statement ( else statement )?
    If {
        condition: Expr<'s>,
        then_branch: Rc<Stmt<'s>>,
        else_branch: Option<Rc<Stmt<'s>>>,
    },
    /// while ( expr ) statement
    While {
        condition: Expr<'s>,
        stmt: Rc<Stmt<'s>>,
    },
    /// for (init; (test; (after;)? )?) stmt
    For {
        init: Rc<Stmt<'s>>,
        test: Option<Rc<Expr<'s>>>,
        after: Option<Rc<Expr<'s>>>,
        body: Rc<Stmt<'s>>,
    },
    /// return expr? ;
    Return(Option<Rc<Expr<'s>>>),
}

#[derive(Debug, PartialEq)]
pub struct Stmt<'s> {
    pub kind: StmtKind<'s>,
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
            And => "and",
            Or => "or",
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

impl<'s> fmt::Display for Ident<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'s> fmt::Display for Fn<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params = self
            .params
            .iter()
            .map(|p| p.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "fun {}({params}) {{ .. }}", self.name)
    }
}

impl<'s> fmt::Display for Term<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Grouped(box expr) => write!(f, "({expr})"),
            Term::Literal(lit) => lit.fmt(f),
            Term::Ident(ident) => ident.fmt(f),
            Term::FnCall { callee, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{callee}({arguments})")
            }
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
            ExprKind::Assign { name, box expr } => {
                write!(f, "{name} = {expr}")
            }
        }
    }
}

impl<'s> fmt::Display for Stmt<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StmtKind::Expr(expr) => expr.fmt(f),
            StmtKind::Print(expr) => write!(f, "print {expr}"),
            StmtKind::DefFun(fun) => fun.fmt(f),
            StmtKind::DeclVar { name, initializer } => write!(f, "var {name} = {initializer}"),
            StmtKind::Block(block) => write!(f, "{{ {} lines }}", block.len()),
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => match else_branch {
                None => write!(f, "if ({condition}) {then_branch}"),
                Some(else_branch) => write!(f, "if ({condition}) {then_branch} else {else_branch}"),
            },
            StmtKind::While { condition, stmt } => write!(f, "while ({condition}) {stmt}"),
            StmtKind::For {
                init,
                test,
                after,
                body,
            } => {
                write!(f, "for ({init}")?;
                if let Some(test) = test {
                    write!(f, "; {test}")?;
                }
                if let Some(after) = after {
                    write!(f, "; {after}")?;
                }
                write!(f, ")")?;
                write!(f, "{body}")
            }
            StmtKind::Return(expr) => match expr {
                Some(expr) => write!(f, "return {expr}"),
                None => write!(f, "return"),
            },
        }
    }
}
