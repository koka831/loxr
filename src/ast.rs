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
//!             | "class" ident "{" method* "}"
//!             | "fun" ident "(" ( ident ( "," ident )* )? ")" block stmt ;
//!             | "var" ident "=" expression ";" ;
//!             | "{" statement* "}" ;
//!             | "if" "(" ")" statement ( "else" statement )? ;
//!             | "while" "(" expression ")" statement ;
//!             | "for" "(" (DeclVar | expr stmt | ";") expression? ";" expression? ")" statement ;
//!             | "return" expression? ";" ;
//!
//! method      -> ident "( ident ("," ident )* ")" block ;
use std::fmt;
use std::rc::Rc;

use crate::span::Span;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnOp {
    Minus,
    Not,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    Integer(i32),
    Float(f32),
    String(String),
    True,
    False,
    Nil,
}

impl Literal {
    pub fn truthy(&self) -> bool {
        !self.falsy()
    }

    pub fn falsy(&self) -> bool {
        matches!(self, Literal::False | Literal::Nil)
    }
}

impl From<bool> for Literal {
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
pub struct FnCall {
    pub callee: Ident,
    pub arguments: Vec<Expr>,
}

#[derive(Debug, PartialEq)]
/// undividable element of `Expr`
pub enum Term {
    Grouped(Box<Expr>),
    Literal(Literal),
    Ident(Ident),
    FnCall(FnCall),
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Term(Term),
    // assign a value to a defined variable.
    Assign { name: Ident, expr: Box<Expr> },
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn nil() -> Self {
        Expr {
            kind: ExprKind::Term(Term::Literal(Literal::Nil)),
            span: Span::new(0, 0),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Ident(pub String);

#[derive(Debug, PartialEq, Clone)]
pub struct Class {
    pub name: Ident,
    pub methods: Vec<Fn>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Fn {
    pub name: Ident,
    pub params: Vec<Ident>,
    pub body: Vec<Rc<Stmt>>,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    /// expression ;
    /// used for call an expression with side-effect.
    Expr(Expr),
    /// print expression ;
    Print(Expr),
    /// class declaration
    DeclClass(Class),
    /// function declaration
    /// fun ident ( params ) { stmt }
    DefFun(Fn),
    /// variable declaration
    /// var ident ( = expr )? ;
    DeclVar {
        name: Ident,
        initializer: Rc<Expr>,
    },
    Block(Vec<Rc<Stmt>>),
    /// if ( expr ) statement ( else statement )?
    If {
        condition: Expr,
        then_branch: Rc<Stmt>,
        else_branch: Option<Rc<Stmt>>,
    },
    /// while ( expr ) statement
    While {
        condition: Expr,
        stmt: Rc<Stmt>,
    },
    /// for (init; (test; (after;)? )?) stmt
    For {
        init: Rc<Stmt>,
        test: Option<Rc<Expr>>,
        after: Option<Rc<Expr>>,
        body: Rc<Stmt>,
    },
    /// return expr? ;
    Return(Option<Rc<Expr>>),
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
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

impl fmt::Display for Literal {
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

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Fn {
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

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Grouped(box expr) => write!(f, "({expr})"),
            Term::Literal(lit) => lit.fmt(f),
            Term::Ident(ident) => ident.fmt(f),
            Term::FnCall(FnCall { callee, arguments }) => {
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

impl fmt::Display for Expr {
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

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StmtKind::Expr(expr) => expr.fmt(f),
            StmtKind::Print(expr) => write!(f, "print {expr}"),
            StmtKind::DeclClass(class) => write!(f, "class {}", class.name),
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
