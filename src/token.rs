use std::fmt;

use crate::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Token {
        Token { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TokenKind {
    // keyword
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    True,
    Var,
    While,

    // literal
    Ident(String),
    String(String),
    Number(NumberKind),

    /// (
    LParen,
    /// )
    RParen,
    /// {
    LBrace,
    /// }
    RBrace,
    /// ,
    Comma,
    /// .
    Dot,
    /// +
    Plus,
    /// -
    Minus,
    /// ;
    Semicolon,
    /// /
    Slash,
    /// *
    Star,

    /// !
    Bang,
    /// !=
    BangEq,
    /// =
    Eq,
    /// ==
    EqEq,
    /// <
    Lt,
    /// <=
    Leq,
    /// >
    Gt,
    /// >=
    Geq,
}

#[derive(Debug, Clone, PartialEq)]
pub enum NumberKind {
    Integer(i32),
    Float(f32),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let token = match self {
            TokenKind::And => "and",
            TokenKind::Class => "class",
            TokenKind::Else => "else",
            TokenKind::False => "false",
            TokenKind::Fun => "fun",
            TokenKind::For => "for",
            TokenKind::If => "if",
            TokenKind::Nil => "nil",
            TokenKind::Or => "or",
            TokenKind::Print => "print",
            TokenKind::Return => "return",
            TokenKind::Super => "super",
            TokenKind::True => "true",
            TokenKind::Var => "var",
            TokenKind::While => "while",
            TokenKind::Ident(ident) => return write!(f, "Ident({ident})"),
            TokenKind::String(s) => return write!(f, "String({s})"),
            TokenKind::Number(ref kind) => {
                return match kind {
                    NumberKind::Integer(n) => write!(f, "Integer({n})"),
                    NumberKind::Float(n) => write!(f, "Float({n})"),
                }
            }
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Semicolon => ";",
            TokenKind::Slash => "/",
            TokenKind::Star => "*",
            TokenKind::Bang => "!",
            TokenKind::BangEq => "!=",
            TokenKind::Eq => "=",
            TokenKind::EqEq => "==",
            TokenKind::Lt => "<",
            TokenKind::Leq => "<=",
            TokenKind::Gt => ">",
            TokenKind::Geq => ">=",
        };

        write!(f, "{token}")
    }
}
