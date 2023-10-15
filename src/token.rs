use crate::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'s> {
    pub kind: TokenKind<'s>,
    pub span: Span,
}

impl<'s> Token<'s> {
    pub fn new(kind: TokenKind, span: Span) -> Token<'_> {
        Token { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TokenKind<'s> {
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
    Ident(&'s str),
    String(&'s str),
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
