use std::borrow::Cow;

use crate::{interpreter::Rt, span::Span, token::Token};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LoxError<'a> {
    #[error("failed to tokenize at {span:?}: {e}")]
    LexError { e: LexError, span: Span },

    #[error("unexpected end of file")]
    UnexpectedEOF,

    #[error("unexpected token: expect {expect}, found `{actual}`")]
    UnexpectedToken {
        expect: Cow<'a, str>,
        actual: Token<'a>,
    },

    #[error("syntax error at {span:?}: {message}")]
    SyntaxError { message: Cow<'a, str>, span: Span },

    #[error("could not read file: {0}")]
    IoError(#[from] std::io::Error),

    #[error(transparent)]
    Other(anyhow::Error),

    #[error("internal use")]
    _Return(Rt<'a>),
}

#[derive(Debug, Copy, Clone, Error)]
pub enum LexError {
    #[error("unterminated string quotation")]
    UnterminatedString(Span),

    #[error("could not parse number")]
    InvalidNumber(Span),
}

impl LexError {
    fn span(&self) -> Span {
        match self {
            LexError::UnterminatedString(span) => *span,
            LexError::InvalidNumber(span) => *span,
        }
    }
}

impl<'a> From<LexError> for LoxError<'a> {
    fn from(e: LexError) -> Self {
        LoxError::LexError { e, span: e.span() }
    }
}

impl From<anyhow::Error> for LoxError<'_> {
    fn from(e: anyhow::Error) -> Self {
        LoxError::Other(e)
    }
}
