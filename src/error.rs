use crate::interpreter::Rt;
use crate::span::Span;
use crate::token::Token;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LoxError {
    #[error("failed to tokenize at {span:?}: {e}")]
    LexError { e: LexError, span: Span },

    #[error("unexpected end of file")]
    UnexpectedEOF,

    #[error("unexpected token: expect {expect}, found `{actual}`")]
    UnexpectedToken { expect: String, actual: Token },

    #[error("syntax error at {span:?}: {message}")]
    SyntaxError { message: String, span: Span },

    #[error("could not read file: {0}")]
    IoError(#[from] std::io::Error),

    #[error(transparent)]
    Other(anyhow::Error),

    #[error("internal use")]
    _Return(Rt),
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

impl From<LexError> for LoxError {
    fn from(e: LexError) -> Self {
        LoxError::LexError { e, span: e.span() }
    }
}

impl From<anyhow::Error> for LoxError {
    fn from(e: anyhow::Error) -> Self {
        LoxError::Other(e)
    }
}
