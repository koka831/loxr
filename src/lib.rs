use std::{borrow::Cow, path::Path};

use lexer::Lexer;
use rustyline::{error::ReadlineError, DefaultEditor};
use span::Span;
use thiserror::Error;

pub mod lexer;
pub mod span;
pub mod token;

#[derive(Debug, Error)]
pub enum LoxError<'a> {
    #[error("failed to tokenize at {span:?}: {message}")]
    LexError { message: Cow<'a, str>, span: Span },

    #[error("syntax error at {span:?}: {message}")]
    SyntaxError { message: Cow<'a, str>, span: Span },

    #[error("could not read file: {0}")]
    IoError(#[from] std::io::Error),

    #[error("could not parse literal into number at {span:?}: {message}")]
    ParseNumError { message: Cow<'a, str>, span: Span },

    #[error(transparent)]
    Other(anyhow::Error),
}

impl From<anyhow::Error> for LoxError<'_> {
    fn from(e: anyhow::Error) -> Self {
        LoxError::Other(e)
    }
}

pub fn prompt() -> Result<(), LoxError<'static>> {
    let mut rl = DefaultEditor::new().map_err(|e| LoxError::Other(e.into()))?;

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                let lexer = Lexer::new(&line);
                let lexed = lexer.collect::<Result<Vec<_>, LoxError<'_>>>();
                dbg!(lexed);
            }
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("lox: failed to read stdin\n{e}");
                break;
            }
        }
    }

    Ok(())
}

pub fn exec_file<'s, P: AsRef<Path> + 's>(path: P) -> Result<(), LoxError<'s>> {
    let content = std::fs::read_to_string(path)?;

    for lexed in Lexer::new(&content) {
        dbg!(lexed);
    }

    Ok(())
}

pub fn interpret(_source: String) {
    // let lexed = Lexer::new(source);
}
