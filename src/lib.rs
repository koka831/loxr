#![forbid(unsafe_code)]
#![feature(box_patterns)]

use std::path::Path;

use error::LexError;
use lexer::Lexer;
use rustyline::{error::ReadlineError, DefaultEditor};

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub fn prompt() -> Result<(), LexError> {
    let mut rl = DefaultEditor::new().unwrap();

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                let lexer = Lexer::new(&line);
                let lexed = lexer.collect::<Result<Vec<_>, LexError>>();
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

pub fn exec_file<'s, P: AsRef<Path> + 's>(path: P) -> Result<(), LexError> {
    let content = std::fs::read_to_string(path).unwrap();

    for lexed in Lexer::new(&content) {
        dbg!(lexed);
    }

    Ok(())
}

pub fn interpret(_source: String) {
    // let lexed = Lexer::new(source);
}
