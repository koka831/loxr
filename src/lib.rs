#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]

use std::path::Path;

use error::LoxError;
use lexer::Lexer;
use rustyline::{error::ReadlineError, DefaultEditor};

use crate::{ast::Expr, interpreter::Interpreter, parser::Parser};

pub mod ast;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub fn prompt<'a>() -> Result<(), LoxError<'a>> {
    let mut rl = DefaultEditor::new().unwrap();

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                let mut parser = Parser::new(&line);
                let expr = parser.parse::<Expr>().unwrap();
                let result = Interpreter::new().expr(&expr).unwrap();
                println!("{result}");
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
    let content = std::fs::read_to_string(path).unwrap();

    for lexed in Lexer::new(&content) {
        dbg!(lexed);
    }

    Ok(())
}

pub fn interpret(_source: String) {
    // let lexed = Lexer::new(source);
}
