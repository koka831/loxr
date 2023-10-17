#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]

use std::{
    io::{self, BufWriter},
    path::Path,
};

use error::LoxError;
use rustyline::{error::ReadlineError, DefaultEditor};

use crate::{interpreter::Interpreter, parser::Parser};

pub mod ast;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub fn prompt<'a>() -> Result<(), LoxError<'a>> {
    let mut rl = DefaultEditor::new().unwrap();
    let mut out = BufWriter::new(io::stdout().lock());

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                let stmts = parser::parse(&line);
                let mut interpreter = Interpreter::new(&mut out);
                for stmt in stmts {
                    match interpreter.stmt(&stmt) {
                        Ok(_) => {}
                        Err(e) => eprintln!("{e}"),
                    }
                }
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

    let mut out = BufWriter::new(io::stdout());
    let expr = Parser::new(&content).parse().unwrap();
    let result = Interpreter::new(&mut out).expr(&expr).unwrap();
    println!("{result}");

    Ok(())
}
