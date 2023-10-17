#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]

use std::{
    io::{self, BufWriter, Write},
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
    let mut out = BufWriter::new(io::stdout());

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                let stmt = match Parser::new(&line).parse() {
                    Ok(stmt) => stmt,
                    Err(e) => {
                        eprintln!("{e}");
                        continue;
                    }
                };
                let mut interpreter = Interpreter::new(&mut out);
                match interpreter.stmt(&stmt) {
                    Ok(_) => {}
                    Err(e) => eprintln!("{e}"),
                }
                out.flush().unwrap();
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
