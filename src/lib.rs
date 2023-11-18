#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

use std::{
    io::{self, BufWriter},
    path::Path,
};

use error::LoxError;
use rustyline::{error::ReadlineError, DefaultEditor};

use crate::{diagnosis::DiagnosticReporter, interpreter::Interpreter};

pub mod ast;
pub mod diagnosis;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub fn prompt() -> Result<(), LoxError> {
    let mut rl = DefaultEditor::new().unwrap();
    let mut out = BufWriter::new(io::stdout());
    let mut interpreter = Interpreter::new(&mut out);

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                if let Err(e) = interpreter.execute(&line) {
                    eprintln!("{e}");
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

pub fn exec_file<P: AsRef<Path>>(path: P) -> Result<(), LoxError> {
    let content = std::fs::read_to_string(path).unwrap();

    let mut out = BufWriter::new(io::stdout());
    if let Err(e) = Interpreter::new(&mut out).execute(&content) {
        let mut stderr = BufWriter::new(io::stderr().lock());
        DiagnosticReporter::new(&mut stderr).report(&e, &content);
    }

    Ok(())
}
