#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]
#![allow(clippy::needless_range_loop)]

use std::io::{self, BufWriter};
use std::path::Path;

use error::LoxError;
use wasm_bindgen::prelude::*;

use crate::diagnosis::DiagnosticReporter;
use crate::interpreter::Interpreter;

pub mod ast;
pub mod diagnosis;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

#[wasm_bindgen]
pub fn interpret(program: &str) -> String {
    let mut out = BufWriter::new(Vec::new());
    match Interpreter::new(&mut out).execute(program) {
        Ok(()) => String::from_utf8(out.into_inner().unwrap()).unwrap(),
        Err(e) => e.to_string(),
    }
}

pub fn exec_file<P: AsRef<Path>>(path: P) -> Result<(), LoxError> {
    let content = std::fs::read_to_string(path).unwrap();

    let mut out = BufWriter::new(io::stdout());
    if let Err(e) = Interpreter::new(&mut out).execute(&content) {
        let mut stderr = BufWriter::new(io::stderr().lock());
        DiagnosticReporter::new(&mut stderr).report(&e, &content);
        return Err(e);
    }

    Ok(())
}
