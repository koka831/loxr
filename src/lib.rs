#![forbid(unsafe_code)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(assert_matches)]

use std::{
    io::{self, BufWriter},
    path::Path,
};

use error::LoxError;

use crate::{diagnosis::DiagnosticReporter, interpreter::Interpreter};

pub mod ast;
pub mod diagnosis;
pub mod error;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

// pub fn prompt<'a>() -> Result<(), LoxError<'a>> {
//     let mut rl = DefaultEditor::new().unwrap();
//     let mut out = BufWriter::new(io::stdout());
//     let mut interpreter = Interpreter::new(&mut out);

//     let source = Rc::new(RefCell::new(Vec::new()));

//     loop {
//         match rl.readline(">> ") {
//             Ok(line) => {
//                 source.borrow_mut().push(line);

//                 let len = source.borrow().len();
//                 if let Err(e) = interpreter.execute(source.borrow()[len - 1])
//                 {
//                     eprintln!("{e}");
//                 }
//             }
//             Err(ReadlineError::Eof) => break,
//             Err(e) => {
//                 eprintln!("lox: failed to read stdin\n{e}");
//                 break;
//             }
//         }
//     }

//     Ok(())
// }

pub fn exec_file<'s, P: AsRef<Path> + 's>(path: P) -> Result<(), LoxError<'s>> {
    let content = std::fs::read_to_string(path).unwrap();

    let mut out = BufWriter::new(io::stdout());
    if let Err(e) = Interpreter::new(&mut out).execute(&content) {
        let mut stderr = BufWriter::new(io::stderr().lock());
        DiagnosticReporter::new(&mut stderr).report(&e, &content);
    }

    Ok(())
}
