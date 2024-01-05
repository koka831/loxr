use loxr::error::LoxError;
use loxr::exec_file;
use loxr::interpreter::Interpreter;
#[cfg(not(target_arch = "wasm32"))]
use rustyline::error::ReadlineError;
#[cfg(not(target_arch = "wasm32"))]
use rustyline::DefaultEditor;
use std::io::BufWriter;
use std::{env, io};
use tracing_subscriber::prelude::*;
use tracing_subscriber::{fmt, EnvFilter};

fn main() {
    let filter_layer = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new("rustyline=warn,loxr::lexer=warn,loxr::parser=warn,info"))
        .unwrap();
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(filter_layer)
        .init();

    let args: Vec<String> = env::args().collect();
    let res = if let Some(fpath) = args.get(1) {
        exec_file(fpath)
    } else {
        prompt()
    };

    if let Err(e) = res {
        tracing::info!("loxr did not finish normally: {e}");
        std::process::exit(1);
    }
}

#[cfg(target_arch = "wasm32")]
pub fn prompt() -> Result<(), LoxError> {
    unimplemented!()
}

#[cfg(not(target_arch = "wasm32"))]
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
