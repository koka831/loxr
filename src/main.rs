use std::env;

use loxr::{exec_file, prompt};
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
        tracing::error!("loxr did not finish normally: {e}");
        std::process::exit(1);
    }
}
