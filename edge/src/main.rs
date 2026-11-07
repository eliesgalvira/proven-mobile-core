use std::path::Path;
use std::process::ExitCode;

use edge::config::Config;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let path = match args.as_slice() {
        [_, flag, path] if flag == "--config" => path,
        _ => {
            eprintln!("usage: edge --config <file>");
            return ExitCode::from(2);
        }
    };
    let config = match Config::load(Path::new(path)) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("edge: {e}");
            return ExitCode::from(2);
        }
    };
    match edge::edge::run(&config) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("edge: {e}");
            ExitCode::FAILURE
        }
    }
}
