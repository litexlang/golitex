use crate::stmt_result_to_lean_compiler::compile_litex_file_to_lean_file;
use std::path::Path;
use std::process;

pub(super) fn run_lean_file_command(file_path: &str, output_path: &str) {
    match compile_litex_file_to_lean_file(Path::new(file_path), Path::new(output_path)) {
        Ok(()) => println!("wrote freshly generated Lean to {}", output_path),
        Err(message) => {
            eprintln!("{}", message);
            process::exit(1);
        }
    }
}
