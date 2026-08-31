use super::json_output::{render_artifact, simple_error};
use crate::prelude::JsonValue;
use crate::stmt_result_to_lean_compiler::compile_litex_file_to_lean_file;
use std::path::Path;

pub(super) fn run_lean_file_command(file_path: &str, output_path: &str) -> bool {
    match compile_litex_file_to_lean_file(Path::new(file_path), Path::new(output_path)) {
        Ok(()) => {
            println!(
                "{}",
                render_artifact(
                    "compiled_source",
                    "lean",
                    "file",
                    Some(file_path),
                    Some(output_path),
                    JsonValue::Null,
                    JsonValue::Null,
                )
            );
            true
        }
        Err(message) => {
            println!(
                "{}",
                render_artifact(
                    "compiled_source",
                    "lean",
                    "file",
                    Some(file_path),
                    Some(output_path),
                    JsonValue::Null,
                    simple_error("lean_compilation_error", message.as_str()),
                )
            );
            false
        }
    }
}
