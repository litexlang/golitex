use super::source_compilation::compile_litex_source_to_lean_source;
use crate::prelude::*;
use std::fs;
use std::path::Path;

pub fn compile_litex_file_to_lean_file(
    source_path: &Path,
    output_path: &Path,
) -> Result<(), String> {
    record_pipeline_step(
        "lean compiler",
        "compile_litex_file_to_lean_file",
        "src/stmt_result_to_lean_compiler/file_compilation.rs",
    );
    reject_same_input_and_output(source_path, output_path)?;

    let source = fs::read_to_string(source_path)
        .map_err(|error| format!("failed to read {}: {error}", source_path.display()))?;
    let generated =
        compile_litex_source_to_lean_source(&source, &source_path.display().to_string()).map_err(
            |error| {
                format!(
                    "failed to compile {} to Lean: {error}",
                    source_path.display()
                )
            },
        )?;

    if let Some(parent) = output_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|error| {
                format!(
                    "failed to create output directory {}: {error}",
                    parent.display()
                )
            })?;
        }
    }
    fs::write(output_path, generated)
        .map_err(|error| format!("failed to write {}: {error}", output_path.display()))
}

fn reject_same_input_and_output(source_path: &Path, output_path: &Path) -> Result<(), String> {
    if source_path == output_path {
        return Err("the Litex input and Lean output paths must be different".to_string());
    }

    let canonical_source = fs::canonicalize(source_path)
        .map_err(|error| format!("failed to resolve {}: {error}", source_path.display()))?;
    if output_path.exists() {
        let canonical_output = fs::canonicalize(output_path)
            .map_err(|error| format!("failed to resolve {}: {error}", output_path.display()))?;
        if canonical_source == canonical_output {
            return Err("the Litex input and Lean output paths must be different".to_string());
        }
    }
    Ok(())
}
