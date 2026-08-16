use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;

use crate::compile_to_lean::compile_to_lean;
use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{run_with_large_stack, source_has_isolated_import};

fn run_example_lit_file(relative_path: &str) {
    let lit_path = example_lit_path(relative_path);

    let lit_content = match fs::read_to_string(&lit_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", lit_path, read_error),
    };
    if lit_content.trim().is_empty() {
        println!("examples/{} is empty; skip run", relative_path);
        return;
    }

    let path_str = match lit_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", lit_path),
    };

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(path_str);
    let normalized_source = remove_windows_carriage_return(lit_content.as_str());
    runtime.isolated = source_has_isolated_import(normalized_source.as_str());

    let start_time = Instant::now();
    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let status_label = if run_succeeded { "OK" } else { "FAILED" };
    println!(
        "{}\n=== [{}] {:?} ({:.2} ms user file only) ===\n",
        run_output, path_str, status_label, duration_ms
    );
    let error_json = match &runtime_error {
        Some(error) => display_runtime_error_json(&runtime, error, false),
        None => run_output.clone(),
    };
    assert!(
        run_succeeded,
        "examples/{} failed.\n\n>>> Litex error JSON:\n{}\n\n=== [{}] {:?} ({:.2} ms user file only) ===",
        relative_path, error_json, path_str, status_label, duration_ms
    );
}

#[test]
fn run_tmp0() {
    run_with_large_stack("run_tmp0_large_stack", || run_example_lit_file("tmp.lit"));
}

fn compile_tmp_to_lean() {
    let source_path = "examples/tmp.lit";
    let lit_path = example_lit_path("tmp.lit");
    let lit_content = fs::read_to_string(&lit_path)
        .unwrap_or_else(|read_error| panic!("failed to read {:?}: {}", lit_path, read_error));
    let lit_source = source_without_trailing_triple_quoted_block(&lit_content).trim();
    if lit_source.is_empty() {
        let output = "\n=== LITEX -> LEAN: examples/tmp.lit is empty ===\n\
             Put Litex source in that file and rerun:\n  \
             cargo test --release tmp0_to_lean\n";
        write_scratch_command_output(output);
        return;
    }

    let path_str = lit_path
        .to_str()
        .unwrap_or_else(|| panic!("{:?} must be valid UTF-8", lit_path));
    let normalized_source = remove_windows_carriage_return(lit_source);
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(path_str);
    runtime.isolated = source_has_isolated_import(normalized_source.as_str());
    let generated_lean =
        compile_to_lean(normalized_source.as_str(), &mut runtime).unwrap_or_else(|error| {
            panic!(
                "failed to generate Lean from {}:\n{}",
                path_str,
                display_runtime_error_json(&runtime, &error, false)
            )
        });

    let output = render_tmp_translation(source_path, lit_source, &generated_lean);
    write_scratch_command_output(&output);
}

#[test]
fn tmp0_to_lean() {
    run_with_large_stack("tmp0_to_lean_large_stack", compile_tmp_to_lean);
}

fn example_lit_path(relative_path: &str) -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = manifest_dir.join("examples").join(relative_path);
    assert!(path.is_file(), "examples/{} must exist", relative_path);
    path
}

fn source_without_trailing_triple_quoted_block(source: &str) -> &str {
    let trimmed_source = source.trim_end();
    let Some(before_closing_delimiter) = trimmed_source.strip_suffix("\"\"\"") else {
        return source;
    };
    let closing_delimiter_start = before_closing_delimiter.len();
    if closing_delimiter_start > 0
        && trimmed_source.as_bytes()[closing_delimiter_start - 1] != b'\n'
    {
        return source;
    }

    let mut search_end = before_closing_delimiter.len();
    while let Some(opening_delimiter_start) = before_closing_delimiter[..search_end].rfind("\"\"\"")
    {
        let starts_line = opening_delimiter_start == 0
            || before_closing_delimiter.as_bytes()[opening_delimiter_start - 1] == b'\n';
        let after_opening_delimiter = &before_closing_delimiter[opening_delimiter_start + 3..];
        let ends_line = after_opening_delimiter.starts_with('\n')
            || after_opening_delimiter.starts_with("\r\n");
        if starts_line && ends_line {
            return &source[..opening_delimiter_start];
        }
        search_end = opening_delimiter_start;
    }

    source
}

fn render_tmp_translation(source_path: &str, litex_source: &str, generated_lean: &str) -> String {
    format!(
        "\n==================== LITEX -> LEAN ====================\n\
         source: {source_path}\n\
         \n\
         ----- LITEX SOURCE -----------------------------------\n\
         {}\n\
         \n\
         ----- GENERATED LEAN ---------------------------------\n\
         {}\n\
         ========================= END =========================\n",
        litex_source.trim(),
        generated_lean.trim()
    )
}

fn write_scratch_command_output(output: &str) {
    // `tmp0_to_lean` is a display command. Write directly so plain `cargo test`
    // shows the mapping without requiring the libtest `--nocapture` flag.
    let mut stdout = std::io::stdout().lock();
    stdout
        .write_all(output.as_bytes())
        .expect("write Litex-to-Lean scratch output");
    stdout.flush().expect("flush Litex-to-Lean scratch output");
}
