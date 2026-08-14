use std::fs;
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

fn compile_example_lit_file_to_lean(relative_path: &str) -> Option<String> {
    run_example_lit_file(relative_path);

    let lit_path = example_lit_path(relative_path);
    let lit_content = match fs::read_to_string(&lit_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", lit_path, read_error),
    };
    if lit_content.trim().is_empty() {
        return None;
    }

    let path_str = match lit_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", lit_path),
    };
    let normalized_source = remove_windows_carriage_return(lit_content.as_str());
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
    let updated_source = source_with_generated_lean(&lit_content, &generated_lean);
    fs::write(&lit_path, updated_source)
        .unwrap_or_else(|write_error| panic!("failed to write {:?}: {}", lit_path, write_error));

    println!("generated Lean appended to {:?}", lit_path);
    Some(generated_lean)
}

#[test]
#[ignore]
fn print_tmp_lit_in_all_output_languages() {
    run_with_large_stack("print_tmp_lit_in_all_output_languages_large_stack", || {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let tmp_lit_path = manifest_dir.join("examples").join("tmp.lit");
        let tmp_lit_content = match fs::read_to_string(&tmp_lit_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", tmp_lit_path, read_error),
        };
        let path_str = match tmp_lit_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", tmp_lit_path),
        };
        let normalized_source = remove_windows_carriage_return(tmp_lit_content.as_str());
        let languages = vec![
            ("en", OutputLanguage::English),
            ("zh", OutputLanguage::SimplifiedChinese),
            ("zh-Hans", OutputLanguage::TraditionalChinese),
            ("ja", OutputLanguage::Japanese),
            ("ko", OutputLanguage::Korean),
            ("es", OutputLanguage::Spanish),
            ("fr", OutputLanguage::French),
            ("de", OutputLanguage::German),
            ("pt", OutputLanguage::Portuguese),
            ("ru", OutputLanguage::Russian),
            ("ar", OutputLanguage::Arabic),
            ("hi", OutputLanguage::Hindi),
            ("vi", OutputLanguage::Vietnamese),
            ("id", OutputLanguage::Indonesian),
        ];

        for (language_code, output_language) in languages {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(path_str);
            runtime.output_language = output_language;

            let start_time = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), &mut runtime);
            let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            println!(
                "\n=== [lang={}] examples/tmp.lit {} ({:.2} ms user file only) ===\n{}\n",
                language_code,
                if run_succeeded { "OK" } else { "FAILED" },
                duration_ms,
                run_output
            );

            assert!(
                run_succeeded,
                "examples/tmp.lit failed for language `{}`",
                language_code
            );
        }
    });
}

#[test]
fn run_tmp0() {
    run_with_large_stack("run_tmp0_large_stack", || run_example_lit_file("tmp.lit"));
}

fn compile_tmp_to_lean(index: usize) {
    let relative_path = if index == 0 {
        "tmp.lit".to_string()
    } else {
        format!("tmp{}.lit", index)
    };
    let lit_path = example_lit_path(&relative_path);
    let lit_content = fs::read_to_string(&lit_path)
        .unwrap_or_else(|read_error| panic!("failed to read {:?}: {}", lit_path, read_error));
    let lit_source = source_without_trailing_triple_quoted_block(&lit_content).trim();
    if lit_source.is_empty() {
        println!(
            "\n=== LITEX -> LEAN: examples/{} is empty ===\n\
             Put Litex source in that file and rerun:\n  \
             cargo test --release tmp{}_to_lean -- --nocapture\n",
            relative_path, index
        );
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

    println!(
        "{}",
        render_tmp_translation(&relative_path, lit_source, &generated_lean)
    );
}

#[test]
fn tmp0_to_lean() {
    run_with_large_stack("tmp0_to_lean_large_stack", || compile_tmp_to_lean(0));
}

#[test]
#[ignore = "developer scratch command; run explicitly to print the source/target pair"]
fn compile_tmp1_to_lean() {
    run_with_large_stack("compile_tmp1_to_lean_large_stack", || {
        compile_tmp_to_lean(1)
    });
}

#[test]
#[ignore = "developer scratch command; run explicitly to print the source/target pair"]
fn compile_tmp2_to_lean() {
    run_with_large_stack("compile_tmp2_to_lean_large_stack", || {
        compile_tmp_to_lean(2)
    });
}

#[test]
fn compile_empty_to_lean() {
    run_with_large_stack("compile_empty_to_lean_large_stack", || {
        compile_example_lit_file_to_lean("_internal/compile_to_lean/empty.lit");
    });
}

#[test]
#[ignore = "developer snapshot command that rewrites the showcase source"]
fn compile_to_lean_showcase() {
    run_with_large_stack("compile_to_lean_showcase_large_stack", || {
        compile_example_lit_file_to_lean("_internal/compile_to_lean/showcase.lit");
    });
}

#[test]
fn wraps_generated_lean_at_end_of_tmp_source() {
    let source = "1 + 1 = 2\n\n\n\"\"\"\nold generated Lean\n\"\"\"\n";
    let updated_source = source_with_generated_lean(source, "import Mathlib\n");

    assert_eq!(
        updated_source,
        "1 + 1 = 2\n\n\n\"\"\"\nimport Mathlib\n\"\"\"\n"
    );
}

#[test]
fn keeps_nontrailing_triple_quoted_blocks() {
    let source = "\"\"\"\nsource note\n\"\"\"\n\n1 + 1 = 2\n";
    let updated_source = source_with_generated_lean(source, "import Mathlib\n");

    assert!(updated_source.starts_with("\"\"\"\nsource note\n\"\"\"\n"));
    assert!(updated_source.ends_with("\"\"\"\nimport Mathlib\n\"\"\"\n"));
}

#[test]
fn renders_tmp_translation_as_one_clean_source_target_pair() {
    let output = render_tmp_translation(
        "tmp.lit",
        "1 + 1 = 2",
        "theorem fact_0 : 1 + 1 = 2 := by\n  norm_num\n",
    );

    assert_eq!(output.matches("----- LITEX SOURCE").count(), 1);
    assert_eq!(output.matches("----- GENERATED LEAN").count(), 1);
    assert!(output.contains("source: examples/tmp.lit"));
    assert!(output.contains("1 + 1 = 2"));
    assert!(output.contains("theorem fact_0"));
    assert!(!output.contains("generated Lean appended"));
    assert!(!output.contains("generated Lean replaced"));
}

#[test]
fn run_comparison_rules_draft() {
    run_with_large_stack("run_comparison_rules_draft_large_stack", || {
        run_example_lit_file("_internal/drafts/comparison_rules_draft.lit")
    });
}

#[test]
fn run_statement_forms_draft() {
    run_with_large_stack("run_statement_forms_draft_large_stack", || {
        run_example_lit_file("_internal/drafts/statement_forms_draft.lit")
    });
}

#[test]
fn run_output_trace_showcase() {
    run_with_large_stack("run_output_trace_showcase_large_stack", || {
        run_example_lit_file("_internal/drafts/output_trace_showcase.lit")
    });
}

fn example_lit_path(relative_path: &str) -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = manifest_dir.join("examples").join(relative_path);
    assert!(path.is_file(), "examples/{} must exist", relative_path);
    path
}

fn source_with_generated_lean(source: &str, generated_lean: &str) -> String {
    let source = source_without_trailing_triple_quoted_block(source);
    format!(
        "{}\n\n\n\"\"\"\n{}\n\"\"\"\n",
        source.trim_end(),
        generated_lean.trim_end()
    )
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

fn render_tmp_translation(relative_path: &str, litex_source: &str, generated_lean: &str) -> String {
    format!(
        "\n==================== LITEX -> LEAN ====================\n\
         source: examples/{relative_path}\n\
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
