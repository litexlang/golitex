use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;
use crate::to_lean::to_lean;

use super::helper::{run_with_large_stack, source_has_isolated_import, SKETCH_EXAMPLES_SUBDIR};

fn run_tmp_lit_file(file_name: &str) {
    let tmp_lit_path = tmp_lit_path(file_name);

    let tmp_lit_content = match fs::read_to_string(&tmp_lit_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", tmp_lit_path, read_error),
    };
    if tmp_lit_content.trim().is_empty() {
        println!("examples/{} is empty; skip run", file_name);
        return;
    }

    let path_str = match tmp_lit_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", tmp_lit_path),
    };

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(path_str);
    let normalized_source = remove_windows_carriage_return(tmp_lit_content.as_str());
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
        file_name, error_json, path_str, status_label, duration_ms
    );
}

fn run_tmp_lit_file_to_lean(file_name: &str) {
    run_tmp_lit_file(file_name);

    let tmp_lit_path = tmp_lit_path(file_name);
    let tmp_lit_content = match fs::read_to_string(&tmp_lit_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", tmp_lit_path, read_error),
    };
    if tmp_lit_content.trim().is_empty() {
        return;
    }

    let path_str = match tmp_lit_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", tmp_lit_path),
    };
    let normalized_source = remove_windows_carriage_return(tmp_lit_content.as_str());
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(path_str);
    runtime.isolated = source_has_isolated_import(normalized_source.as_str());

    let generated_lean =
        to_lean(normalized_source.as_str(), &mut runtime).unwrap_or_else(|error| {
            panic!(
                "failed to generate Lean from {}:\n{}",
                path_str,
                display_runtime_error_json(&runtime, &error, false)
            )
        });
    let updated_source = source_with_generated_lean(&tmp_lit_content, &generated_lean);
    fs::write(&tmp_lit_path, updated_source).unwrap_or_else(|write_error| {
        panic!("failed to write {:?}: {}", tmp_lit_path, write_error)
    });

    println!("generated Lean appended to {:?}", tmp_lit_path);
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
    run_with_large_stack("run_tmp0_large_stack", || run_tmp_lit_file("tmp.lit"));
}

#[test]
fn run_tmp0_to_lean() {
    run_with_large_stack("run_tmp0_to_lean_large_stack", || {
        run_tmp_lit_file_to_lean("tmp.lit")
    });
}

#[test]
fn wraps_generated_lean_at_end_of_tmp_source() {
    let updated_source = source_with_generated_lean("1 + 1 = 2\n", "import Mathlib\n");

    assert_eq!(
        updated_source,
        "1 + 1 = 2\n\n\n\"\"\"\nimport Mathlib\n\"\"\"\n"
    );
}

#[test]
fn run_tmp2() {
    run_with_large_stack("run_tmp2_large_stack", || run_tmp_lit_file("tmp2.lit"));
}

#[test]
fn run_tmp3() {
    run_with_large_stack("run_tmp3_large_stack", || run_tmp_lit_file("tmp3.lit"));
}

#[test]
fn run_tmp4() {
    run_with_large_stack("run_tmp4_large_stack", || run_tmp_lit_file("tmp4.lit"));
}

fn tmp_lit_path(file_name: &str) -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate_paths = [
        manifest_dir.join("examples").join(file_name),
        manifest_dir.join(SKETCH_EXAMPLES_SUBDIR).join(file_name),
    ];
    candidate_paths
        .iter()
        .find(|path| path.is_file())
        .cloned()
        .unwrap_or_else(|| {
            panic!(
                "{} must exist in one of: {}",
                file_name,
                candidate_paths
                    .iter()
                    .map(|path| {
                        path.strip_prefix(&manifest_dir)
                            .unwrap_or(path)
                            .display()
                            .to_string()
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
}

fn source_with_generated_lean(source: &str, generated_lean: &str) -> String {
    format!(
        "{}\n\n\n\"\"\"\n{}\n\"\"\"\n",
        source.trim_end(),
        generated_lean.trim_end()
    )
}
