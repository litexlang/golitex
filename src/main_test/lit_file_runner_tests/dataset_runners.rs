use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{print_slowest_run_labels, run_with_large_stack};

#[test]
fn run_gsm8k_solutions() {
    run_with_large_stack("run_gsm8k_solutions_large_stack", run_gsm8k_solutions_impl);
}

// cargo test run_gsm8k_debug_items -- --ignored --nocapture
// LITEX_GSM8K_TITLE=gsm8k_1 cargo test run_gsm8k_debug_items -- --ignored --nocapture
// LITEX_GSM8K_FILTER=wallet LITEX_GSM8K_LIMIT=5 cargo test run_gsm8k_debug_items -- --ignored --nocapture
// LITEX_GSM8K_SPLIT=test LITEX_GSM8K_LIMIT=20 cargo test run_gsm8k_debug_items -- --ignored --nocapture
// LITEX_GSM8K_DETAIL_OUTPUT=1 LITEX_GSM8K_TITLE=gsm8k_1 cargo test run_gsm8k_debug_items -- --ignored --nocapture
#[test]
#[ignore = "local debug helper; filters GSM8K items with env vars"]
fn run_gsm8k_debug_items() {
    run_with_large_stack(
        "run_gsm8k_debug_items_large_stack",
        run_gsm8k_debug_items_impl,
    );
}

fn run_gsm8k_debug_items_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_paths = vec![
        manifest_dir
            .join("scripts")
            .join("gsm8k-litex")
            .join("train.jsonl"),
        manifest_dir
            .join("scripts")
            .join("gsm8k-litex")
            .join("test.jsonl"),
    ];
    run_jsonl_debug_items(
        "gsm8k",
        jsonl_paths.as_slice(),
        "LITEX_GSM8K",
        true,
        Some("train|test|all"),
    );
}

fn run_gsm8k_solutions_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_paths = vec![
        manifest_dir
            .join("scripts")
            .join("gsm8k-litex")
            .join("train.jsonl"),
        manifest_dir
            .join("scripts")
            .join("gsm8k-litex")
            .join("test.jsonl"),
    ];

    for jsonl_path in jsonl_paths.iter() {
        if !jsonl_path.is_file() {
            println!(
                "--- gsm8k jsonl file missing at {:?}; skip gsm8k solutions ---",
                jsonl_path
            );
            return;
        }
    }

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;

    let run_wall_start = Instant::now();
    let mut total_count: usize = 0;
    let mut failed_labels: Vec<String> = Vec::new();
    let mut total_solution_duration_ms: f64 = 0.0;

    for jsonl_path in jsonl_paths.iter() {
        run_gsm8k_jsonl_file(
            jsonl_path,
            &mut runtime,
            &mut total_count,
            &mut failed_labels,
            &mut total_solution_duration_ms,
        );
    }

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    println!("--- gsm8k timing (summary) ---");
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  solutions: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        total_count, total_solution_duration_ms, run_wall_ms
    );

    if failed_labels.is_empty() {
        println!("--- gsm8k: all train/test solutions OK ---");
        return;
    }

    println!("--- gsm8k failed titles ---");
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "gsm8k solution run failed for {} of {} item(s)",
        failed_labels.len(),
        total_count
    );
}

fn run_gsm8k_jsonl_file(
    jsonl_path: &Path,
    runtime: &mut Runtime,
    total_count: &mut usize,
    failed_labels: &mut Vec<String>,
    total_solution_duration_ms: &mut f64,
) {
    let jsonl_path_str = match jsonl_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => panic!("{:?} must be valid UTF-8", jsonl_path),
    };

    let jsonl_content = match fs::read_to_string(&jsonl_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
    };

    if *total_count == 0 {
        runtime.new_file_path_new_env_new_name_scope(jsonl_path_str.as_str());
    } else {
        runtime.reset_for_isolated_runner_item();
        runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
    }

    for (line_index, line) in jsonl_content.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }

        if *total_count > 0 || line_index > 0 {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
        }

        let title = jsonl_string_field(line, "title").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse title in {:?} line {}: {}",
                jsonl_path,
                line_index + 1,
                error_message
            )
        });
        let solution = jsonl_string_field(line, "solution").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse solution in {:?} line {} ({}): {}",
                jsonl_path,
                line_index + 1,
                title,
                error_message
            )
        });
        let normalized_source = remove_windows_carriage_return(solution.as_str());

        let start_time_for_one_solution = Instant::now();
        let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), runtime);
        let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;
        *total_solution_duration_ms += duration_ms;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        *total_count += 1;
        if !run_succeeded {
            let label = format!(
                "{}:{}",
                jsonl_path
                    .file_name()
                    .and_then(|file_name| file_name.to_str())
                    .unwrap_or("gsm8k jsonl"),
                title
            );
            println!(
                "=== [FAILED] {} at jsonl line {} ({:.2} ms) ===\n{}\n",
                label,
                line_index + 1,
                duration_ms,
                run_output
            );
            failed_labels.push(label);
        }

        if *total_count % 1000 == 0 {
            println!(
                "--- gsm8k progress: {} solution(s), {} failure(s) ---",
                total_count,
                failed_labels.len()
            );
        }
    }
}

// cargo test run_metamathqa_debug_items -- --ignored --nocapture
// LITEX_METAMATHQA_TITLE=MetaMathQA-GSM_FOBAR-350228 cargo test run_metamathqa_debug_items -- --ignored --nocapture
// LITEX_METAMATHQA_FILTER=paint LITEX_METAMATHQA_LIMIT=5 cargo test run_metamathqa_debug_items -- --ignored --nocapture
#[test]
#[ignore = "local debug helper; filters MetaMathQA items with env vars"]
fn run_metamathqa_debug_items() {
    run_with_large_stack(
        "run_metamathqa_debug_items_large_stack",
        run_metamathqa_debug_items_impl,
    );
}

fn run_metamathqa_debug_items_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_paths = vec![manifest_dir
        .join("scripts")
        .join("MetaMathQA-litex")
        .join("MetaMathQA.jsonl")];
    run_jsonl_debug_items(
        "metamathqa",
        jsonl_paths.as_slice(),
        "LITEX_METAMATHQA",
        false,
        None,
    );
}

#[test]
fn run_math23k_solutions() {
    run_with_large_stack(
        "run_math23k_solutions_large_stack",
        run_math23k_solutions_impl,
    );
}

fn run_math23k_solutions_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_path = manifest_dir
        .join("scripts")
        .join("math23k-litex")
        .join("math23k.jsonl");
    assert!(
        jsonl_path.is_file(),
        "math23k-litex jsonl file must exist at {:?}",
        jsonl_path
    );

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;

    let run_wall_start = Instant::now();
    let mut total_count: usize = 0;
    let mut failed_labels: Vec<String> = Vec::new();
    let mut total_solution_duration_ms: f64 = 0.0;

    run_labeled_jsonl_solution_file(
        "math23k-litex",
        &jsonl_path,
        &mut runtime,
        &mut total_count,
        &mut failed_labels,
        &mut total_solution_duration_ms,
    );

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    println!("--- math23k-litex timing (summary) ---");
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  solutions: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        total_count, total_solution_duration_ms, run_wall_ms
    );

    if failed_labels.is_empty() {
        println!("--- math23k-litex: all solutions OK ---");
        return;
    }

    println!("--- math23k-litex failed titles ---");
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "math23k-litex solution run failed for {} of {} item(s)",
        failed_labels.len(),
        total_count
    );
}

// cargo test run_math23k_debug_items -- --ignored --nocapture
// LITEX_MATH23K_TITLE=Math23k_15120 cargo test run_math23k_debug_items -- --ignored --nocapture
// LITEX_MATH23K_FILTER=camera LITEX_MATH23K_LIMIT=5 cargo test run_math23k_debug_items -- --ignored --nocapture
#[test]
#[ignore = "local debug helper; filters Math23K items with env vars"]
fn run_math23k_debug_items() {
    run_with_large_stack(
        "run_math23k_debug_items_large_stack",
        run_math23k_debug_items_impl,
    );
}

fn run_math23k_debug_items_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_paths = vec![manifest_dir
        .join("scripts")
        .join("math23k-litex")
        .join("math23k.jsonl")];
    run_jsonl_debug_items(
        "math23k",
        jsonl_paths.as_slice(),
        "LITEX_MATH23K",
        false,
        None,
    );
}

#[test]
fn run_metamathqa_litex_solutions() {
    run_with_large_stack(
        "run_metamathqa_litex_solutions_large_stack",
        run_metamathqa_litex_solutions_impl,
    );
}

#[test]
fn run_minif2f_litex_finished() {
    run_with_large_stack(
        "run_minif2f_litex_finished_large_stack",
        run_minif2f_litex_finished_impl,
    );
}

#[test]
fn run_math500_litex_finished() {
    run_with_large_stack(
        "run_math500_litex_finished_large_stack",
        run_math500_litex_finished_impl,
    );
}

fn run_minif2f_litex_finished_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_path = manifest_dir
        .join("scripts")
        .join("litex-minif2f")
        .join("litex_dataset")
        .join("finished.jsonl");
    run_finished_litex_jsonl_dataset("MiniF2F-litex finished", &jsonl_path, "name");
}

fn run_math500_litex_finished_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_path = manifest_dir
        .join("scripts")
        .join("MATH-500-litex")
        .join("litex_dataset")
        .join("test-litex.jsonl");
    run_finished_litex_jsonl_dataset("MATH-500-litex finished", &jsonl_path, "unique_id");
}

fn run_finished_litex_jsonl_dataset(dataset_label: &str, jsonl_path: &Path, label_field: &str) {
    assert!(
        jsonl_path.is_file(),
        "{} JSONL file must exist at {:?}",
        dataset_label,
        jsonl_path
    );

    let jsonl_path_str = match jsonl_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => panic!("{:?} must be valid UTF-8", jsonl_path),
    };
    let jsonl_content = match fs::read_to_string(jsonl_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
    };

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
    runtime.new_file_path_new_env_new_name_scope(jsonl_path_str.as_str());

    let run_wall_start = Instant::now();
    let mut total_count: usize = 0;
    let mut failed_labels: Vec<String> = Vec::new();
    let mut durations_ms: Vec<(String, f64)> = Vec::new();

    for (line_index, line) in jsonl_content.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        if total_count > 0 {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
        }

        let item_label = jsonl_string_field(line, label_field).unwrap_or_else(|error_message| {
            panic!(
                "failed to parse {} in {:?} line {}: {}",
                label_field,
                jsonl_path,
                line_index + 1,
                error_message
            )
        });
        let litex_code = jsonl_string_field(line, "litex_code").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse litex_code in {:?} line {} ({}): {}",
                jsonl_path,
                line_index + 1,
                item_label,
                error_message
            )
        });

        let normalized_source = remove_windows_carriage_return(litex_code.as_str());
        let start_time_for_one_solution = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        total_count += 1;
        durations_ms.push((item_label.clone(), duration_ms));
        if !run_succeeded {
            let label = format!("{}:{}", line_index + 1, item_label);
            println!(
                "=== [FAILED] {} at jsonl line {} ({:.2} ms): {} ===\n{}\n",
                dataset_label,
                line_index + 1,
                duration_ms,
                item_label,
                run_output
            );
            failed_labels.push(label);
        }

        if total_count % 100 == 0 {
            println!(
                "--- {} progress: {} snippet(s), {} failure(s) ---",
                dataset_label,
                total_count,
                failed_labels.len()
            );
        }
    }

    assert!(
        total_count > 0,
        "{} JSONL file must contain at least one non-empty row at {:?}",
        dataset_label,
        jsonl_path
    );

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    let total_duration_ms: f64 = durations_ms
        .iter()
        .map(|(_, duration_ms)| *duration_ms)
        .sum();
    println!("--- {} timing (summary) ---", dataset_label);
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  finished snippets: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        total_count, total_duration_ms, run_wall_ms
    );
    print_slowest_run_labels(
        format!("{} snippets", dataset_label).as_str(),
        durations_ms.as_slice(),
    );

    if failed_labels.is_empty() {
        println!("--- {}: all finished snippets OK ---", dataset_label);
        return;
    }

    println!("--- {} failed labels ---", dataset_label);
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "{} snippet run failed for {} of {} item(s)",
        dataset_label,
        failed_labels.len(),
        total_count
    );
}

fn run_metamathqa_litex_solutions_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let jsonl_path = manifest_dir
        .join("scripts")
        .join("MetaMathQA-litex")
        .join("MetaMathQA.jsonl");
    assert!(
        jsonl_path.is_file(),
        "MetaMathQA-litex jsonl file must exist at {:?}",
        jsonl_path
    );

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;

    let run_wall_start = Instant::now();
    let mut total_count: usize = 0;
    let mut failed_labels: Vec<String> = Vec::new();
    let mut total_solution_duration_ms: f64 = 0.0;

    run_metamathqa_jsonl_file(
        &jsonl_path,
        &mut runtime,
        &mut total_count,
        &mut failed_labels,
        &mut total_solution_duration_ms,
    );

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    println!("--- MetaMathQA-litex timing (summary) ---");
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  solutions: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        total_count, total_solution_duration_ms, run_wall_ms
    );

    if failed_labels.is_empty() {
        println!("--- MetaMathQA-litex: all solutions OK ---");
        return;
    }

    println!("--- MetaMathQA-litex failed titles ---");
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "MetaMathQA-litex solution run failed for {} of {} item(s)",
        failed_labels.len(),
        total_count
    );
}

fn run_metamathqa_jsonl_file(
    jsonl_path: &Path,
    runtime: &mut Runtime,
    total_count: &mut usize,
    failed_labels: &mut Vec<String>,
    total_solution_duration_ms: &mut f64,
) {
    let jsonl_path_str = match jsonl_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => panic!("{:?} must be valid UTF-8", jsonl_path),
    };

    let jsonl_content = match fs::read_to_string(jsonl_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
    };

    runtime.new_file_path_new_env_new_name_scope(jsonl_path_str.as_str());

    for (line_index, line) in jsonl_content.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }

        if line_index > 0 {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
        }

        let title = jsonl_string_field(line, "title").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse title in {:?} line {}: {}",
                jsonl_path,
                line_index + 1,
                error_message
            )
        });
        let solution = jsonl_string_field(line, "solution").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse solution in {:?} line {} ({}): {}",
                jsonl_path,
                line_index + 1,
                title,
                error_message
            )
        });
        let normalized_source = remove_windows_carriage_return(solution.as_str());

        let start_time_for_one_solution = Instant::now();
        let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), runtime);
        let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;
        *total_solution_duration_ms += duration_ms;

        let (run_succeeded, run_output) =
            render_run_source_code_output(runtime, &stmt_results, &runtime_error, false);

        *total_count += 1;
        if !run_succeeded {
            let label = format!("{}:{}", line_index + 1, title);
            println!(
                "=== [FAILED] MetaMathQA-litex at jsonl line {} ({:.2} ms): {} ===\n{}\n",
                line_index + 1,
                duration_ms,
                title,
                run_output
            );
            failed_labels.push(label);
        }

        if *total_count % 100 == 0 {
            println!(
                "--- MetaMathQA-litex progress: {} solution(s), {} failure(s) ---",
                total_count,
                failed_labels.len()
            );
        }
    }
}

#[derive(Clone)]
struct JsonlDebugItem {
    label: String,
    title: String,
    source: String,
    path_for_runtime: String,
}

fn run_jsonl_debug_items(
    dataset_label: &str,
    jsonl_paths: &[PathBuf],
    env_prefix: &str,
    allow_split_filter: bool,
    split_hint: Option<&str>,
) {
    let split_key = format!("{}_SPLIT", env_prefix);
    let title_key = format!("{}_TITLE", env_prefix);
    let filter_key = format!("{}_FILTER", env_prefix);
    let limit_key = format!("{}_LIMIT", env_prefix);
    let stop_key = format!("{}_STOP_ON_FIRST_FAILURE", env_prefix);
    let detail_key = format!("{}_DETAIL_OUTPUT", env_prefix);

    let split_filter = if allow_split_filter {
        env_string(split_key.as_str())
            .unwrap_or_else(|| "all".to_string())
            .to_ascii_lowercase()
    } else {
        "all".to_string()
    };
    let title_filter = env_string(title_key.as_str());
    let text_filter = env_string(filter_key.as_str());
    let limit = env_usize(limit_key.as_str());
    let stop_on_first_failure = env_flag_is_set(stop_key.as_str());
    let detail_output = env_flag_is_set(detail_key.as_str());

    if title_filter.is_none() && text_filter.is_none() && limit.is_none() {
        println!("--- run_{}_debug_items: skip ---", dataset_label);
        println!("  Set one of:");
        println!("    {}=<exact title>", title_key);
        println!("    {}=<text substring>", filter_key);
        println!("    {}=5", limit_key);
        println!("  Optional:");
        if let Some(hint) = split_hint {
            println!("    {}={}", split_key, hint);
        }
        println!("    {}=1", detail_key);
        println!("    {}=1", stop_key);
        return;
    }

    let selected_paths =
        select_jsonl_paths_for_debug(jsonl_paths, split_filter.as_str(), allow_split_filter);

    if selected_paths.is_empty() {
        panic!(
            "{} must be one of train, test, all; got {:?}",
            split_key, split_filter
        );
    }

    for jsonl_path in selected_paths.iter() {
        if !jsonl_path.is_file() {
            println!(
                "--- {} jsonl file missing at {:?}; skip {} debug items ---",
                dataset_label, jsonl_path, dataset_label
            );
            return;
        }
    }

    let title_filter_lower = title_filter
        .as_ref()
        .map(|value| value.to_ascii_lowercase());
    let text_filter_lower = text_filter.as_ref().map(|value| value.to_ascii_lowercase());
    let mut items: Vec<JsonlDebugItem> = Vec::new();

    for jsonl_path in selected_paths.iter() {
        let jsonl_path_str = match jsonl_path.to_str() {
            Some(path_string) => path_string.to_string(),
            None => panic!("{:?} must be valid UTF-8", jsonl_path),
        };
        let split_label = jsonl_path
            .file_stem()
            .and_then(|file_stem| file_stem.to_str())
            .unwrap_or(dataset_label);
        let jsonl_content = match fs::read_to_string(jsonl_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
        };

        for (line_index, line) in jsonl_content.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }

            let title = jsonl_string_field(line, "title").unwrap_or_else(|error_message| {
                panic!(
                    "failed to parse title in {:?} line {}: {}",
                    jsonl_path,
                    line_index + 1,
                    error_message
                )
            });
            let description =
                jsonl_string_field(line, "description").unwrap_or_else(|error_message| {
                    panic!(
                        "failed to parse description in {:?} line {} ({}): {}",
                        jsonl_path,
                        line_index + 1,
                        title,
                        error_message
                    )
                });
            let solution = jsonl_string_field(line, "solution").unwrap_or_else(|error_message| {
                panic!(
                    "failed to parse solution in {:?} line {} ({}): {}",
                    jsonl_path,
                    line_index + 1,
                    title,
                    error_message
                )
            });

            if let Some(expected_title) = title_filter_lower.as_ref() {
                if title.to_ascii_lowercase() != *expected_title {
                    continue;
                }
            }
            if let Some(filter_text) = text_filter_lower.as_ref() {
                let haystack = format!("{}\n{}", title, description).to_ascii_lowercase();
                if !haystack.contains(filter_text.as_str()) {
                    continue;
                }
            }

            items.push(JsonlDebugItem {
                label: format!("{}:{} (line {})", split_label, title, line_index + 1),
                title,
                source: solution,
                path_for_runtime: jsonl_path_str.clone(),
            });

            if limit.is_some_and(|max_items| items.len() >= max_items) {
                break;
            }
        }

        if limit.is_some_and(|max_items| items.len() >= max_items) {
            break;
        }
    }

    if items.is_empty() {
        println!(
            "--- run_{}_debug_items: no matching items ---",
            dataset_label
        );
        if allow_split_filter {
            println!("  split: {}", split_filter);
        }
        if let Some(title) = title_filter {
            println!("  title: {}", title);
        }
        if let Some(filter_text) = text_filter {
            println!("  filter: {}", filter_text);
        }
        if let Some(max_items) = limit {
            println!("  limit: {}", max_items);
        }
        return;
    }

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
    runtime.new_file_path_new_env_new_name_scope(items[0].path_for_runtime.as_str());
    runtime.detail_output = detail_output;

    let run_wall_start = Instant::now();
    let mut durations_ms: Vec<(String, f64)> = Vec::new();
    let mut failed_labels: Vec<String> = Vec::new();

    for (item_index, item) in items.iter().enumerate() {
        if item_index > 0 {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
        }

        let normalized_source = remove_windows_carriage_return(item.source.as_str());
        let start_time = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        let status_label = if run_succeeded { "OK" } else { "FAILED" };

        println!(
            "=== [{}] {} ({:.2} ms) ===\n# {}\n{}\n",
            status_label, item.label, duration_ms, item.title, run_output
        );

        durations_ms.push((item.label.clone(), duration_ms));
        if !run_succeeded {
            failed_labels.push(item.label.clone());
            if stop_on_first_failure {
                break;
            }
        }
    }

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    println!("--- {} debug timing (summary) ---", dataset_label);
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  items: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        durations_ms.len(),
        durations_ms
            .iter()
            .map(|(_, duration_ms)| duration_ms)
            .sum::<f64>(),
        run_wall_ms
    );
    print_slowest_run_labels(
        format!("{} debug items", dataset_label).as_str(),
        durations_ms.as_slice(),
    );

    if failed_labels.is_empty() {
        println!("--- {} debug: all selected items OK ---", dataset_label);
        return;
    }

    println!("--- {} debug failed labels ---", dataset_label);
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "{} debug run failed for {} of {} item(s)",
        dataset_label,
        failed_labels.len(),
        durations_ms.len()
    );
}

fn select_jsonl_paths_for_debug(
    jsonl_paths: &[PathBuf],
    split_filter: &str,
    allow_split_filter: bool,
) -> Vec<PathBuf> {
    if !allow_split_filter || split_filter == "all" {
        return jsonl_paths.to_vec();
    }

    let mut selected_paths: Vec<PathBuf> = Vec::new();
    for jsonl_path in jsonl_paths.iter() {
        let Some(file_stem) = jsonl_path.file_stem().and_then(|name| name.to_str()) else {
            continue;
        };
        if file_stem.eq_ignore_ascii_case(split_filter) {
            selected_paths.push(jsonl_path.clone());
        }
    }
    selected_paths
}

fn run_labeled_jsonl_solution_file(
    dataset_label: &str,
    jsonl_path: &Path,
    runtime: &mut Runtime,
    total_count: &mut usize,
    failed_labels: &mut Vec<String>,
    total_solution_duration_ms: &mut f64,
) {
    let jsonl_path_str = match jsonl_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => panic!("{:?} must be valid UTF-8", jsonl_path),
    };

    let jsonl_content = match fs::read_to_string(jsonl_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
    };

    runtime.new_file_path_new_env_new_name_scope(jsonl_path_str.as_str());

    for (line_index, line) in jsonl_content.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }

        if line_index > 0 {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
        }

        let title = jsonl_string_field(line, "title").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse title in {:?} line {}: {}",
                jsonl_path,
                line_index + 1,
                error_message
            )
        });
        let solution = jsonl_string_field(line, "solution").unwrap_or_else(|error_message| {
            panic!(
                "failed to parse solution in {:?} line {} ({}): {}",
                jsonl_path,
                line_index + 1,
                title,
                error_message
            )
        });
        let normalized_source = remove_windows_carriage_return(solution.as_str());

        let start_time_for_one_solution = Instant::now();
        let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), runtime);
        let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;
        *total_solution_duration_ms += duration_ms;

        let (run_succeeded, run_output) =
            render_run_source_code_output(runtime, &stmt_results, &runtime_error, false);

        *total_count += 1;
        if !run_succeeded {
            let label = format!("{}:{}", line_index + 1, title);
            println!(
                "=== [FAILED] {} at jsonl line {} ({:.2} ms): {} ===\n{}\n",
                dataset_label,
                line_index + 1,
                duration_ms,
                title,
                run_output
            );
            failed_labels.push(label);
        }

        if *total_count % 100 == 0 {
            println!(
                "--- {} progress: {} solution(s), {} failure(s) ---",
                dataset_label,
                total_count,
                failed_labels.len()
            );
        }
    }
}

fn jsonl_string_field(line: &str, key: &str) -> Result<String, String> {
    let field_name = format!("\"{}\"", key);
    let field_start = line
        .find(field_name.as_str())
        .ok_or_else(|| format!("missing JSON field `{}`", key))?;
    let after_field_name = field_start + field_name.len();
    let colon_offset = line[after_field_name..]
        .find(':')
        .ok_or_else(|| format!("missing `:` after JSON field `{}`", key))?;
    let mut value_start = after_field_name + colon_offset + 1;
    while value_start < line.len() && line.as_bytes()[value_start].is_ascii_whitespace() {
        value_start += 1;
    }
    parse_json_string_at(line, value_start)
}

fn parse_json_string_at(line: &str, start_index: usize) -> Result<String, String> {
    if start_index >= line.len() || line.as_bytes()[start_index] != b'"' {
        return Err("JSON field value must be a string".to_string());
    }

    let mut result = String::new();
    let mut chars = line[start_index + 1..].chars();
    while let Some(ch) = chars.next() {
        if ch == '"' {
            return Ok(result);
        }
        if ch != '\\' {
            result.push(ch);
            continue;
        }

        let escaped = chars
            .next()
            .ok_or_else(|| "unfinished JSON escape".to_string())?;
        match escaped {
            '"' => result.push('"'),
            '\\' => result.push('\\'),
            '/' => result.push('/'),
            'b' => result.push('\u{0008}'),
            'f' => result.push('\u{000c}'),
            'n' => result.push('\n'),
            'r' => result.push('\r'),
            't' => result.push('\t'),
            'u' => {
                let mut hex = String::new();
                for _ in 0..4 {
                    hex.push(
                        chars
                            .next()
                            .ok_or_else(|| "unfinished JSON unicode escape".to_string())?,
                    );
                }
                let code = u32::from_str_radix(hex.as_str(), 16)
                    .map_err(|_| format!("invalid JSON unicode escape: {}", hex))?;
                let code =
                    if (0xD800..=0xDBFF).contains(&code) {
                        let backslash = chars
                            .next()
                            .ok_or_else(|| "unfinished JSON unicode surrogate pair".to_string())?;
                        let unicode_marker = chars
                            .next()
                            .ok_or_else(|| "unfinished JSON unicode surrogate pair".to_string())?;
                        if backslash != '\\' || unicode_marker != 'u' {
                            return Err(
                                "high JSON unicode surrogate must be followed by \\u".to_string()
                            );
                        }

                        let mut low_hex = String::new();
                        for _ in 0..4 {
                            low_hex.push(chars.next().ok_or_else(|| {
                                "unfinished JSON unicode low surrogate".to_string()
                            })?);
                        }
                        let low = u32::from_str_radix(low_hex.as_str(), 16)
                            .map_err(|_| format!("invalid JSON unicode escape: {}", low_hex))?;
                        if !(0xDC00..=0xDFFF).contains(&low) {
                            return Err(format!(
                                "high JSON unicode surrogate {} followed by non-low surrogate {}",
                                hex, low_hex
                            ));
                        }
                        0x10000 + ((code - 0xD800) << 10) + (low - 0xDC00)
                    } else if (0xDC00..=0xDFFF).contains(&code) {
                        return Err(format!("unexpected JSON unicode low surrogate: {}", hex));
                    } else {
                        code
                    };
                let decoded = char::from_u32(code)
                    .ok_or_else(|| format!("invalid JSON unicode code point: {}", hex))?;
                result.push(decoded);
            }
            other => return Err(format!("unknown JSON escape: \\{}", other)),
        }
    }

    Err("unterminated JSON string".to_string())
}

fn env_flag_is_set(name: &str) -> bool {
    match std::env::var(name) {
        Ok(value) => {
            let normalized = value.trim().to_ascii_lowercase();
            !normalized.is_empty() && normalized != "0" && normalized != "false"
        }
        Err(_) => false,
    }
}

fn env_string(name: &str) -> Option<String> {
    match std::env::var(name) {
        Ok(value) => {
            let trimmed = value.trim();
            if trimmed.is_empty() {
                None
            } else {
                Some(trimmed.to_string())
            }
        }
        Err(_) => None,
    }
}

fn env_usize(name: &str) -> Option<usize> {
    let value = env_string(name)?;
    match value.parse::<usize>() {
        Ok(parsed) => Some(parsed),
        Err(parse_error) => {
            panic!(
                "{} must be a positive integer, got {:?}: {}",
                name, value, parse_error
            )
        }
    }
}
