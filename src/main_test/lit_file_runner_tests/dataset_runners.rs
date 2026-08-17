use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{print_slowest_run_labels, run_with_large_stack, source_has_isolated_import};

#[test]
#[ignore = "large dataset gate; run explicitly with an exact filter and --ignored"]
fn run_gsm8k_solutions() {
    run_with_large_stack("run_gsm8k_solutions_large_stack", run_gsm8k_solutions_impl);
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
        assert!(
            jsonl_path.is_file(),
            "GSM8K-litex JSONL file must exist at {:?}",
            jsonl_path
        );
    }

    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;

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
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
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

#[test]
#[ignore = "large dataset gate; run explicitly with an exact filter and --ignored"]
fn run_metamathqa_litex_solutions() {
    run_with_large_stack(
        "run_metamathqa_litex_solutions_large_stack",
        run_metamathqa_litex_solutions_impl,
    );
}

#[test]
#[ignore = "large dataset gate; run explicitly with an exact filter and --ignored"]
fn run_minif2f_litex_finished() {
    run_with_large_stack(
        "run_minif2f_litex_finished_large_stack",
        run_minif2f_litex_finished_impl,
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

    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;
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
        runtime.isolated = source_has_isolated_import(normalized_source.as_str());
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
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
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

    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;

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
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
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
