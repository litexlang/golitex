use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{print_slowest_run_labels, run_with_large_stack};

// Local workflow helper: run math500 temporary snippets without touching golitex/examples.
//
// This test is intentionally non-failing when the sibling repo doesn't exist, so CI won't care.
// It is meant for local iteration while authoring snippets under ../MATH-500-litex/tmp/.
#[test]
fn run_math500_tmp() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let local_tmp_path = manifest_dir.join("tmp").join("math500_work.lit");
    let sibling_tmp_path = match manifest_dir.parent() {
        Some(parent) => parent
            .join("MATH-500-litex")
            .join("tmp")
            .join("math500_work.lit"),
        None => PathBuf::new(),
    };

    let math500_tmp_path = if local_tmp_path.is_file() {
        local_tmp_path
    } else if sibling_tmp_path.is_file() {
        sibling_tmp_path
    } else {
        println!("--- run_math500_tmp: skip (missing file) ---");
        println!("  checked: {}", local_tmp_path.display());
        if !sibling_tmp_path.as_os_str().is_empty() {
            println!("  checked: {}", sibling_tmp_path.display());
        }
        return;
    };
    println!(
        "--- run_math500_tmp: using {} ---",
        math500_tmp_path.display()
    );

    let source_code = match fs::read_to_string(&math500_tmp_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", math500_tmp_path, read_error),
    };

    #[derive(Clone)]
    struct Snippet {
        label: String,
        source: String,
    }

    // Split by "# test/..." markers so we can clear env between problems, while keeping one
    // Runtime alive (like run_examples does).
    let mut snippets: Vec<Snippet> = Vec::new();
    let mut current_lines: Vec<String> = Vec::new();
    let mut current_label: Option<String> = None;

    for line in source_code.lines() {
        if line.starts_with("# test/") {
            if let Some(label) = current_label.take() {
                let body = current_lines.join("\n");
                if !body.trim().is_empty() {
                    snippets.push(Snippet {
                        label,
                        source: body,
                    });
                }
            }
            current_lines.clear();
            current_label = Some(line.trim().to_string());
        }
        if current_label.is_some() {
            current_lines.push(line.to_string());
        }
    }
    if let Some(label) = current_label.take() {
        let body = current_lines.join("\n");
        if !body.trim().is_empty() {
            snippets.push(Snippet {
                label,
                source: body,
            });
        }
    }
    if snippets.is_empty() {
        // Fallback: run whole file as one snippet.
        snippets.push(Snippet {
            label: "math500_work.lit (whole file)".to_string(),
            source: source_code,
        });
    }

    let path_for_runtime = match math500_tmp_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", math500_tmp_path),
    };

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(path_for_runtime);

    let mut durations_ms: Vec<(String, f64)> = Vec::new();
    for (snippet_index, snippet) in snippets.iter().enumerate() {
        if snippet_index > 0 {
            runtime.clear_current_env_and_parse_name_scope();
            runtime.set_current_user_lit_file_path(path_for_runtime);
        }

        let normalized_source = remove_windows_carriage_return(snippet.source.as_str());
        let start_time = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        durations_ms.push((snippet.label.clone(), duration_ms));

        if !run_succeeded {
            print_slowest_run_labels("math500 snippets before failure", durations_ms.as_slice());
            panic!(
                "math500 snippet FAILED:\n{}\n>>> FAILED snippet: {}\n",
                run_output, snippet.label
            );
        }
    }

    print_slowest_run_labels("math500 snippets", durations_ms.as_slice());
    for (label, duration_ms) in durations_ms.iter() {
        println!("  OK  {:.2} ms  {}", duration_ms, label);
    }
}

#[test]
fn run_math500_litex_simple() {
    run_with_large_stack(
        "run_math500_litex_simple_large_stack",
        run_math500_litex_simple_impl,
    );
}

#[test]
fn run_math500_litex_all() {
    run_with_large_stack(
        "run_math500_litex_all_large_stack",
        run_math500_litex_all_impl,
    );
}

fn run_math500_litex_simple_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let completed_dir = manifest_dir.join("MATH-500-litex").join("litex_file");
    let completed_dir = if completed_dir.is_dir() {
        completed_dir
    } else {
        manifest_dir
            .join("scripts")
            .join("MATH-500-litex")
            .join("litex_file")
    };
    assert!(
        completed_dir.is_dir(),
        "MATH-500-litex/litex_file must exist at {:?}",
        completed_dir
    );
    run_math500_litex_lit_dir(&completed_dir);
}

fn run_math500_litex_all_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let lit_dir = manifest_dir
        .join("MATH-500-litex")
        .join("unfinished_litex_file");
    let lit_dir = if lit_dir.is_dir() {
        lit_dir
    } else {
        manifest_dir
            .join("scripts")
            .join("MATH-500-litex")
            .join("unfinished_litex_file")
    };
    assert!(
        lit_dir.is_dir(),
        "MATH-500-litex/unfinished_litex_file must exist at {:?}",
        lit_dir
    );
    run_math500_litex_lit_dir(&lit_dir);
}

fn run_math500_litex_lit_dir(base_dir: &Path) {
    fn collect_lit_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let read_directory = fs::read_dir(dir)
            .unwrap_or_else(|read_error| panic!("failed to read {:?}: {}", dir, read_error));
        for directory_entry_result in read_directory {
            let directory_entry = directory_entry_result.unwrap_or_else(|read_error| {
                panic!("failed to read directory entry: {}", read_error)
            });
            let path = directory_entry.path();
            let file_type = directory_entry
                .file_type()
                .unwrap_or_else(|file_type_error| {
                    panic!(
                        "failed to read file type for {:?}: {}",
                        path, file_type_error
                    )
                });
            if file_type.is_dir() {
                collect_lit_files(path.as_path(), out);
            } else if path.extension().is_some_and(|ext| ext == "lit") {
                out.push(path);
            }
        }
    }

    let mut lit_paths: Vec<PathBuf> = Vec::new();
    collect_lit_files(base_dir, &mut lit_paths);
    lit_paths.sort();

    if lit_paths.is_empty() {
        println!(
            "--- math500-litex simple: no .lit files under {:?}; skip ---",
            base_dir
        );
        return;
    }

    let base_dir_str = base_dir.to_string_lossy().to_string();

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
    runtime.new_file_path_new_env_new_name_scope(base_dir_str.as_str());

    let run_wall_start = Instant::now();
    let mut total_count: usize = 0;
    let mut failed_labels: Vec<String> = Vec::new();
    let mut total_solution_duration_ms: f64 = 0.0;

    for lit_path in lit_paths.iter() {
        if total_count > 0 {
            runtime.clear_current_env_and_parse_name_scope();
        }

        let lit_path_str = lit_path.to_string_lossy().to_string();
        runtime.set_current_user_lit_file_path(lit_path_str.as_str());

        let relative_label = match lit_path.strip_prefix(base_dir) {
            Ok(relative_path) => relative_path.to_string_lossy().to_string(),
            Err(_) => lit_path_str.clone(),
        };

        let litex_code = fs::read_to_string(lit_path)
            .unwrap_or_else(|read_error| panic!("failed to read {:?}: {}", lit_path, read_error));
        let litex_code = litex_code.trim();
        if litex_code.is_empty() {
            println!("--- [SKIP] empty .lit file: {} ---", relative_label);
            continue;
        }

        let normalized_source = remove_windows_carriage_return(litex_code);

        let start_time_for_one_solution = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;
        total_solution_duration_ms += duration_ms;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        total_count += 1;
        if !run_succeeded {
            let label = relative_label.clone();
            println!(
                "=== [FAILED] math500-litex simple at .lit file {} ({:.2} ms) ===\n{}\n",
                relative_label, duration_ms, run_output
            );
            failed_labels.push(label);
        }
    }

    let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
    println!("--- math500-litex simple timing (summary) ---");
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    println!(
        "  snippets: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
        total_count, total_solution_duration_ms, run_wall_ms
    );

    if failed_labels.is_empty() {
        println!("--- math500-litex simple: all snippets OK ---");
        return;
    }

    println!("--- math500-litex simple failed unique_id ---");
    for label in failed_labels.iter() {
        println!("{}", label);
    }
    panic!(
        "math500-litex simple failed for {} of {} item(s)",
        failed_labels.len(),
        total_count
    );
}
