use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{
    collect_markdown_files_under_dir_sorted, litex_snippets_from_markdown_files,
    run_single_the_mechanics_chapter_markdown_file_impl, run_with_large_stack, the_mechanics_dir,
    THE_MECHANICS_SUBDIR,
};

#[test]
fn run_the_mechanics_markdown_files() {
    run_with_large_stack(
        "run_the_mechanics_markdown_files_large_stack",
        run_the_mechanics_markdown_files_impl,
    );
}

#[test]
fn run_the_mechanics_chapter_1_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_1_markdown_file_large_stack",
        run_the_mechanics_chapter_1_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_1_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl(
        "Chapter_1_Proofs_By_Calculation.md",
        "Chapter 1",
    );
}

#[test]
fn run_the_mechanics_chapter_2_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_2_markdown_file_large_stack",
        run_the_mechanics_chapter_2_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_2_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl(
        "Chapter_2_Proofs_With_Structure.md",
        "Chapter 2",
    );
}

#[test]
fn run_the_mechanics_chapter_3_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_3_markdown_file_large_stack",
        run_the_mechanics_chapter_3_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_3_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl(
        "Chapter_3_Parity_And_Divisibility.md",
        "Chapter 3",
    );
}

#[test]
fn run_the_mechanics_chapter_4_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_4_markdown_file_large_stack",
        run_the_mechanics_chapter_4_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_4_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl(
        "Chapter_4_Proofs_With_Structure_II.md",
        "Chapter 4",
    );
}

#[test]
fn run_the_mechanics_chapter_5_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_5_markdown_file_large_stack",
        run_the_mechanics_chapter_5_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_5_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_5_Logic.md", "Chapter 5");
}

#[test]
fn run_the_mechanics_chapter_6_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_6_markdown_file_large_stack",
        run_the_mechanics_chapter_6_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_6_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_6_Induction.md", "Chapter 6");
}

#[test]
fn run_the_mechanics_chapter_7_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_7_markdown_file_large_stack",
        run_the_mechanics_chapter_7_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_7_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_7_Number_Theory.md", "Chapter 7");
}

#[test]
fn run_the_mechanics_chapter_8_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_8_markdown_file_large_stack",
        run_the_mechanics_chapter_8_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_8_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_8_Functions.md", "Chapter 8");
}

#[test]
fn run_the_mechanics_chapter_9_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_9_markdown_file_large_stack",
        run_the_mechanics_chapter_9_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_9_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_9_Sets.md", "Chapter 9");
}

#[test]
fn run_the_mechanics_chapter_10_markdown_file() {
    run_with_large_stack(
        "run_the_mechanics_chapter_10_markdown_file_large_stack",
        run_the_mechanics_chapter_10_markdown_file_impl,
    );
}

fn run_the_mechanics_chapter_10_markdown_file_impl() {
    run_single_the_mechanics_chapter_markdown_file_impl("Chapter_10_Relations.md", "Chapter 10");
}

pub(super) fn run_the_mechanics_markdown_files_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mechanics_dir = the_mechanics_dir(&manifest_dir);
    assert!(
        mechanics_dir.is_dir(),
        "{} must exist at {:?}",
        THE_MECHANICS_SUBDIR,
        mechanics_dir
    );

    let md_paths = collect_markdown_files_under_dir_sorted(&mechanics_dir);
    assert!(
        !md_paths.is_empty(),
        "{} must contain markdown files",
        THE_MECHANICS_SUBDIR
    );

    let mut snippets_by_file: Vec<Vec<(String, String, String)>> = Vec::new();
    let mut total_snippet_count: usize = 0;
    for md_path in md_paths.iter() {
        let snippets = litex_snippets_from_markdown_files(&manifest_dir, &[md_path.clone()]);
        total_snippet_count += snippets.len();
        snippets_by_file.push(snippets);
    }
    assert!(
        total_snippet_count > 0,
        "{} markdown files must contain ```litex``` blocks",
        THE_MECHANICS_SUBDIR
    );

    let mut snippet_durations_ms: Vec<(String, f64)> = Vec::new();
    let mut failed_labels: Vec<String> = Vec::new();
    let wall_start = Instant::now();
    let mut file_count_with_snippets: usize = 0;
    for snippets in snippets_by_file.iter() {
        if snippets.is_empty() {
            continue;
        }

        file_count_with_snippets += 1;
        let mut runtime = Runtime::new_with_builtin_code();

        for (snippet_index, (label, source_code, md_path_for_run_file)) in
            snippets.iter().enumerate()
        {
            if snippet_index == 0 {
                runtime.new_file_path_new_env_new_name_scope(md_path_for_run_file.as_str());
            } else {
                runtime.clear_current_env_and_parse_name_scope();
                runtime.set_current_user_lit_file_path(md_path_for_run_file.as_str());
            }

            let normalized_source = remove_windows_carriage_return(source_code);
            let start_snippet = Instant::now();
            let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_source_code(normalized_source.as_str(), &mut runtime)
            }));
            let (stmt_results, runtime_error) = match run_result {
                Ok(result) => result,
                Err(panic_payload) => {
                    let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;
                    let panic_message = if let Some(message) = panic_payload.downcast_ref::<&str>()
                    {
                        message.to_string()
                    } else if let Some(message) = panic_payload.downcast_ref::<String>() {
                        message.clone()
                    } else {
                        "non-string panic payload".to_string()
                    };
                    println!(
                        "=== [PANICKED] {} markdown snippet ({:.2} ms) ===\n{}\n>>> PANICKED snippet (open .md here): {}\n",
                        THE_MECHANICS_SUBDIR, duration_ms, panic_message, label
                    );
                    failed_labels.push(label.clone());
                    break;
                }
            };
            let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;

            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            if !run_succeeded {
                let status_label = if run_output.contains("\"error_type\": \"UnknownError\"") {
                    "UNKNOWN"
                } else {
                    "FAILED"
                };
                println!(
                    "=== [{}] {} markdown snippet ({:.2} ms) ===\n{}\n>>> {} snippet (open .md here): {}\n",
                    status_label, THE_MECHANICS_SUBDIR, duration_ms, run_output, status_label, label
                );
                failed_labels.push(label.clone());
                break;
            }
            snippet_durations_ms.push((label.clone(), duration_ms));
        }
    }

    let status_text = if failed_labels.is_empty() {
        "all OK"
    } else {
        "completed with failures"
    };
    println!(
        "--- {} markdown: {} ```litex``` block(s) in {} markdown file(s), {} ({:.2} ms wall) ---",
        THE_MECHANICS_SUBDIR,
        total_snippet_count,
        file_count_with_snippets,
        status_text,
        wall_start.elapsed().as_secs_f64() * 1000.0
    );
    for (label, duration_ms) in snippet_durations_ms.iter() {
        println!("  OK  {:.2} ms  {}", duration_ms, label);
    }

    if !failed_labels.is_empty() {
        println!("--- {} markdown failed snippets ---", THE_MECHANICS_SUBDIR);
        for label in failed_labels.iter() {
            println!("{}", label);
        }
    }
    assert!(
        failed_labels.is_empty(),
        "{} markdown has {} failing snippet(s); see output above",
        THE_MECHANICS_SUBDIR,
        failed_labels.len()
    );
}
