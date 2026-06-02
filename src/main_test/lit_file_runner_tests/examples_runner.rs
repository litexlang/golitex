use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

use super::helper::{
    collect_lit_files_recursive_under, collect_lit_files_recursive_under_excluding,
    collect_markdown_files_under_dir_sorted, extract_litex_fenced_blocks,
    litex_snippets_from_markdown_files, print_known_forall_profile_summary,
    print_slowest_run_labels, run_with_large_stack, CITE_STD_EXAMPLES_SUBDIR,
};
use super::mechanics_markdown_runner::run_the_mechanics_markdown_files_impl;

/// Single footer: builtin + per-phase sums/walls + `phase timing` line.
fn print_run_examples_timing_summary(
    builtin_duration_ms: f64,
    examples_ran: bool,
    example_runs_ms: &[(String, f64)],
    examples_phase_wall_ms: f64,
    doc_runs_ms: &[(String, f64)],
    docs_phase_wall_ms: f64,
) {
    let examples_sum_ms: f64 = example_runs_ms.iter().map(|(_, ms)| *ms).sum();
    let docs_sum_ms: f64 = doc_runs_ms.iter().map(|(_, ms)| *ms).sum();
    println!("--- timing (summary) ---");
    println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
    if examples_ran {
        println!(
            "  phase 1 (selected examples/**/*.lit + docs/Manual ```litex```): sum of runs: {:.2} ms  |  wall: {:.2} ms",
            examples_sum_ms, examples_phase_wall_ms
        );
    }
    println!(
            "  remaining markdown ```litex``` snippets (README + docs excluding docs/Manual; see phase 1): sum of runs: {:.2} ms  |  wall: {:.2} ms",
            docs_sum_ms, docs_phase_wall_ms
        );
    println!(
        "--- phase timing: phase1 {:.2} ms | docs {:.2} ms ---",
        examples_phase_wall_ms, docs_phase_wall_ms
    );

    let mut all_runs_ms: Vec<(String, f64)> = Vec::new();
    for (label, duration_ms) in example_runs_ms.iter() {
        all_runs_ms.push((format!("phase 1: {}", label), *duration_ms));
    }
    for (label, duration_ms) in doc_runs_ms.iter() {
        all_runs_ms.push((format!("docs: {}", label), *duration_ms));
    }
    print_slowest_run_labels("all examples/docs runs", all_runs_ms.as_slice());
}

#[test]
fn run_examples() {
    run_with_large_stack("run_examples_large_stack", || run_examples_impl(false));
}

#[test]
fn run_examples_include_std() {
    if !include_std_test_selected_directly("run_examples_include_std") {
        return;
    }
    run_with_large_stack("run_examples_include_std_large_stack", || {
        run_examples_impl(true)
    });
}

#[test]
fn run_all() {
    run_with_large_stack("run_all_large_stack", run_all_impl);
}

#[test]
fn run_all_include_std() {
    if !include_std_test_selected_directly("run_all_include_std") {
        return;
    }
    run_with_large_stack("run_all_include_std_large_stack", run_all_include_std_impl);
}

fn run_all_impl() {
    run_examples_impl(false);
    run_the_mechanics_markdown_files_impl();
}

fn run_all_include_std_impl() {
    run_examples_impl(true);
    run_the_mechanics_markdown_files_impl();
}

#[test]
fn run_the_mechanics_of_litex_proof() {
    run_with_large_stack(
        "run_the_mechanics_of_litex_proof_large_stack",
        run_the_mechanics_of_litex_proof_impl,
    );
}

fn run_the_mechanics_of_litex_proof_impl() {
    run_the_mechanics_markdown_files_impl();
}

fn run_examples_impl(include_std_examples: bool) {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let lit_file_paths = if include_std_examples {
        collect_lit_files_recursive_under(&manifest_dir, "examples")
    } else {
        collect_lit_files_recursive_under_excluding(
            &manifest_dir,
            "examples",
            &[CITE_STD_EXAMPLES_SUBDIR],
        )
    };
    if include_std_examples {
        println!("--- examples/_internal/std_imports included ---");
    } else {
        println!(
            "--- examples/_internal/std_imports excluded; use run_examples_include_std to include it ---"
        );
    }

    let manual_md_dir = manifest_dir.join("docs").join("Manual");
    let manual_md_paths = collect_markdown_files_under_dir_sorted(&manual_md_dir);
    let manual_snippets = litex_snippets_from_markdown_files(&manifest_dir, &manual_md_paths);

    #[derive(Clone)]
    struct Phase1Item {
        report_label: String,
        source: String,
        path_for_runtime: String,
    }

    let mut phase1_items: Vec<Phase1Item> = Vec::new();
    for lit_file_path in lit_file_paths.iter() {
        let lit_file_path_str = match lit_file_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", lit_file_path),
        };
        let file_label_for_report = match lit_file_path.strip_prefix(&manifest_dir) {
            Ok(rel) => rel.display().to_string(),
            Err(_) => match lit_file_path.file_name() {
                Some(os_file_name) => match os_file_name.to_str() {
                    Some(name_string) => String::from(name_string),
                    None => format!("{:?}", lit_file_path),
                },
                None => format!("{:?}", lit_file_path),
            },
        };
        let source_code = match fs::read_to_string(lit_file_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", lit_file_path, read_error),
        };
        phase1_items.push(Phase1Item {
            report_label: file_label_for_report,
            source: source_code,
            path_for_runtime: lit_file_path_str.to_string(),
        });
    }
    for (label, block, md_path_str) in manual_snippets.iter() {
        phase1_items.push(Phase1Item {
            report_label: label.clone(),
            source: block.clone(),
            path_for_runtime: md_path_str.clone(),
        });
    }

    let builtin_start = Instant::now();
    let mut runtime = Runtime::new_with_builtin_code();
    let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;

    let mut file_label_and_duration_ms_list: Vec<(String, f64)> = Vec::new();
    let mut every_file_run_ok = true;
    let mut examples_ran = false;
    let mut examples_phase_wall_ms: f64 = 0.0;

    if phase1_items.is_empty() {
        println!(
            "--- phase 1: no selected examples/**/*.lit and no docs/Manual ```litex``` snippets ---"
        );
    } else {
        examples_ran = true;
        let examples_wall_start = Instant::now();
        let first_path = phase1_items[0].path_for_runtime.as_str();
        runtime.new_file_path_new_env_new_name_scope(first_path);
        crate::verify::known_forall_profile::reset();

        for (item_index, item) in phase1_items.iter().enumerate() {
            if item_index > 0 {
                runtime.clear_current_env_and_parse_name_scope();
                runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
            }

            let normalized_source = remove_windows_carriage_return(item.source.as_str());

            let start_time_for_one_file = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), &mut runtime);
            let duration_ms_for_one_file = start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;

            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            if !run_succeeded {
                every_file_run_ok = false;
                file_label_and_duration_ms_list
                    .push((item.report_label.clone(), duration_ms_for_one_file));
                print_slowest_run_labels(
                    "phase 1 runs before failure",
                    file_label_and_duration_ms_list.as_slice(),
                );
                println!(
                    "=== [{}] {} ===\n{}\n>>> FAILED snippet (open .md here): {}\n",
                    "FAILED", item.report_label, run_output, item.report_label
                );
                break;
            }

            file_label_and_duration_ms_list
                .push((item.report_label.clone(), duration_ms_for_one_file));
        }
        examples_phase_wall_ms = examples_wall_start.elapsed().as_secs_f64() * 1000.0;
        print_known_forall_profile_summary("phase 1");
    }

    if every_file_run_ok && examples_ran {
        println!(
            "--- phase 1: {} run(s) (selected examples/**/*.lit + docs/Manual ```litex```), all OK ---",
            file_label_and_duration_ms_list.len()
        );
        print_slowest_run_labels("phase 1 runs", file_label_and_duration_ms_list.as_slice());
        for (file_label, duration_ms) in file_label_and_duration_ms_list.iter() {
            println!("  {}  {:.2} ms", file_label, duration_ms);
        }
    }

    assert!(
        every_file_run_ok,
        "examples or docs/Manual litex snippet failed; see output above"
    );

    let docs_dir = manifest_dir.join("docs");
    if !docs_dir.is_dir() {
        println!(
            "--- docs folder missing at {:?}; skip markdown litex blocks ---",
            docs_dir
        );
        print_run_examples_timing_summary(
            builtin_duration_ms,
            examples_ran,
            file_label_and_duration_ms_list.as_slice(),
            examples_phase_wall_ms,
            &[],
            0.0,
        );
        return;
    }

    let mut md_paths_all: Vec<PathBuf> = Vec::new();
    let readme_path = manifest_dir.join("README.md");
    if readme_path.is_file() {
        md_paths_all.push(readme_path);
    }
    md_paths_all.extend(collect_markdown_files_under_dir_sorted(&docs_dir));
    md_paths_all.sort();
    let manual_prefix = manifest_dir.join("docs").join("Manual");
    let md_paths: Vec<PathBuf> = md_paths_all
        .into_iter()
        .filter(|p| !p.starts_with(&manual_prefix))
        .collect();

    // (test report label, fenced litex body, current markdown path string for relative run_file resolution)
    let mut doc_snippets: Vec<(String, String, String)> = Vec::new();
    for md_path in md_paths.iter() {
        let rel_label = md_path
            .strip_prefix(&manifest_dir)
            .unwrap_or(md_path)
            .display()
            .to_string();
        let md_current_path_str = md_path.to_string_lossy().into_owned();
        let md_content = match fs::read_to_string(md_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", md_path, read_error),
        };
        for (block_index, (md_line, block)) in extract_litex_fenced_blocks(&md_content)
            .into_iter()
            .enumerate()
        {
            doc_snippets.push((
                format!(
                    "{} ```litex```#{} (md line {})",
                    rel_label, block_index, md_line
                ),
                block,
                md_current_path_str.clone(),
            ));
        }
    }

    if doc_snippets.is_empty() {
        println!("--- remaining markdown: no ```litex``` fenced blocks ---");
        print_run_examples_timing_summary(
            builtin_duration_ms,
            examples_ran,
            file_label_and_duration_ms_list.as_slice(),
            examples_phase_wall_ms,
            &[],
            0.0,
        );
        return;
    }

    if !examples_ran {
        runtime.new_file_path_new_env_new_name_scope("remaining markdown ```litex``` snippets");
    }

    println!(
        "--- remaining markdown: {} ```litex``` block(s) in {} markdown file(s) ---",
        doc_snippets.len(),
        md_paths.len()
    );

    crate::verify::known_forall_profile::reset();
    let docs_wall_start = Instant::now();
    let mut doc_durations_ms: Vec<(String, f64)> = Vec::new();
    for (snippet_index, (label, source_code, md_path_for_run_file)) in
        doc_snippets.iter().enumerate()
    {
        if examples_ran || snippet_index > 0 {
            runtime.clear_current_env_and_parse_name_scope();
        }
        runtime.set_current_user_lit_file_path(md_path_for_run_file.as_str());

        let normalized_source = remove_windows_carriage_return(source_code);
        let start_snippet = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        doc_durations_ms.push((label.clone(), duration_ms));

        if !run_succeeded {
            print_slowest_run_labels(
                "remaining markdown snippets before failure",
                doc_durations_ms.as_slice(),
            );
            panic!(
                "docs litex snippet FAILED:\n{}\n>>> FAILED snippet (open .md here): {}\n",
                run_output, label
            );
        }
    }
    let docs_phase_wall_ms = docs_wall_start.elapsed().as_secs_f64() * 1000.0;
    print_known_forall_profile_summary("remaining markdown");

    print_slowest_run_labels("remaining markdown snippets", doc_durations_ms.as_slice());
    for (label, duration_ms) in doc_durations_ms.iter() {
        println!("  OK  {:.2} ms  {}", duration_ms, label);
    }
    print_run_examples_timing_summary(
        builtin_duration_ms,
        examples_ran,
        file_label_and_duration_ms_list.as_slice(),
        examples_phase_wall_ms,
        doc_durations_ms.as_slice(),
        docs_phase_wall_ms,
    );
}

fn include_std_test_selected_directly(test_name: &str) -> bool {
    let full_path_suffix = format!("::{}", test_name);
    let selected = std::env::args()
        .skip(1)
        .any(|arg| arg == test_name || arg.ends_with(&full_path_suffix));
    if !selected {
        println!(
            "--- {} skipped; select it directly with `cargo test {} -- --nocapture` ---",
            test_name, test_name
        );
    }
    selected
}
