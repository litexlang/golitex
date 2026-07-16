use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_repository_file_target, run_source_code};
use crate::prelude::*;

use super::helper::{
    collect_lit_files_recursive_under_excluding, collect_markdown_files_under_dir_sorted,
    format_litex_failure_location, litex_snippets_from_markdown_files,
    print_known_forall_profile_summary, print_slowest_run_labels, run_with_large_stack,
    spawn_with_large_stack, REPOSITORY_EXAMPLES_SUBDIR,
};
use super::runtime_regression_tests::run_runtime_contract_suite_impl;

const ANALYSIS_ONE_CHAPTERS_SUBDIR: &str = "textbooks/Analysis";
const MECHANICS_TEXTBOOK_CHAPTERS_SUBDIR: &str = "textbooks/The-Mechanics-of-Litex-Proof";
const NUMBER_THEORY_FOR_BEGINNERS_SUBDIR: &str = "textbooks/NumberTheoryForBeginners";

#[derive(Clone)]
struct LitexRunItem {
    report_label: String,
    source: String,
    path_for_runtime: String,
    run_in_project_context: bool,
}

#[derive(Clone)]
struct LitexRunGroup {
    group_index: usize,
    group_label: String,
    items: Vec<LitexRunItem>,
}

struct LitexRunGroupSummary {
    group_index: usize,
    run_durations_ms: Vec<(String, f64)>,
    failed_labels: Vec<String>,
    failure_outputs: Vec<String>,
}

struct TimedRunSummary {
    ran: bool,
    run_durations_ms: Vec<(String, f64)>,
    wall_ms: f64,
}

/// Single footer: runtime setup + per-phase sums/walls + `phase timing` line.
fn print_run_examples_timing_summary(
    runtime_setup_duration_ms: f64,
    examples_ran: bool,
    example_runs_ms: &[(String, f64)],
    examples_phase_wall_ms: f64,
    doc_runs_ms: &[(String, f64)],
    docs_phase_wall_ms: f64,
) {
    let examples_sum_ms: f64 = example_runs_ms.iter().map(|(_, ms)| *ms).sum();
    let docs_sum_ms: f64 = doc_runs_ms.iter().map(|(_, ms)| *ms).sum();
    println!("--- timing (summary) ---");
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
    if examples_ran {
        println!(
            "  phase 1 (selected examples/**/*.lit + examples/07_dataset_gallery/**/*.md ```litex``` + docs/Manual.md ```litex```): sum of runs: {:.2} ms  |  wall: {:.2} ms",
            examples_sum_ms, examples_phase_wall_ms
        );
    }
    println!(
            "  remaining markdown ```litex``` snippets (README + docs excluding docs/Manual.md; see phase 1): sum of runs: {:.2} ms  |  wall: {:.2} ms",
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
    run_with_large_stack("run_examples_large_stack", run_examples_impl);
}

#[test]
fn run_docs_markdown_files() {
    run_with_large_stack("run_docs_markdown_files_large_stack", || {
        run_docs_markdown_impl(true)
    });
}

#[test]
fn run_all() {
    run_with_large_stack("run_all_large_stack", run_all_impl);
}

fn run_all_impl() {
    run_all_parallel_impl();
}

fn run_all_parallel_impl() {
    if crate::verify::known_forall_profile::enabled() {
        // The profile counters are process-global, so keep profiled aggregate runs sequential.
        println!(
            "--- run_all: LITEX_PROFILE_KNOWN_FORALL enabled; running datasets sequentially ---"
        );
        run_examples_impl();
        run_analysis_one_chapters_impl();
        run_mechanics_textbook_chapters_impl();
        run_number_theory_for_beginners_impl();
        run_runtime_contract_suite_impl();
        return;
    }

    println!(
        "--- run_all: running examples, docs, and runtime contracts in parallel; then textbook chapter suites ---"
    );
    let wall_start = Instant::now();
    let mut handles = Vec::new();
    handles.push((
        "examples",
        spawn_with_large_stack("run_all_examples_large_stack", run_examples_dataset_impl),
    ));
    handles.push((
        "docs",
        spawn_with_large_stack("run_all_docs_large_stack", || run_docs_markdown_impl(true)),
    ));
    handles.push((
        "runtime contracts",
        spawn_with_large_stack(
            "run_all_runtime_contracts_large_stack",
            run_runtime_contract_suite_impl,
        ),
    ));

    let mut failed_dataset_labels: Vec<&str> = Vec::new();
    for (label, handle) in handles {
        collect_run_all_dataset_result(label, handle, &mut failed_dataset_labels);
    }
    collect_run_all_dataset_result(
        "Analysis I chapters",
        spawn_with_large_stack(
            "run_all_analysis_one_chapters_large_stack",
            run_analysis_one_chapters_impl,
        ),
        &mut failed_dataset_labels,
    );
    collect_run_all_dataset_result(
        "Mechanics textbook chapters",
        spawn_with_large_stack(
            "run_all_mechanics_textbook_chapters_large_stack",
            run_mechanics_textbook_chapters_impl,
        ),
        &mut failed_dataset_labels,
    );
    collect_run_all_dataset_result(
        "Number Theory for Beginners chapters",
        spawn_with_large_stack(
            "run_number_theory_for_beginners_large_stack",
            run_number_theory_for_beginners_impl,
        ),
        &mut failed_dataset_labels,
    );

    println!(
        "--- run_all: parallel dataset wall time {:.2} ms ---",
        wall_start.elapsed().as_secs_f64() * 1000.0
    );
    assert!(
        failed_dataset_labels.is_empty(),
        "run_all dataset(s) failed: {}",
        failed_dataset_labels.join(", ")
    );
}

fn collect_run_all_dataset_result(
    label: &'static str,
    handle: std::thread::JoinHandle<()>,
    failed_dataset_labels: &mut Vec<&'static str>,
) {
    match handle.join() {
        Ok(()) => {
            println!("--- run_all: {} dataset OK ---", label);
        }
        Err(panic_payload) => {
            let panic_message = panic_payload_to_string(panic_payload);
            println!(
                "--- run_all: {} dataset panicked ---\n{}",
                label, panic_message
            );
            failed_dataset_labels.push(label);
        }
    }
}

#[test]
fn run_analysis_one_chapters() {
    run_with_large_stack(
        "run_analysis_one_chapters_large_stack",
        run_analysis_one_chapters_impl,
    );
}

fn run_analysis_one_chapters_impl() {
    run_textbook_chapters_impl(ANALYSIS_ONE_CHAPTERS_SUBDIR, "Analysis I chapters");
}

#[test]
fn run_mechanics_textbook_chapters() {
    run_with_large_stack(
        "run_mechanics_textbook_chapters_large_stack",
        run_mechanics_textbook_chapters_impl,
    );
}

fn run_mechanics_textbook_chapters_impl() {
    run_textbook_chapters_impl(
        MECHANICS_TEXTBOOK_CHAPTERS_SUBDIR,
        "Mechanics textbook chapters",
    );
}

#[test]
fn run_number_theory_for_beginners() {
    run_with_large_stack(
        "run_number_theory_for_beginners_large_stack",
        run_number_theory_for_beginners_impl,
    );
}

fn run_number_theory_for_beginners_impl() {
    run_textbook_chapters_impl(
        NUMBER_THEORY_FOR_BEGINNERS_SUBDIR,
        "Number Theory for Beginners sections",
    );
}

fn run_textbook_chapters_impl(chapters_subdir: &'static str, textbook_name: &'static str) {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repository_path = manifest_dir.join(chapters_subdir);
    let config_path = repository_path.join("litex.config");
    assert!(
        config_path.is_file(),
        "{} must contain litex.config",
        chapters_subdir
    );
    let repository_path = repository_path
        .to_str()
        .expect("textbook repository path must be valid UTF-8");

    println!(
        "--- {}: running one recursive -r project plan ---",
        textbook_name
    );
    let wall_start = Instant::now();
    let mut runtime = Runtime::new();
    let target = discover_repository(&mut runtime, repository_path).unwrap_or_else(|error| {
        panic!(
            "{} discovery failed at {}: {:?}",
            textbook_name, repository_path, error
        )
    });
    let (stmt_results, runtime_error) = run_repository_file_target(&mut runtime, target);
    let run_succeeded = runtime_error.is_none() && stmt_results.iter().all(StmtResult::is_true);
    let duration_ms = wall_start.elapsed().as_secs_f64() * 1000.0;

    if !run_succeeded {
        let (_, output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        panic!(
            "{} -r failed after {:.2} ms:\n{}",
            textbook_name, duration_ms, output
        );
    }

    println!(
        "--- {}: one -r run, {} top-level result(s), all OK ({:.2} ms) ---",
        textbook_name,
        stmt_results.len(),
        duration_ms,
    );
}

fn run_examples_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;

    let examples_summary = run_examples_phase1_with_runtime(&manifest_dir, &mut runtime, true);
    let docs_summary =
        run_docs_markdown_with_runtime(&manifest_dir, &mut runtime, false, !examples_summary.ran);
    print_run_examples_timing_summary(
        runtime_setup_duration_ms,
        examples_summary.ran,
        examples_summary.run_durations_ms.as_slice(),
        examples_summary.wall_ms,
        docs_summary.run_durations_ms.as_slice(),
        docs_summary.wall_ms,
    );
}

fn run_examples_dataset_impl() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;
    let examples_summary = run_examples_phase1_with_runtime(&manifest_dir, &mut runtime, false);
    print_examples_dataset_timing_summary(runtime_setup_duration_ms, &examples_summary, false);
}

fn run_docs_markdown_impl(include_manual_docs: bool) {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime_setup_start = Instant::now();
    let mut runtime = Runtime::new();
    let runtime_setup_duration_ms = runtime_setup_start.elapsed().as_secs_f64() * 1000.0;
    let docs_summary =
        run_docs_markdown_with_runtime(&manifest_dir, &mut runtime, include_manual_docs, true);
    print_docs_timing_summary(
        runtime_setup_duration_ms,
        &docs_summary,
        include_manual_docs,
    );
}

fn run_examples_phase1_with_runtime(
    manifest_dir: &Path,
    runtime: &mut Runtime,
    include_manual_docs: bool,
) -> TimedRunSummary {
    if crate::verify::known_forall_profile::enabled() {
        return run_examples_phase1_sequential_with_runtime(
            manifest_dir,
            runtime,
            include_manual_docs,
        );
    }

    let phase_label = examples_phase_label(include_manual_docs);
    let phase1_groups = collect_examples_phase1_groups(manifest_dir, include_manual_docs);
    let phase1_items_count: usize = phase1_groups.iter().map(|group| group.items.len()).sum();
    let phase1_group_count = phase1_groups.len();

    if phase1_groups.is_empty() {
        println!("--- {}: no runs ---", phase_label);
        return TimedRunSummary {
            ran: false,
            run_durations_ms: Vec::new(),
            wall_ms: 0.0,
        };
    }

    runtime
        .new_file_path_new_env_new_name_scope(phase1_groups[0].items[0].path_for_runtime.as_str());
    crate::verify::known_forall_profile::reset();

    let examples_wall_start = Instant::now();
    let mut handles = Vec::new();
    for group in phase1_groups {
        let thread_name = format!("run_examples_phase1_group_{}", group.group_index);
        handles.push(spawn_with_large_stack(thread_name.as_str(), move || {
            run_litex_run_group(group)
        }));
    }

    let mut group_summaries = Vec::new();
    for handle in handles {
        match handle.join() {
            Ok(summary) => group_summaries.push(summary),
            Err(panic_payload) => {
                let panic_message = panic_payload_to_string(panic_payload);
                group_summaries.push(LitexRunGroupSummary {
                    group_index: usize::MAX,
                    run_durations_ms: Vec::new(),
                    failed_labels: vec!["examples phase 1 worker panic".to_string()],
                    failure_outputs: vec![format!(
                        "=== [PANICKED] {} worker ===\n{}",
                        phase_label, panic_message
                    )],
                });
            }
        }
    }
    let examples_phase_wall_ms = examples_wall_start.elapsed().as_secs_f64() * 1000.0;

    group_summaries.sort_by_key(|summary| summary.group_index);
    let mut file_label_and_duration_ms_list: Vec<(String, f64)> = Vec::new();
    let mut failed_labels: Vec<String> = Vec::new();
    let mut failure_outputs: Vec<String> = Vec::new();
    for summary in group_summaries {
        file_label_and_duration_ms_list.extend(summary.run_durations_ms);
        failed_labels.extend(summary.failed_labels);
        failure_outputs.extend(summary.failure_outputs);
    }

    print_known_forall_profile_summary(phase_label);

    if failed_labels.is_empty() {
        println!(
            "--- {}: {} run(s) in {} group(s), all OK ---",
            phase_label, phase1_items_count, phase1_group_count
        );
        println!(
            "--- {}: ran {} file/group(s) in parallel ---",
            phase_label, phase1_group_count
        );
        let slowest_title = format!("{} runs", phase_label);
        print_slowest_run_labels(
            slowest_title.as_str(),
            file_label_and_duration_ms_list.as_slice(),
        );
        for (file_label, duration_ms) in file_label_and_duration_ms_list.iter() {
            println!("  {}  {:.2} ms", file_label, duration_ms);
        }
    } else {
        let slowest_title = format!("{} runs before failure", phase_label);
        print_slowest_run_labels(
            slowest_title.as_str(),
            file_label_and_duration_ms_list.as_slice(),
        );
        for output in failure_outputs.iter() {
            println!("{}", output);
        }
    }

    assert!(
        failed_labels.is_empty(),
        "{} failed; see output above",
        phase_label
    );

    TimedRunSummary {
        ran: true,
        run_durations_ms: file_label_and_duration_ms_list,
        wall_ms: examples_phase_wall_ms,
    }
}

fn run_examples_phase1_sequential_with_runtime(
    manifest_dir: &Path,
    runtime: &mut Runtime,
    include_manual_docs: bool,
) -> TimedRunSummary {
    let phase_label = examples_phase_label(include_manual_docs);
    let phase1_items = collect_examples_phase1_items(manifest_dir, include_manual_docs);

    let mut file_label_and_duration_ms_list: Vec<(String, f64)> = Vec::new();
    let mut every_file_run_ok = true;
    let mut examples_ran = false;
    let mut examples_phase_wall_ms: f64 = 0.0;

    if phase1_items.is_empty() {
        println!("--- {}: no runs ---", phase_label);
    } else {
        examples_ran = true;
        let examples_wall_start = Instant::now();
        let first_path = phase1_items[0].path_for_runtime.as_str();
        runtime.new_file_path_new_env_new_name_scope(first_path);
        crate::verify::known_forall_profile::reset();

        for (item_index, item) in phase1_items.iter().enumerate() {
            if item_index > 0 {
                runtime.reset_for_isolated_runner_item();
                runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
            }

            let normalized_source = remove_windows_carriage_return(item.source.as_str());

            let start_time_for_one_file = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), runtime);
            let duration_ms_for_one_file = start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;

            let (run_succeeded, run_output) =
                render_run_source_code_output(runtime, &stmt_results, &runtime_error, false);

            if !run_succeeded {
                every_file_run_ok = false;
                file_label_and_duration_ms_list
                    .push((item.report_label.clone(), duration_ms_for_one_file));
                let failure_location =
                    format_litex_failure_location(&item.report_label, &runtime_error);
                let slowest_title = format!("{} runs before failure", phase_label);
                print_slowest_run_labels(
                    slowest_title.as_str(),
                    file_label_and_duration_ms_list.as_slice(),
                );
                println!(
                    "=== [{}] {} ===\n{}\n>>> FAILED location: {}\n",
                    "FAILED", failure_location, run_output, failure_location
                );
                break;
            }

            file_label_and_duration_ms_list
                .push((item.report_label.clone(), duration_ms_for_one_file));
        }
        examples_phase_wall_ms = examples_wall_start.elapsed().as_secs_f64() * 1000.0;
        print_known_forall_profile_summary(phase_label);
    }

    if every_file_run_ok && examples_ran {
        println!(
            "--- {}: {} run(s), all OK ---",
            phase_label,
            file_label_and_duration_ms_list.len()
        );
        let slowest_title = format!("{} runs", phase_label);
        print_slowest_run_labels(
            slowest_title.as_str(),
            file_label_and_duration_ms_list.as_slice(),
        );
        for (file_label, duration_ms) in file_label_and_duration_ms_list.iter() {
            println!("  {}  {:.2} ms", file_label, duration_ms);
        }
    }

    assert!(
        every_file_run_ok,
        "{} failed; see output above",
        phase_label
    );

    TimedRunSummary {
        ran: examples_ran,
        run_durations_ms: file_label_and_duration_ms_list,
        wall_ms: examples_phase_wall_ms,
    }
}

fn run_docs_markdown_with_runtime(
    manifest_dir: &Path,
    runtime: &mut Runtime,
    include_manual_docs: bool,
    runtime_needs_file_path: bool,
) -> TimedRunSummary {
    let docs_label = docs_markdown_label(include_manual_docs);
    let docs_dir = manifest_dir.join("docs");
    if !docs_dir.is_dir() {
        println!(
            "--- docs folder missing at {:?}; skip markdown litex blocks ---",
            docs_dir
        );
        return TimedRunSummary {
            ran: false,
            run_durations_ms: Vec::new(),
            wall_ms: 0.0,
        };
    }

    let mut md_paths_all: Vec<PathBuf> = Vec::new();
    let readme_path = manifest_dir.join("README.md");
    if readme_path.is_file() {
        md_paths_all.push(readme_path);
    }
    md_paths_all.extend(collect_markdown_files_under_dir_sorted(&docs_dir));
    md_paths_all.sort();

    let md_paths: Vec<PathBuf> = if include_manual_docs {
        md_paths_all
    } else {
        md_paths_all
            .into_iter()
            .filter(|p| !is_manual_markdown_path(manifest_dir, p))
            .collect()
    };

    let doc_snippets = litex_snippets_from_markdown_files(manifest_dir, &md_paths);
    if doc_snippets.is_empty() {
        println!("--- {}: no ```litex``` fenced blocks ---", docs_label);
        return TimedRunSummary {
            ran: false,
            run_durations_ms: Vec::new(),
            wall_ms: 0.0,
        };
    }

    if runtime_needs_file_path {
        let synthetic_path = format!("{} ```litex``` snippets", docs_label);
        runtime.new_file_path_new_env_new_name_scope(synthetic_path.as_str());
    }

    println!(
        "--- {}: {} ```litex``` block(s) in {} markdown file(s) ---",
        docs_label,
        doc_snippets.len(),
        md_paths.len()
    );

    crate::verify::known_forall_profile::reset();
    let docs_wall_start = Instant::now();
    let mut doc_durations_ms: Vec<(String, f64)> = Vec::new();
    for (snippet_index, (label, source_code, source_path)) in doc_snippets.iter().enumerate() {
        if !runtime_needs_file_path || snippet_index > 0 {
            runtime.reset_for_isolated_runner_item();
        }
        runtime.set_current_user_lit_file_path(source_path.as_str());

        let normalized_source = remove_windows_carriage_return(source_code);
        let start_snippet = Instant::now();
        let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), runtime);
        let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(runtime, &stmt_results, &runtime_error, false);

        doc_durations_ms.push((label.clone(), duration_ms));

        if !run_succeeded {
            let failure_location = format_litex_failure_location(label, &runtime_error);
            let slowest_title = format!("{} snippets before failure", docs_label);
            print_slowest_run_labels(slowest_title.as_str(), doc_durations_ms.as_slice());
            panic!(
                "{} litex snippet FAILED at {}:\n{}\n>>> FAILED snippet (open .md here): {}\n",
                docs_label, failure_location, run_output, failure_location
            );
        }
    }
    let docs_phase_wall_ms = docs_wall_start.elapsed().as_secs_f64() * 1000.0;
    print_known_forall_profile_summary(docs_label);

    let slowest_title = format!("{} snippets", docs_label);
    print_slowest_run_labels(slowest_title.as_str(), doc_durations_ms.as_slice());
    for (label, duration_ms) in doc_durations_ms.iter() {
        println!("  OK  {:.2} ms  {}", duration_ms, label);
    }

    TimedRunSummary {
        ran: true,
        run_durations_ms: doc_durations_ms,
        wall_ms: docs_phase_wall_ms,
    }
}

fn collect_examples_phase1_items(
    manifest_dir: &Path,
    include_manual_docs: bool,
) -> Vec<LitexRunItem> {
    collect_examples_phase1_groups(manifest_dir, include_manual_docs)
        .into_iter()
        .flat_map(|group| group.items)
        .collect()
}

fn collect_examples_phase1_groups(
    manifest_dir: &Path,
    include_manual_docs: bool,
) -> Vec<LitexRunGroup> {
    let lit_file_paths = collect_lit_files_recursive_under_excluding(
        manifest_dir,
        "examples",
        &[REPOSITORY_EXAMPLES_SUBDIR],
    );

    let manual_md_paths = if include_manual_docs {
        collect_manual_markdown_paths(manifest_dir)
    } else {
        Vec::new()
    };
    let dataset_gallery_md_dir = manifest_dir.join("examples").join("07_dataset_gallery");
    let dataset_gallery_md_paths = collect_markdown_files_under_dir_sorted(&dataset_gallery_md_dir);

    let mut phase1_groups: Vec<LitexRunGroup> = Vec::new();
    for lit_file_path in lit_file_paths.iter() {
        let lit_file_path_str = match lit_file_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", lit_file_path),
        };
        let file_label_for_report = match lit_file_path.strip_prefix(manifest_dir) {
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
        let group_index = phase1_groups.len();
        phase1_groups.push(LitexRunGroup {
            group_index,
            group_label: file_label_for_report.clone(),
            items: vec![LitexRunItem {
                report_label: file_label_for_report,
                source: source_code,
                path_for_runtime: lit_file_path_str.to_string(),
                run_in_project_context: false,
            }],
        });
    }
    push_markdown_run_groups(&mut phase1_groups, manifest_dir, &manual_md_paths);
    push_markdown_run_groups(&mut phase1_groups, manifest_dir, &dataset_gallery_md_paths);
    phase1_groups
}

fn push_markdown_run_groups(
    groups: &mut Vec<LitexRunGroup>,
    manifest_dir: &Path,
    md_paths: &[PathBuf],
) {
    for md_path in md_paths.iter() {
        let snippets = litex_snippets_from_markdown_files(manifest_dir, &[md_path.clone()]);
        if snippets.is_empty() {
            continue;
        }
        let group_label = md_path
            .strip_prefix(manifest_dir)
            .unwrap_or(md_path)
            .display()
            .to_string();
        let mut items = Vec::new();
        for (label, block, md_path_str) in snippets {
            items.push(LitexRunItem {
                report_label: label,
                source: block,
                path_for_runtime: md_path_str,
                run_in_project_context: false,
            });
        }
        let group_index = groups.len();
        groups.push(LitexRunGroup {
            group_index,
            group_label,
            items,
        });
    }
}

fn run_litex_run_group(group: LitexRunGroup) -> LitexRunGroupSummary {
    let mut runtime = Runtime::new();
    let mut run_durations_ms: Vec<(String, f64)> = Vec::new();
    let mut failed_labels: Vec<String> = Vec::new();
    let mut failure_outputs: Vec<String> = Vec::new();

    for (item_index, item) in group.items.iter().enumerate() {
        if item.run_in_project_context {
            let start_time_for_one_file = Instant::now();
            let (run_succeeded, run_output) =
                run_source_code_in_file_with_ok(item.path_for_runtime.as_str());
            let duration_ms = start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;
            run_durations_ms.push((item.report_label.clone(), duration_ms));

            if !run_succeeded {
                failure_outputs.push(format!(
                    "=== [FAILED] {} ({:.2} ms) ===\n{}\n>>> FAILED project file: {}\n",
                    item.report_label, duration_ms, run_output, item.report_label
                ));
                failed_labels.push(item.report_label.clone());
                break;
            }
            continue;
        }

        if item_index == 0 {
            runtime.new_file_path_new_env_new_name_scope(item.path_for_runtime.as_str());
        } else {
            runtime.reset_for_isolated_runner_item();
            runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
        }

        let normalized_source = remove_windows_carriage_return(item.source.as_str());
        let start_time_for_one_file = Instant::now();
        let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_source_code(normalized_source.as_str(), &mut runtime)
        }));
        let (stmt_results, runtime_error) = match run_result {
            Ok(result) => result,
            Err(panic_payload) => {
                let duration_ms = start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;
                let panic_message = panic_payload_to_string(panic_payload);
                run_durations_ms.push((item.report_label.clone(), duration_ms));
                failure_outputs.push(format!(
                    "=== [PANICKED] {} ({:.2} ms) ===\n{}\n>>> PANICKED snippet (open here): {}\n",
                    group.group_label, duration_ms, panic_message, item.report_label
                ));
                failed_labels.push(item.report_label.clone());
                break;
            }
        };
        let duration_ms = start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        run_durations_ms.push((item.report_label.clone(), duration_ms));

        if !run_succeeded {
            let failure_location =
                format_litex_failure_location(&item.report_label, &runtime_error);
            failure_outputs.push(format!(
                "=== [FAILED] {} ({:.2} ms) ===\n{}\n>>> FAILED location: {}\n",
                failure_location, duration_ms, run_output, failure_location
            ));
            failed_labels.push(failure_location);
            break;
        }
    }

    LitexRunGroupSummary {
        group_index: group.group_index,
        run_durations_ms,
        failed_labels,
        failure_outputs,
    }
}

fn print_examples_dataset_timing_summary(
    runtime_setup_duration_ms: f64,
    examples_summary: &TimedRunSummary,
    include_manual_docs: bool,
) {
    let phase_label = examples_phase_label(include_manual_docs);
    let examples_sum_ms: f64 = examples_summary
        .run_durations_ms
        .iter()
        .map(|(_, ms)| *ms)
        .sum();
    println!("--- timing ({}) ---", phase_label);
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
    if examples_summary.ran {
        println!(
            "  runs: sum of runs: {:.2} ms  |  wall: {:.2} ms",
            examples_sum_ms, examples_summary.wall_ms
        );
    }
}

fn print_docs_timing_summary(
    runtime_setup_duration_ms: f64,
    docs_summary: &TimedRunSummary,
    include_manual_docs: bool,
) {
    let docs_label = docs_markdown_label(include_manual_docs);
    let docs_sum_ms: f64 = docs_summary
        .run_durations_ms
        .iter()
        .map(|(_, ms)| *ms)
        .sum();
    println!("--- timing ({}) ---", docs_label);
    println!(
        "  runtime setup (once): {:.2} ms",
        runtime_setup_duration_ms
    );
    if docs_summary.ran {
        println!(
            "  snippets: sum of runs: {:.2} ms  |  wall: {:.2} ms",
            docs_sum_ms, docs_summary.wall_ms
        );
    }
}

fn examples_phase_label(include_manual_docs: bool) -> &'static str {
    if include_manual_docs {
        "phase 1 (selected examples/**/*.lit + examples/07_dataset_gallery/**/*.md ```litex``` + docs/Manual.md ```litex```)"
    } else {
        "examples dataset (selected examples/**/*.lit + examples/07_dataset_gallery/**/*.md ```litex```)"
    }
}

fn docs_markdown_label(include_manual_docs: bool) -> &'static str {
    if include_manual_docs {
        "docs markdown (README + docs/**/*.md)"
    } else {
        "remaining markdown (README + docs excluding docs/Manual.md)"
    }
}

fn collect_manual_markdown_paths(manifest_dir: &Path) -> Vec<PathBuf> {
    let mut manual_md_paths = Vec::new();
    let manual_md_file = manifest_dir.join("docs").join("Manual.md");
    if manual_md_file.is_file() {
        manual_md_paths.push(manual_md_file);
    }
    let manual_md_dir = manifest_dir.join("docs").join("Manual");
    manual_md_paths.extend(collect_markdown_files_under_dir_sorted(&manual_md_dir));
    manual_md_paths.sort();
    manual_md_paths
}

fn is_manual_markdown_path(manifest_dir: &Path, path: &Path) -> bool {
    let manual_md_file = manifest_dir.join("docs").join("Manual.md");
    let manual_md_dir = manifest_dir.join("docs").join("Manual");
    path == manual_md_file.as_path() || path.starts_with(manual_md_dir)
}

fn panic_payload_to_string(panic_payload: Box<dyn std::any::Any + Send + 'static>) -> String {
    if let Some(message) = panic_payload.downcast_ref::<&str>() {
        message.to_string()
    } else if let Some(message) = panic_payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}
