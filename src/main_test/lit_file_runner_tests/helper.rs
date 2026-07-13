use std::fs;
use std::path::{Path, PathBuf};

use crate::prelude::*;

const LARGE_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;
const SLOWEST_RUNS_TO_PRINT: usize = 10;
pub(super) const REPOSITORY_EXAMPLES_SUBDIR: &str = "examples/08_module_repository";
pub(super) const SKETCH_EXAMPLES_SUBDIR: &str = "examples/_internal/sketch";

pub(super) fn print_known_forall_profile_summary(label: &str) {
    if !crate::verify::known_forall_profile::enabled() {
        return;
    }
    let p = crate::verify::known_forall_profile::snapshot();
    println!(
        "--- known_forall profile: {} ---\n  entries={} success={} unknown={} candidates={} exact={} fallback={} other={} env_user={} env_builtin={} arg_matches={} requirement_failures={}",
        label,
        p.entries,
        p.successes,
        p.unknowns,
        p.candidate_attempts,
        p.exact_candidate_attempts,
        p.fallback_candidate_attempts,
        p.other_candidate_attempts,
        p.user_candidate_attempts,
        p.builtin_candidate_attempts,
        p.arg_matches,
        p.requirement_failures,
    );
}

pub(super) fn spawn_with_large_stack<T: Send + 'static>(
    test_name: &str,
    f: impl FnOnce() -> T + Send + 'static,
) -> std::thread::JoinHandle<T> {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(LARGE_TEST_STACK_SIZE)
        .spawn(f)
        .unwrap()
}

pub(super) fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
    spawn_with_large_stack(test_name, f).join().unwrap();
}

pub(super) fn format_litex_failure_location(
    report_label: &str,
    runtime_error: &Option<RuntimeError>,
) -> String {
    let Some(error) = runtime_error.as_ref() else {
        return report_label.to_string();
    };

    let outer_line_number = error.line_file().0;
    let line_number = deepest_runtime_error_line(error);
    if line_number == 0 {
        return report_label.to_string();
    }

    let outer_line_suffix = if outer_line_number > 0 && outer_line_number != line_number {
        format!(" (outer line {})", outer_line_number)
    } else {
        String::new()
    };

    if report_label.contains("```litex```") {
        format!(
            "{}; snippet line {}{}",
            report_label, line_number, outer_line_suffix
        )
    } else {
        format!("{}:{}{}", report_label, line_number, outer_line_suffix)
    }
}

fn deepest_runtime_error_line(error: &RuntimeError) -> usize {
    let (line_number, previous_error) = runtime_error_line_and_previous(error);
    match previous_error {
        Some(previous_error) => {
            let previous_line_number = deepest_runtime_error_line(previous_error);
            if previous_line_number > 0 {
                previous_line_number
            } else {
                line_number
            }
        }
        None => line_number,
    }
}

fn runtime_error_line_and_previous(error: &RuntimeError) -> (usize, Option<&RuntimeError>) {
    match error {
        RuntimeError::ArithmeticError(error)
        | RuntimeError::NewFactError(error)
        | RuntimeError::StoreFactError(error)
        | RuntimeError::ParseError(error)
        | RuntimeError::ExecStmtError(error)
        | RuntimeError::WellDefinedError(error)
        | RuntimeError::VerifyError(error)
        | RuntimeError::UnknownError(error)
        | RuntimeError::InferError(error)
        | RuntimeError::NameAlreadyUsedError(error)
        | RuntimeError::DefineParamsError(error)
        | RuntimeError::InstantiateError(error) => {
            (error.line_file.0, error.previous_error.as_deref())
        }
    }
}

/// Collect ```litex``` bodies. A block is omitted when the last non-empty line before its opening
/// fence is exactly `<!-- litex:skip-test -->` (for snippets that are illustrative only).
/// The line number is 1-based: the markdown line where the opening ` ```litex ` fence starts.
pub(super) fn extract_litex_fenced_blocks(markdown: &str) -> Vec<(usize, String)> {
    const SKIP_MARKER: &str = "<!-- litex:skip-test -->";
    let mut blocks: Vec<(usize, String)> = Vec::new();
    let mut in_litex = false;
    let mut skip_this_block = false;
    let mut current = String::new();
    let mut prev_non_empty_outside_block: Option<&str> = None;
    let mut fence_open_line: usize = 0;

    for (line_index_zero, line) in markdown.lines().enumerate() {
        let line_number_1based = line_index_zero + 1;
        let trimmed_start = line.trim_start();
        if trimmed_start.starts_with("```") {
            let info = trimmed_start[3..].trim();
            if in_litex {
                if !skip_this_block {
                    let trimmed = current.trim();
                    if !trimmed.is_empty() {
                        blocks.push((fence_open_line, trimmed.to_string()));
                    }
                }
                current.clear();
                in_litex = false;
                skip_this_block = false;
                prev_non_empty_outside_block = None;
            } else if info == "litex" {
                in_litex = true;
                fence_open_line = line_number_1based;
                skip_this_block = prev_non_empty_outside_block == Some(SKIP_MARKER);
                current.clear();
            }
        } else if in_litex {
            if !skip_this_block {
                if !current.is_empty() {
                    current.push('\n');
                }
                current.push_str(line);
            }
        } else {
            let t = line.trim();
            if !t.is_empty() {
                prev_non_empty_outside_block = Some(t);
            }
        }
    }
    blocks
}

pub(super) fn collect_markdown_files_under_dir_sorted(root: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if !root.is_dir() {
        return out;
    }
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let read_dir = match fs::read_dir(dir) {
            Ok(entries) => entries,
            Err(_) => return,
        };
        for entry in read_dir.flatten() {
            let path = entry.path();
            let Ok(file_type) = entry.file_type() else {
                continue;
            };
            if file_type.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "md") {
                out.push(path);
            }
        }
    }
    walk(root, &mut out);
    out.sort();
    out
}

pub(super) fn litex_snippets_from_markdown_files(
    manifest_dir: &Path,
    md_paths: &[PathBuf],
) -> Vec<(String, String, String)> {
    let mut out: Vec<(String, String, String)> = Vec::new();
    for md_path in md_paths {
        let rel_label = md_path
            .strip_prefix(manifest_dir)
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
            out.push((
                format!(
                    "{} ```litex```#{} (md line {})",
                    rel_label, block_index, md_line
                ),
                block,
                md_current_path_str.clone(),
            ));
        }
    }
    out
}

/// All `*.lit` files under `manifest_dir/subdir`, recursively (e.g. `examples/subdir/foo.lit`).
/// Sorted by full path after collection. Empty if `subdir` is missing or has no `.lit` files.
pub(super) fn collect_lit_files_recursive_under(manifest_dir: &Path, subdir: &str) -> Vec<PathBuf> {
    collect_lit_files_recursive_under_excluding(manifest_dir, subdir, &[])
}

pub(super) fn collect_lit_files_recursive_under_excluding(
    manifest_dir: &Path,
    subdir: &str,
    excluded_subdirs: &[&str],
) -> Vec<PathBuf> {
    let dir_path = manifest_dir.join(subdir);
    if !dir_path.is_dir() {
        println!("--- {} {:?}: directory missing; skip ---", subdir, dir_path);
        return Vec::new();
    }
    let excluded_paths: Vec<PathBuf> = excluded_subdirs
        .iter()
        .map(|excluded_subdir| manifest_dir.join(excluded_subdir))
        .collect();
    fn walk(dir: &Path, excluded_paths: &[PathBuf], out: &mut Vec<PathBuf>) {
        let read_directory = match fs::read_dir(dir) {
            Ok(entries) => entries,
            Err(read_error) => panic!("failed to read {:?}: {}", dir, read_error),
        };
        for directory_entry_result in read_directory {
            let directory_entry = match directory_entry_result {
                Ok(entry) => entry,
                Err(read_error) => panic!("failed to read directory entry: {}", read_error),
            };
            let path = directory_entry.path();
            let Ok(file_type) = directory_entry.file_type() else {
                continue;
            };
            if file_type.is_dir() {
                if excluded_paths
                    .iter()
                    .any(|excluded_path| path == *excluded_path)
                {
                    continue;
                }
                walk(&path, excluded_paths, out);
            } else if path.extension().is_some_and(|ext| ext == "lit") {
                out.push(path);
            }
        }
    }
    let mut lit_file_paths = Vec::new();
    walk(&dir_path, excluded_paths.as_slice(), &mut lit_file_paths);
    lit_file_paths.sort();
    lit_file_paths
}

pub(super) fn print_slowest_run_labels(title: &str, run_durations_ms: &[(String, f64)]) {
    if run_durations_ms.is_empty() {
        return;
    }

    let mut sorted_runs = run_durations_ms.to_vec();
    sorted_runs.sort_by(|left, right| {
        right
            .1
            .partial_cmp(&left.1)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let count_to_print = SLOWEST_RUNS_TO_PRINT.min(sorted_runs.len());
    println!(
        "--- slowest {}: top {} of {} ---",
        title,
        count_to_print,
        sorted_runs.len()
    );
    for (index, (label, duration_ms)) in sorted_runs.iter().take(count_to_print).enumerate() {
        println!("  {:>2}. {:.2} ms  {}", index + 1, duration_ms, label);
    }
}
