use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;

const LARGE_TEST_STACK_SIZE: usize = 16 * 1024 * 1024;
const SLOWEST_RUNS_TO_PRINT: usize = 10;
pub(super) const THE_MECHANICS_SUBDIR: &str = "scripts/The-Mechanics-of-Litex-Proof";
pub(super) const CITE_STD_EXAMPLES_SUBDIR: &str = "examples/_internal/std_imports";

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

pub(super) fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(LARGE_TEST_STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

pub(super) fn the_mechanics_dir(manifest_dir: &Path) -> PathBuf {
    manifest_dir.join(THE_MECHANICS_SUBDIR)
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

pub(super) fn run_single_the_mechanics_chapter_markdown_file_impl(
    chapter_filename: &str,
    chapter_label: &str,
) {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let chapter_path = the_mechanics_dir(&manifest_dir).join(chapter_filename);
    assert!(
        chapter_path.is_file(),
        "{} markdown file must exist at {:?}",
        chapter_label,
        chapter_path
    );

    let snippets = litex_snippets_from_markdown_files(&manifest_dir, &[chapter_path.clone()]);
    assert!(
        !snippets.is_empty(),
        "{} markdown file must contain ```litex``` blocks",
        chapter_label
    );

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(snippets[0].2.as_str());

    let mut snippet_durations_ms: Vec<(String, f64)> = Vec::new();
    let wall_start = Instant::now();
    for (snippet_index, (label, source_code, md_path_for_run_file)) in snippets.iter().enumerate() {
        if snippet_index > 0 {
            runtime.clear_current_env_and_parse_name_scope();
            runtime.set_current_user_lit_file_path(md_path_for_run_file.as_str());
        }

        let normalized_source = remove_windows_carriage_return(source_code);
        let start_snippet = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
        let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;

        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        if !run_succeeded {
            panic!(
                "{} markdown litex snippet FAILED:\n{}\n>>> FAILED snippet (open .md here): {}\n",
                chapter_label, run_output, label
            );
        }

        snippet_durations_ms.push((label.clone(), duration_ms));
    }

    println!(
        "--- {} markdown: {} ```litex``` block(s), all OK ({:.2} ms wall) ---",
        chapter_label,
        snippets.len(),
        wall_start.elapsed().as_secs_f64() * 1000.0
    );
    print_slowest_run_labels(
        format!("{} markdown snippets", chapter_label).as_str(),
        snippet_durations_ms.as_slice(),
    );
    for (label, duration_ms) in snippet_durations_ms.iter() {
        println!("  OK  {:.2} ms  {}", duration_ms, label);
    }
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
