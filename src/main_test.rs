#[cfg(test)]
mod lit_file_runner_tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::Instant;

    use crate::pipeline::{render_run_source_code_output, run_source_code};
    use crate::prelude::*;

    const LARGE_TEST_STACK_SIZE: usize = 16 * 1024 * 1024;
    const SLOWEST_RUNS_TO_PRINT: usize = 10;

    fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(LARGE_TEST_STACK_SIZE)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }

    /// Collect ```litex``` bodies. A block is omitted when the last non-empty line before its opening
    /// fence is exactly `<!-- litex:skip-test -->` (for snippets that are illustrative only).
    /// The line number is 1-based: the markdown line where the opening ` ```litex ` fence starts.
    fn extract_litex_fenced_blocks(markdown: &str) -> Vec<(usize, String)> {
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

    fn collect_markdown_files_under_dir_sorted(root: &Path) -> Vec<PathBuf> {
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

    fn litex_snippets_from_markdown_files(
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

    fn run_single_the_mechanics_chapter_markdown_file_impl(
        chapter_filename: &str,
        chapter_label: &str,
    ) {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let chapter_path = manifest_dir
            .join("The-Mechanics-of-Litex-Proof")
            .join(chapter_filename);
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
        for (snippet_index, (label, source_code, md_path_for_run_file)) in
            snippets.iter().enumerate()
        {
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

    fn run_tmp_lit_file(file_name: &str) {
        let tmp_lit_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(file_name);

        assert!(
            tmp_lit_path.is_file(),
            "examples/{} must exist at {:?}",
            file_name,
            tmp_lit_path
        );

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

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(path_str);
        let normalized_source = remove_windows_carriage_return(tmp_lit_content.as_str());

        let start_time = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
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

    #[test]
    fn run_tmp0() {
        run_tmp_lit_file("tmp.lit");
    }

    #[test]
    fn run_tmp2() {
        run_tmp_lit_file("tmp2.lit");
    }

    #[test]
    fn run_tmp3() {
        run_tmp_lit_file("tmp3.lit");
    }

    #[test]
    fn list_set_membership_implies_equality_or() {
        let source_code = r#"
forall a set:
    a = 1 or a = 2 or a = 3
    =>:
        a $in {1, 2, 3}
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("list_set_membership_implies_equality_or");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "list_set_membership_implies_equality_or failed:\n{}",
            run_output
        );
    }

    #[test]
    fn citation_verified_by_type_reflects_cited_stmt_kind() {
        let source_code = r#"
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
let a R:
    a = 1
a = 1
prop q(x R):
    x = 1
$q(1)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "citation_verified_by_type_reflects_cited_stmt_kind",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "citation_verified_by_type_reflects_cited_stmt_kind failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"cite forall fact\""));
        assert!(run_output.contains("\"type\": \"cite atomic fact\""));
        assert!(run_output.contains("\"type\": \"cite prop def\""));
    }

    #[test]
    fn run_file_from_path() {
        run_with_large_stack("run_file_from_path_large_stack", run_file_from_path_impl);
    }

    fn run_file_from_path_impl() {
        let path: String = "./examples/chapter_6_induction.lit".to_string();
        let file_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        assert!(
            file_path.is_absolute(),
            "path must be an absolute path: {:?}",
            file_path
        );
        assert!(
            file_path.is_file(),
            "path must point to a file: {:?}",
            file_path
        );

        let source_code = match fs::read_to_string(&file_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", file_path, read_error),
        };
        let path_str = match file_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", file_path),
        };

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(path_str);
        let normalized_source = remove_windows_carriage_return(source_code.as_str());

        let start_time = Instant::now();
        let (stmt_results, runtime_error) =
            run_source_code(normalized_source.as_str(), &mut runtime);
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
            "Litex file failed: {}\n\n>>> Litex error JSON:\n{}\n\n=== [{}] {:?} ({:.2} ms user file only) ===",
            path_str, error_json, path_str, status_label, duration_ms
        );
    }

    #[test]
    fn run_the_mechanics_markdown_files() {
        run_with_large_stack(
            "run_the_mechanics_markdown_files_large_stack",
            run_the_mechanics_markdown_files_impl,
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
    fn run_the_mechanics_chapter_7_markdown_file() {
        run_with_large_stack(
            "run_the_mechanics_chapter_7_markdown_file_large_stack",
            run_the_mechanics_chapter_7_markdown_file_impl,
        );
    }

    fn run_the_mechanics_chapter_7_markdown_file_impl() {
        run_single_the_mechanics_chapter_markdown_file_impl(
            "Chapter_7_Number_Theory.md",
            "Chapter 7",
        );
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
        run_single_the_mechanics_chapter_markdown_file_impl(
            "Chapter_10_Relations.md",
            "Chapter 10",
        );
    }

    fn run_the_mechanics_markdown_files_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mechanics_dir = manifest_dir.join("The-Mechanics-of-Litex-Proof");
        assert!(
            mechanics_dir.is_dir(),
            "The-Mechanics-of-Litex-Proof must exist at {:?}",
            mechanics_dir
        );

        let md_paths = collect_markdown_files_under_dir_sorted(&mechanics_dir);
        assert!(
            !md_paths.is_empty(),
            "The-Mechanics-of-Litex-Proof must contain markdown files"
        );

        let snippets = litex_snippets_from_markdown_files(&manifest_dir, &md_paths);
        assert!(
            !snippets.is_empty(),
            "The-Mechanics-of-Litex-Proof markdown files must contain ```litex``` blocks"
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(snippets[0].2.as_str());

        let mut snippet_durations_ms: Vec<(String, f64)> = Vec::new();
        let wall_start = Instant::now();
        for (snippet_index, (label, source_code, md_path_for_run_file)) in
            snippets.iter().enumerate()
        {
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
                    "The-Mechanics-of-Litex-Proof markdown litex snippet FAILED:\n{}\n>>> FAILED snippet (open .md here): {}\n",
                    run_output, label
                );
            }

            snippet_durations_ms.push((label.clone(), duration_ms));
        }

        println!(
            "--- The-Mechanics-of-Litex-Proof markdown: {} ```litex``` block(s) in {} markdown file(s), all OK ({:.2} ms wall) ---",
            snippets.len(),
            md_paths.len(),
            wall_start.elapsed().as_secs_f64() * 1000.0
        );
        for (label, duration_ms) in snippet_durations_ms.iter() {
            println!("  OK  {:.2} ms  {}", duration_ms, label);
        }
    }

    /// All `*.lit` files under `manifest_dir/subdir`, recursively (e.g. `examples/subdir/foo.lit`).
    /// Sorted by full path after collection. Empty if `subdir` is missing or has no `.lit` files.
    fn collect_lit_files_recursive_under(manifest_dir: &Path, subdir: &str) -> Vec<PathBuf> {
        let dir_path = manifest_dir.join(subdir);
        if !dir_path.is_dir() {
            println!("--- {} {:?}: directory missing; skip ---", subdir, dir_path);
            return Vec::new();
        }
        fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
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
                    walk(&path, out);
                } else if path.extension().is_some_and(|ext| ext == "lit") {
                    out.push(path);
                }
            }
        }
        let mut lit_file_paths = Vec::new();
        walk(&dir_path, &mut lit_file_paths);
        lit_file_paths.sort();
        lit_file_paths
    }

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
                "  phase 1 (examples/*.lit + docs/Manual ```litex```): sum of runs: {:.2} ms  |  wall: {:.2} ms",
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

    fn print_slowest_run_labels(title: &str, run_durations_ms: &[(String, f64)]) {
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

    #[test]
    fn run_examples() {
        run_with_large_stack("run_examples_large_stack", run_examples_impl);
    }

    fn run_examples_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lit_file_paths = collect_lit_files_recursive_under(&manifest_dir, "examples");

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
            println!("--- phase 1: no examples/*.lit and no docs/Manual ```litex``` snippets ---");
        } else {
            examples_ran = true;
            let examples_wall_start = Instant::now();
            let first_path = phase1_items[0].path_for_runtime.as_str();
            runtime.new_file_path_new_env_new_name_scope(first_path);

            for (item_index, item) in phase1_items.iter().enumerate() {
                if item_index > 0 {
                    runtime.clear_current_env_and_parse_name_scope();
                    runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
                }

                let normalized_source = remove_windows_carriage_return(item.source.as_str());

                let start_time_for_one_file = Instant::now();
                let (stmt_results, runtime_error) =
                    run_source_code(normalized_source.as_str(), &mut runtime);
                let duration_ms_for_one_file =
                    start_time_for_one_file.elapsed().as_secs_f64() * 1000.0;

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
        }

        if every_file_run_ok && examples_ran {
            println!(
                "--- phase 1: {} run(s) (examples/*.lit + docs/Manual ```litex```), all OK ---",
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

    #[test]
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
                "gsm8k jsonl file must exist at {:?}",
                jsonl_path
            );
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
            runtime.clear_current_env_and_parse_name_scope();
            runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
        }

        for (line_index, line) in jsonl_content.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }

            if *total_count > 0 || line_index > 0 {
                runtime.clear_current_env_and_parse_name_scope();
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
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), runtime);
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
    fn run_metamathqa_litex_solutions() {
        run_with_large_stack(
            "run_metamathqa_litex_solutions_large_stack",
            run_metamathqa_litex_solutions_impl,
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
                runtime.clear_current_env_and_parse_name_scope();
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
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), runtime);
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
                    let decoded = char::from_u32(code)
                        .ok_or_else(|| format!("invalid JSON unicode code point: {}", hex))?;
                    result.push(decoded);
                }
                other => return Err(format!("unknown JSON escape: \\{}", other)),
            }
        }

        Err("unterminated JSON string".to_string())
    }
}
