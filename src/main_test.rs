#[cfg(test)]
mod lit_file_runner_tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::Instant;

    use crate::pipeline::{render_run_source_code_output, run_source_code};
    use crate::prelude::*;

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

    #[test]
    fn run_tmp() {
        let tmp_lit_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        assert!(
            tmp_lit_path.is_file(),
            "examples/tmp.lit must exist at {:?}",
            tmp_lit_path
        );

        let tmp_lit_content = match fs::read_to_string(&tmp_lit_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", tmp_lit_path, read_error),
        };
        if tmp_lit_content.trim().is_empty() {
            println!("examples/tmp.lit is empty; skip run_tmp");
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
    }

    #[test]
    fn run_file_from_path() {
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
        assert!(run_succeeded, "Litex file failed: {}", path_str);
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
    }

    #[test]
    fn run_examples() {
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

            if !run_succeeded {
                panic!(
                    "docs litex snippet FAILED:\n{}\n>>> FAILED snippet (open .md here): {}\n",
                    run_output, label
                );
            }

            doc_durations_ms.push((label.clone(), duration_ms));
        }
        let docs_phase_wall_ms = docs_wall_start.elapsed().as_secs_f64() * 1000.0;

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
}
