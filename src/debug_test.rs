#[cfg(test)]
mod local_debug_tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::prelude::*;

    const LARGE_TEST_STACK_SIZE: usize = 16 * 1024 * 1024;
    const DEBUG_LIT_REL_PATH: &str = "tmp/debug.lit";

    #[derive(Clone)]
    struct DebugSnippet {
        label: String,
        source: String,
    }

    fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(LARGE_TEST_STACK_SIZE)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }

    // cargo test run_debug_snippets -- --ignored --nocapture
    // LITEX_DEBUG_FILE=tmp/other.lit cargo test run_debug_snippets -- --ignored --nocapture
    // LITEX_DEBUG_DETAIL_OUTPUT=1 cargo test run_debug_snippets -- --ignored --nocapture
    // LITEX_DEBUG_STOP_ON_FIRST_FAILURE=1 cargo test run_debug_snippets -- --ignored --nocapture
    #[test]
    #[ignore = "local debug helper; reads tmp/debug.lit"]
    fn run_debug_snippets() {
        run_with_large_stack("run_debug_snippets_large_stack", run_debug_snippets_impl);
    }

    fn run_debug_snippets_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let debug_lit_path = debug_lit_path(&manifest_dir);

        if !debug_lit_path.is_file() {
            println!(
                "--- run_debug_snippets: skip (missing {}) ---",
                debug_lit_path.display()
            );
            println!("  Put snippets in {}", debug_lit_path.display());
            println!("  Split snippets with lines like `# debug/name` or `# test/name`.");
            return;
        }

        let source_code = fs::read_to_string(&debug_lit_path).unwrap_or_else(|read_error| {
            panic!("failed to read {:?}: {}", debug_lit_path, read_error)
        });
        let snippets = split_debug_snippets(source_code.as_str());
        if snippets.is_empty() {
            println!(
                "--- run_debug_snippets: skip (empty {}) ---",
                DEBUG_LIT_REL_PATH
            );
            return;
        }

        let path_for_runtime = match debug_lit_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", debug_lit_path),
        };

        let builtin_start = Instant::now();
        let mut runtime = Runtime::new_with_builtin_code();
        let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
        runtime.new_file_path_new_env_new_name_scope(path_for_runtime);
        let detail_output = env_flag_is_set("LITEX_DEBUG_DETAIL_OUTPUT");
        runtime.detail_output = detail_output;
        let stop_on_first_failure = env_flag_is_set("LITEX_DEBUG_STOP_ON_FIRST_FAILURE");
        let keep_env_between_snippets = env_flag_is_set("LITEX_DEBUG_KEEP_ENV");

        let run_wall_start = Instant::now();
        let mut durations_ms: Vec<(String, f64)> = Vec::new();
        let mut failed_labels: Vec<String> = Vec::new();

        for (snippet_index, snippet) in snippets.iter().enumerate() {
            if snippet_index > 0 && !keep_env_between_snippets {
                runtime.clear_current_env_parse_name_scope_and_stop_imports();
                runtime.set_current_user_lit_file_path(path_for_runtime);
            }

            let normalized_source = remove_windows_carriage_return(snippet.source.as_str());
            let start_time = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), &mut runtime);
            let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            let status_label = if run_succeeded { "OK" } else { "FAILED" };

            println!(
                "=== [{}] {} ({:.2} ms) ===\n{}\n",
                status_label, snippet.label, duration_ms, run_output
            );

            durations_ms.push((snippet.label.clone(), duration_ms));
            if !run_succeeded {
                failed_labels.push(snippet.label.clone());
                if stop_on_first_failure {
                    break;
                }
            }
        }

        let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
        println!("--- debug snippets timing (summary) ---");
        println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
        println!(
            "  snippets: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
            durations_ms.len(),
            durations_ms
                .iter()
                .map(|(_, duration_ms)| duration_ms)
                .sum::<f64>(),
            run_wall_ms
        );
        print_debug_durations(durations_ms.as_slice());

        if failed_labels.is_empty() {
            println!("--- debug snippets: all OK ---");
            return;
        }

        println!("--- debug snippets failed labels ---");
        for label in failed_labels.iter() {
            println!("{}", label);
        }
        panic!(
            "debug snippet run failed for {} of {} item(s)",
            failed_labels.len(),
            durations_ms.len()
        );
    }

    fn split_debug_snippets(source_code: &str) -> Vec<DebugSnippet> {
        let mut snippets: Vec<DebugSnippet> = Vec::new();
        let mut current_lines: Vec<String> = Vec::new();
        let mut current_label: Option<String> = None;

        for line in source_code.lines() {
            if is_debug_snippet_marker(line) {
                push_current_debug_snippet(&mut snippets, &mut current_lines, &mut current_label);
                current_label = Some(line.trim().to_string());
            }

            if current_label.is_some() {
                current_lines.push(line.to_string());
            }
        }
        push_current_debug_snippet(&mut snippets, &mut current_lines, &mut current_label);

        if snippets.is_empty() {
            let trimmed = source_code.trim();
            if !trimmed.is_empty() {
                snippets.push(DebugSnippet {
                    label: format!("{} (whole file)", DEBUG_LIT_REL_PATH),
                    source: trimmed.to_string(),
                });
            }
        }

        snippets
    }

    fn debug_lit_path(manifest_dir: &PathBuf) -> PathBuf {
        match std::env::var("LITEX_DEBUG_FILE") {
            Ok(path) if !path.trim().is_empty() => {
                let path = PathBuf::from(path.trim());
                if path.is_absolute() {
                    path
                } else {
                    manifest_dir.join(path)
                }
            }
            _ => manifest_dir.join(DEBUG_LIT_REL_PATH),
        }
    }

    fn push_current_debug_snippet(
        snippets: &mut Vec<DebugSnippet>,
        current_lines: &mut Vec<String>,
        current_label: &mut Option<String>,
    ) {
        let Some(label) = current_label.take() else {
            return;
        };

        let body = current_lines.join("\n");
        current_lines.clear();
        if body.trim().is_empty() {
            return;
        }

        snippets.push(DebugSnippet {
            label,
            source: body,
        });
    }

    fn is_debug_snippet_marker(line: &str) -> bool {
        let trimmed = line.trim();
        trimmed.starts_with("# debug/") || trimmed.starts_with("# test/")
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

    fn print_debug_durations(durations_ms: &[(String, f64)]) {
        let mut sorted = durations_ms.to_vec();
        sorted.sort_by(|(_, a), (_, b)| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));

        println!("--- slowest debug snippets ---");
        for (index, (label, duration_ms)) in sorted.iter().take(10).enumerate() {
            println!("  {:>2}. {:.2} ms  {}", index + 1, duration_ms, label);
        }
    }
}
