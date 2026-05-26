// cargo test run_examples -- --nocapture
// cargo test run_the_mechanics_markdown_files -- --nocapture
// cargo test run_all -- --nocapture

#[cfg(test)]
mod lit_file_runner_tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::Instant;

    use crate::pipeline::{render_run_source_code_output, run_source_code};
    use crate::prelude::*;

    const LARGE_TEST_STACK_SIZE: usize = 16 * 1024 * 1024;
    const SLOWEST_RUNS_TO_PRINT: usize = 10;
    const THE_MECHANICS_SUBDIR: &str = "scripts/The-Mechanics-of-Litex-Proof";

    fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(LARGE_TEST_STACK_SIZE)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }

    fn the_mechanics_dir(manifest_dir: &Path) -> PathBuf {
        manifest_dir.join(THE_MECHANICS_SUBDIR)
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
    fn run_tmp4() {
        run_tmp_lit_file("tmp4.lit");
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
    fn dependent_fn_param_set_uses_previous_arg() {
        let source_code = r#"
have f fn(n N_pos, x closed_range(1, n)) R
f(3, 2) = f(3, 2)
by fn as set: f
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("dependent_fn_param_set_uses_previous_arg");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "dependent_fn_param_set_uses_previous_arg failed:\n{}",
            run_output
        );
    }

    #[test]
    fn fn_return_set_cannot_depend_on_params() {
        let source_code = r#"
have f fn(n N_pos) closed_range(1, n)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("fn_return_set_cannot_depend_on_params");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "dependent return set should fail, but succeeded:\n{}",
            run_output
        );
        assert!(
            run_output.contains("function return set cannot depend on function parameters [n]"),
            "dependent return set failure had unexpected output:\n{}",
            run_output
        );
    }

    #[test]
    fn known_equality_implies_weak_order() {
        let source_code = r#"
have a, b R
know a = b
a <= b
a >= b
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("known_equality_implies_weak_order");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "known_equality_implies_weak_order failed:\n{}",
            run_output
        );
    }

    #[test]
    fn eval_recursive_algo_memoizes_overlapping_calls() {
        run_with_large_stack(
            "eval_recursive_algo_memoizes_overlapping_calls_large_stack",
            || {
                let source_code = r#"
prove:
    have fib fn(x R) R

    know:
        forall x R:
            x = 0
            =>:
                fib(x) = 0

        forall x R:
            x = 1
            =>:
                fib(x) = 1

        forall x R:
            x > 1
            =>:
                fib(x) = fib(x - 1) + fib(x - 2)

    algo fib(x):
        case x = 0: 0
        case x = 1: 1
        fib(x - 1) + fib(x - 2)

    eval fib(25)
    fib(25) = 75025
"#;

                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope(
                    "eval_recursive_algo_memoizes_overlapping_calls",
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(
                    run_succeeded,
                    "eval_recursive_algo_memoizes_overlapping_calls failed:\n{}",
                    run_output
                );
            },
        );
    }

    #[test]
    fn pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined() {
        let source_code = r#"
have fn sqrt(x R: x >= 0) R = x^(1/2)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined failed:\n{}",
            run_output
        );
    }

    #[test]
    fn sqrt_core_builtin_rules() {
        let source_code = r#"
sqrt(0) = 0
sqrt(1) = 1
sqrt(4) = 2
sqrt(452) = sqrt(4 * 113)
sqrt(452) = sqrt(4 * 113) = sqrt(4) * sqrt(113) = 2 * sqrt(113)
sqrt(2) $in R
sqrt(3) / 2 $in R

forall x R:
    x >= 0
    =>:
        (sqrt(x))^2 = x

forall x R:
    x > 0
    =>:
        sqrt(x) > 0

forall x, a, b R:
    x >= 0
    a >= 0
    b >= 0
    x = a * b
    =>:
        sqrt(x) = sqrt(a) * sqrt(b)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("sqrt_core_builtin_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "sqrt_core_builtin_rules failed:\n{}",
            run_output
        );
    }

    #[test]
    fn direct_calculation_equality_is_reported_before_weak_order_fallback() {
        let source_code = "(-1 * sqrt (2)) ^ 2 = 2";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "direct_calculation_equality_is_reported_before_weak_order_fallback",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "direct_calculation_equality_is_reported_before_weak_order_fallback failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"rule\": \"calculation\""));
        assert!(!run_output.contains("\"rule\": \"equality from a >= b and b >= a\""));
    }

    #[test]
    fn known_equality_candidate_uses_rational_expression_simplification() {
        let source_code = r#"
forall a, b R:
    a^2 + a * a + b = 0
    =>:
        0 = 2 * a^2 + b
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "known_equality_candidate_uses_rational_expression_simplification",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "known_equality_candidate_uses_rational_expression_simplification failed:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\"rule\": \"calculation and rational expression simplification\"")
        );
    }

    #[test]
    fn quotient_nonzero_from_numerator_nonzero_builtin_rule() {
        let source_code = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
        0 != a / b
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "quotient_nonzero_from_numerator_nonzero_builtin_rule",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "quotient_nonzero_from_numerator_nonzero_builtin_rule failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"rule\": \"div_not_equal_zero_from_numerator_nonzero\""));
    }

    #[test]
    fn known_obj_values_store_simplified_fraction_for_nonfinite_decimal() {
        let source_code = r#"
have a R
know a = 1 / 2 / 3

have b R
know b = 1 / 2

have c R
know c = 2 / -6

have d R
know d = 1 / (2 / 3 * 4)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "known_obj_values_store_simplified_fraction_for_nonfinite_decimal",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "known_obj_values_store_simplified_fraction_for_nonfinite_decimal failed:\n{}",
            run_output
        );

        let env = runtime.environment_stack.last().expect("top environment");
        match env.known_obj_values.get("a") {
            Some(KnownObjValue::SimplifiedFraction(div)) => {
                assert_eq!(div.left.to_string(), "1");
                assert_eq!(div.right.to_string(), "6");
            }
            other => panic!(
                "expected a to store SimplifiedFraction(1 / 6), got {:?}",
                other.map(|_| "other value")
            ),
        }
        match env.known_obj_values.get("b") {
            Some(KnownObjValue::SimplifiedNumber(number)) => {
                assert_eq!(number.normalized_value, "0.5");
            }
            other => panic!(
                "expected b to store SimplifiedNumber(0.5), got {:?}",
                other.map(|_| "other value")
            ),
        }
        match env.known_obj_values.get("c") {
            Some(KnownObjValue::SimplifiedFraction(div)) => {
                assert_eq!(div.left.to_string(), "-1");
                assert_eq!(div.right.to_string(), "3");
            }
            other => panic!(
                "expected c to store SimplifiedFraction(-1 / 3), got {:?}",
                other.map(|_| "other value")
            ),
        }
        match env.known_obj_values.get("d") {
            Some(KnownObjValue::SimplifiedNumber(number)) => {
                assert_eq!(number.normalized_value, "0.375");
            }
            other => panic!(
                "expected d to store SimplifiedNumber(0.375), got {:?}",
                other.map(|_| "other value")
            ),
        }
    }

    #[test]
    fn simplified_fraction_known_value_is_used_by_resolve() {
        let source_code = r#"
forall a R:
    a = 1 / 2 / 3
    =>:
        a + 1 / 6 = 1 / 3

forall a R:
    a = 2 / -6
    =>:
        a = -1 / 3

forall a R:
    a = 1 / (2 / 3)
    =>:
        a = 3 / 2

forall a R:
    a = 1 / (2 / 3 * 4)
    =>:
        a = 3 / 8
        a + 1 = 11 / 8
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "simplified_fraction_known_value_is_used_by_resolve",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "simplified_fraction_known_value_is_used_by_resolve failed:\n{}",
            run_output
        );
    }

    #[test]
    fn real_interval_membership_rules() {
        let source_code = r#"
have I set = oo(0, 1)

have a R
know a $in oo(0, 1)
a $in R
0 < a
a < 1

have b R
know b $in oc(0, 1)
0 < b
b <= 1

have c R
know c $in co(0, 1)
0 <= c
c < 1

have d R
know d $in cc(0, 1)
0 <= d
d <= 1

have e R
know e $in info(1)
e $in R
e < 1

have f R
know f $in infc(1)
f $in R
f <= 1

have g R
know g $in oinf(0)
g $in R
0 < g

have h R
know h $in cinf(0)
h $in R
0 <= h

have x R
know:
    0 < x
    x <= 1
x $in oc(0, 1)

have y R
know:
    0 <= y
y $in cinf(0)

have phi fn(t oo(0, 1)) R
phi(a) $in R
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("real_interval_membership_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "real_interval_membership_rules failed:\n{}",
            run_output
        );
    }

    #[test]
    fn real_interval_nonempty_and_well_defined_rules() {
        let source_code = r#"
have empty_like set = cc(1, 0)

have a, b R
know:
    a <= b
    a < b

$is_nonempty_set(cc(a, b))
$is_nonempty_set(oo(a, b))
$is_nonempty_set(oc(a, b))
$is_nonempty_set(co(a, b))
$is_nonempty_set(info(a))
$is_nonempty_set(infc(a))
$is_nonempty_set(oinf(a))
$is_nonempty_set(cinf(a))

have x cc(a, b)
x $in cc(a, b)

have y oo(a, b)
y $in oo(a, b)

have left cinf(a)
left $in cinf(a)

have right info(a)
right $in info(a)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("real_interval_nonempty_and_well_defined_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "real_interval_nonempty_and_well_defined_rules failed:\n{}",
            run_output
        );
    }

    #[test]
    fn one_side_infinity_interval_parse_arity_errors() {
        for source_code in ["have bad set = info()", "have bad set = info(0, 1)"] {
            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "one_side_infinity_interval_parse_arity_errors",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(!run_succeeded);
            assert!(
                run_output.contains("info expects 1 argument"),
                "unexpected arity error output:\n{}",
                run_output
            );
        }
    }

    #[test]
    fn typed_function_applications_return_real() {
        let source_code = r#"
run_file trigonometry

sin(0) $in R
cos(pi / 3) $in R
arcsin(1 / 2) $in R
arctan(sqrt(3)) $in R
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("typed_function_applications_return_real");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "typed_function_applications_return_real failed:\n{}",
            run_output
        );
    }

    #[test]
    fn template_instantiation_prefers_angle_brackets() {
        let source_code = r#"
template id_on_set<s set: s = s>:
    have id_on_set set = s

\id_on_set<R> = R
\id_on_set{R} = R
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("template_instantiation_prefers_angle_brackets");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "template_instantiation_prefers_angle_brackets failed:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\\id_on_set<R> = R"),
            "template instantiation display should use angle brackets:\n{}",
            run_output
        );
    }

    #[test]
    fn weak_order_does_not_recursively_prove_equality() {
        let source_code = r#"
have a, b R
know a <= b
a = b
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("weak_order_does_not_recursively_prove_equality");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "recursive equality/order proof should fail, but succeeded:\n{}",
            run_output
        );
    }

    #[test]
    fn zero_product_cancellation_does_not_recursively_reenter_equality() {
        let source_code = r#"
have a, b, k1, k2 N
know:
    k1 = 0
    b = a * k1
b = a * k1 = a * 0 = 0
0 * k2 = 0
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "zero_product_cancellation_does_not_recursively_reenter_equality",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "zero-product cancellation recursion regression failed:\n{}",
            run_output
        );
    }

    #[test]
    fn exist_unique_infers_component_uniqueness_forall() {
        let source_code = r#"
abstract_prop p(a, b)
know exist! a, b R st {$p(a, b)}
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "exist_unique_infers_component_uniqueness_forall",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

        assert!(
            run_succeeded,
            "exist! component uniqueness inference failed:\n{}",
            run_output
        );
        assert!(
            run_output.contains("forall a1, b1 R, a2, b2 R:")
                && run_output.contains("a1 = a2 and b1 = b2"),
            "exist! should infer a component-wise uniqueness forall:\n{}",
            run_output
        );
    }

    #[test]
    fn exist_unique_component_uniqueness_proves_split_then_facts() {
        let source_code = r#"
abstract_prop p(a, b)
know exist! a, b R st {$p(a, b)}
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2
        b1 = b2
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "exist_unique_component_uniqueness_proves_split_then_facts",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "component uniqueness from exist! should prove split then-facts:\n{}",
            run_output
        );
    }

    #[test]
    fn exist_unique_still_accepts_tuple_uniqueness_forall() {
        let source_code = r#"
prove:
    abstract_prop p(a, b)
    know:
        exist a, b R st {$p(a, b)}
        forall a1, b1, a2, b2 R:
            $p(a1, b1)
            $p(a2, b2)
            =>:
                (a1, b1) = (a2, b2)
    exist! a, b R st {$p(a, b)}
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "exist_unique_still_accepts_tuple_uniqueness_forall",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "tuple-style uniqueness should still prove exist!:\n{}",
            run_output
        );
    }

    #[test]
    fn hidden_file_path_output_omits_source_fields() {
        let source_code = "x = 1";
        let path = "/private/tmp/litex-hidden-source-test.lit";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(path);
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(!run_output.contains("\"source\""));
        assert!(!run_output.contains(path));
        assert!(run_output.contains("\"line\": 1"));
    }

    #[test]
    fn normal_output_omits_empty_arrays_and_empty_strings() {
        let source_code = "1 = 1\n1 = 2";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("normal_output_omits_empty_fields");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(!run_output.contains("\"infer_facts\": []"));
        assert!(!run_output.contains("\"inside_results\": []"));
        assert!(!run_output.contains("\"message\": \"\""));
    }

    #[test]
    fn detail_output_keeps_empty_arrays_and_empty_strings() {
        let source_code = "1 = 1\n1 = 2";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("detail_output_keeps_empty_fields");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(run_output.contains("\"infer_facts\": []"));
        assert!(run_output.contains("\"inside_results\": []"));
        assert!(run_output.contains("\"message\": \"\""));
    }

    #[test]
    fn builtin_citation_source_uses_safe_builtin_label() {
        let source_code = "have a, b R\na < b or a = b or a > b";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("builtin_citation_source");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "builtin citation run failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"source_kind\": \"builtin\""));
        assert!(run_output.contains("\"source\": \"builtin_code\""));
        assert!(!run_output.contains("\"path\""));
    }

    #[test]
    fn std_citation_source_uses_safe_module_label() {
        let source_code = "run_file trigonometry\nsin(0) = 0";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("std_citation_source");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(run_succeeded, "std citation run failed:\n{}", run_output);
        assert!(run_output.contains("\"source_kind\": \"std\""));
        assert!(run_output.contains("\"source\": \"std/trigonometry\""));
        assert!(!run_output.contains("\"path\""));
    }

    #[test]
    fn run_file_citation_source_uses_safe_label_and_detail_path() {
        let run_file_path = std::env::temp_dir().join("litex-run-file-citation-source-test.lit");
        fs::write(
            &run_file_path,
            "abstract_prop p(x)\nknow forall x R:\n    $p(x)\n",
        )
        .unwrap();
        let run_file_path_string = run_file_path.to_string_lossy().into_owned();
        let source_code = format!("run_file \"{}\"\n$p(2)", run_file_path_string);

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("run_file_citation_source");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "run_file citation run failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"source_kind\": \"run_file\""));
        assert!(run_output.contains("\"source\": \"external_file\""));
        assert!(!run_output.contains(run_file_path_string.as_str()));

        let mut detail_runtime = Runtime::new_with_builtin_code();
        detail_runtime.new_file_path_new_env_new_name_scope("run_file_citation_source");
        detail_runtime.detail_output = true;
        let (detail_stmt_results, detail_runtime_error) =
            run_source_code(source_code.as_str(), &mut detail_runtime);
        let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
            &detail_runtime,
            &detail_stmt_results,
            &detail_runtime_error,
            false,
        );

        let _ = fs::remove_file(&run_file_path);
        assert!(
            detail_run_succeeded,
            "detail run_file citation run failed:\n{}",
            detail_run_output
        );
        assert!(detail_run_output.contains("\"path\""));
        assert!(detail_run_output.contains(run_file_path_string.as_str()));
    }

    #[test]
    fn harness_success_has_done_action() {
        let (ok, output) = run_harness_for_code("1 + 1 = 2", "-harness-test", true);

        assert!(ok, "harness success run failed:\n{}", output);
        assert!(output.contains("\"harness\": \"litex-agent-harness\""));
        assert!(output.contains("\"result\": \"success\""));
        assert!(output.contains("\"proof_debt_know_statements\": 0"));
        assert!(output.contains("\"next_action\": \"done\""));
    }

    #[test]
    fn harness_unknown_failure_suggests_intermediate_fact() {
        let (ok, output) = run_harness_for_code("1 = 0", "-harness-test", true);

        assert!(!ok, "harness unknown run should fail:\n{}", output);
        assert!(output.contains("\"result\": \"error\""));
        assert!(output.contains("\"error_type\": \"VerifyError\""));
        assert!(output.contains("\"error_type\": \"UnknownError\""));
        assert!(output.contains("\"next_action\": \"add_intermediate_fact\""));
    }

    #[test]
    fn harness_counts_know_as_proof_debt() {
        let (ok, output) = run_harness_for_code("know 1 = 0", "-harness-test", true);

        assert!(!ok, "harness proof debt run should fail:\n{}", output);
        assert!(output.contains("\"proof_debt_know_statements\": 1"));
        assert!(output.contains("\"next_action\": \"reduce_proof_debt\""));
    }

    #[test]
    fn hidden_file_path_run_file_output_omits_run_file_path() {
        let run_file_path = std::env::temp_dir().join("litex-hidden-run-file-test.lit");
        fs::write(&run_file_path, "1 = 1\n").unwrap();
        let run_file_path_string = run_file_path.to_string_lossy().into_owned();
        let source_code = format!("run_file \"{}\"", run_file_path_string);

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        let _ = fs::remove_file(&run_file_path);
        assert!(run_succeeded, "run_file failed:\n{}", run_output);
        assert!(run_output.contains("\"stmt\": \"run_file\""));
        assert!(!run_output.contains(run_file_path_string.as_str()));
        assert!(!run_output.contains("\"source\""));
    }

    #[test]
    fn run_file_read_error_hides_path_unless_detail_output() {
        let run_file_path = std::env::temp_dir().join("litex-missing-run-file-output-test.lit");
        let _ = fs::remove_file(&run_file_path);
        let run_file_path_string = run_file_path.to_string_lossy().into_owned();
        let source_code = format!("run_file \"{}\"", run_file_path_string);

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(run_output.contains("Failed to read file: external_file"));
        assert!(!run_output.contains(run_file_path_string.as_str()));

        let mut detail_runtime = Runtime::new_with_builtin_code();
        detail_runtime.new_file_path_new_env_new_name_scope("repl");
        detail_runtime.detail_output = true;
        let (detail_stmt_results, detail_runtime_error) =
            run_source_code(source_code.as_str(), &mut detail_runtime);
        let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
            &detail_runtime,
            &detail_stmt_results,
            &detail_runtime_error,
            false,
        );

        assert!(!detail_run_succeeded);
        assert!(detail_run_output.contains(run_file_path_string.as_str()));
    }

    #[test]
    fn std_run_file_error_hides_attempted_paths_unless_detail_output() {
        let missing_std_module = "__missing_std_module_for_output_test__";
        let source_code = format!("run_file {}", missing_std_module);

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(run_output.contains(
            format!(
                "Failed to find std run_file target `{}`",
                missing_std_module
            )
            .as_str()
        ));
        assert!(!run_output.contains("Tried:"));

        let mut detail_runtime = Runtime::new_with_builtin_code();
        detail_runtime.new_file_path_new_env_new_name_scope("repl");
        detail_runtime.detail_output = true;
        let (detail_stmt_results, detail_runtime_error) =
            run_source_code(source_code.as_str(), &mut detail_runtime);
        let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
            &detail_runtime,
            &detail_stmt_results,
            &detail_runtime_error,
            false,
        );

        assert!(!detail_run_succeeded);
        assert!(detail_run_output.contains("Tried:"));
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
    fn definition_namespaces_allow_same_spelling_across_kinds() {
        let source_code = r#"
have fn SharedName(x R) R = 1
algo SharedName(x):
    1
prop SharedName(x R)
struct SharedName:
    value R
    other R
template SharedName<s set>:
    have SharedName set = s
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "definition_namespaces_allow_same_spelling_across_kinds",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "same spelling across independent definition namespaces failed:\n{}",
            run_output
        );
    }

    #[test]
    fn duplicate_definition_names_fail_in_their_namespace() {
        let cases = [
            ("prop", "prop dup_prop(x R)\nprop dup_prop(x R)"),
            (
                "abstract_prop",
                "abstract_prop dup_abstract(x)\nabstract_prop dup_abstract(x)",
            ),
            (
                "abstract_prop after prop",
                "prop dup_predicate(x R)\nabstract_prop dup_predicate(x)",
            ),
            (
                "prop after abstract_prop",
                "abstract_prop dup_predicate2(x)\nprop dup_predicate2(x R)",
            ),
            (
                "struct",
                "struct DupStruct:\n    value R\n    other R\nstruct DupStruct:\n    value R\n    other R",
            ),
            (
                "template",
                "template DupTemplate<s set>:\n    have DupTemplate set = s\ntemplate DupTemplate<s set>:\n    have DupTemplate set = s",
            ),
            (
                "algo",
                "have fn dup_algo(x R) R = 1\nalgo dup_algo(x):\n    1\nalgo dup_algo(x):\n    1",
            ),
            (
                "auto algo",
                "have fn as algo dup_auto_algo(x R) R = 1\nalgo dup_auto_algo(x):\n    1",
            ),
        ];

        for (label, source_code) in cases {
            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                format!("duplicate_definition_names_{}", label).as_str(),
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "duplicate {} definition should fail, but succeeded:\n{}",
                label, run_output
            );
            assert!(
                run_output.contains("NameAlreadyUsedError"),
                "duplicate {} definition should report NameAlreadyUsedError:\n{}",
                label,
                run_output
            );
        }
    }

    #[test]
    fn have_fn_as_algo_rejects_non_atomic_case_condition() {
        let source_code = "\
have fn as algo bad_algo_case(x, y R) R by cases:
    case x = 0 and y = 0: 0";
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("have_fn_as_algo_non_atomic_case");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "non-atomic generated algo case should fail, but succeeded:\n{}",
            run_output
        );
        assert!(
            run_output.contains("generated algo case")
                && run_output.contains("currently require atomic case conditions"),
            "non-atomic generated algo case should report a targeted error:\n{}",
            run_output
        );
    }

    #[test]
    fn run_file_from_path() {
        run_with_large_stack("run_file_from_path_large_stack", run_file_from_path_impl);
    }

    #[test]
    fn run_file_in_std_from_folder_name() {
        run_with_large_stack(
            "run_file_in_std_from_folder_name_large_stack",
            run_file_in_std_from_folder_name_impl,
        );
    }

    fn run_file_in_std_from_folder_name_impl() {
        let source_code = "run_file trigonometry\n\nsin(0) = 0\ncos(0) = 1";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(run_succeeded, "run_file in std failed:\n{}", run_output);
        assert!(run_output.contains("\"type\": \"RunFileInStd\""));
        assert!(run_output.contains("\"stmt\": \"run_file trigonometry\""));
        assert!(run_output.contains("\"stmt\": \"sin(0) = 0\""));
        assert!(run_output.contains("\"stmt\": \"cos(0) = 1\""));
    }

    fn run_file_from_path_impl() {
        let path: String = "./examples/strong_induc.lit".to_string();
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

        let mut runtime = Runtime::new_with_builtin_code();

        let mut snippet_durations_ms: Vec<(String, f64)> = Vec::new();
        let mut failed_labels: Vec<String> = Vec::new();
        let wall_start = Instant::now();
        let mut file_count_with_snippets: usize = 0;
        let mut snippet_count_run: usize = 0;
        for snippets in snippets_by_file.iter() {
            if snippets.is_empty() {
                continue;
            }

            file_count_with_snippets += 1;

            for (label, source_code, md_path_for_run_file) in snippets.iter() {
                if snippet_count_run == 0 {
                    runtime.new_file_path_new_env_new_name_scope(md_path_for_run_file.as_str());
                } else {
                    runtime.clear_current_env_and_parse_name_scope();
                    runtime.set_current_user_lit_file_path(md_path_for_run_file.as_str());
                }
                snippet_count_run += 1;

                let normalized_source = remove_windows_carriage_return(source_code);
                let start_snippet = Instant::now();
                let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    run_source_code(normalized_source.as_str(), &mut runtime)
                }));
                let (stmt_results, runtime_error) = match run_result {
                    Ok(result) => result,
                    Err(panic_payload) => {
                        let duration_ms = start_snippet.elapsed().as_secs_f64() * 1000.0;
                        let panic_message =
                            if let Some(message) = panic_payload.downcast_ref::<&str>() {
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

    #[test]
    fn run_all() {
        run_with_large_stack("run_all_large_stack", run_all_impl);
    }

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
                print_slowest_run_labels(
                    "math500 snippets before failure",
                    durations_ms.as_slice(),
                );
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
        let completed_dir = manifest_dir
            .join("MATH-500-litex")
            .join("math-500")
            .join("finished");
        assert!(
            completed_dir.is_dir(),
            "MATH-500-litex/math-500/finished must exist at {:?}",
            completed_dir
        );
        run_math500_litex_lit_dir(&completed_dir);
    }

    fn run_math500_litex_all_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lit_dir = manifest_dir
            .join("MATH-500-litex")
            .join("math-500")
            .join("unfinished");
        assert!(
            lit_dir.is_dir(),
            "MATH-500-litex/math-500/unfinished must exist at {:?}",
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

        assert!(
            !lit_paths.is_empty(),
            "{:?} must contain at least one .lit file",
            base_dir
        );

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

            let litex_code = fs::read_to_string(lit_path).unwrap_or_else(|read_error| {
                panic!("failed to read {:?}: {}", lit_path, read_error)
            });
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

    fn run_all_impl() {
        run_examples_impl();
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

    // cargo test run_gsm8k_debug_items -- --ignored --nocapture
    // LITEX_GSM8K_TITLE=gsm8k_1 cargo test run_gsm8k_debug_items -- --ignored --nocapture
    // LITEX_GSM8K_FILTER=wallet LITEX_GSM8K_LIMIT=5 cargo test run_gsm8k_debug_items -- --ignored --nocapture
    // LITEX_GSM8K_SPLIT=test LITEX_GSM8K_LIMIT=20 cargo test run_gsm8k_debug_items -- --ignored --nocapture
    // LITEX_GSM8K_DETAIL_OUTPUT=1 LITEX_GSM8K_TITLE=gsm8k_1 cargo test run_gsm8k_debug_items -- --ignored --nocapture
    #[test]
    #[ignore = "local debug helper; filters GSM8K items with env vars"]
    fn run_gsm8k_debug_items() {
        run_with_large_stack(
            "run_gsm8k_debug_items_large_stack",
            run_gsm8k_debug_items_impl,
        );
    }

    fn run_gsm8k_debug_items_impl() {
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
        run_jsonl_debug_items(
            "gsm8k",
            jsonl_paths.as_slice(),
            "LITEX_GSM8K",
            true,
            Some("train|test|all"),
        );
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
            if !jsonl_path.is_file() {
                println!(
                    "--- gsm8k jsonl file missing at {:?}; skip gsm8k solutions ---",
                    jsonl_path
                );
                return;
            }
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

    // cargo test run_metamathqa_debug_items -- --ignored --nocapture
    // LITEX_METAMATHQA_TITLE=MetaMathQA-GSM_FOBAR-350228 cargo test run_metamathqa_debug_items -- --ignored --nocapture
    // LITEX_METAMATHQA_FILTER=paint LITEX_METAMATHQA_LIMIT=5 cargo test run_metamathqa_debug_items -- --ignored --nocapture
    #[test]
    #[ignore = "local debug helper; filters MetaMathQA items with env vars"]
    fn run_metamathqa_debug_items() {
        run_with_large_stack(
            "run_metamathqa_debug_items_large_stack",
            run_metamathqa_debug_items_impl,
        );
    }

    fn run_metamathqa_debug_items_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let jsonl_paths = vec![manifest_dir
            .join("scripts")
            .join("MetaMathQA-litex")
            .join("MetaMathQA.jsonl")];
        run_jsonl_debug_items(
            "metamathqa",
            jsonl_paths.as_slice(),
            "LITEX_METAMATHQA",
            false,
            None,
        );
    }

    #[test]
    fn run_math23k_solutions() {
        run_with_large_stack(
            "run_math23k_solutions_large_stack",
            run_math23k_solutions_impl,
        );
    }

    fn run_math23k_solutions_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let jsonl_path = manifest_dir
            .join("scripts")
            .join("math23k-litex")
            .join("math23k.jsonl");
        assert!(
            jsonl_path.is_file(),
            "math23k-litex jsonl file must exist at {:?}",
            jsonl_path
        );

        let builtin_start = Instant::now();
        let mut runtime = Runtime::new_with_builtin_code();
        let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;

        let run_wall_start = Instant::now();
        let mut total_count: usize = 0;
        let mut failed_labels: Vec<String> = Vec::new();
        let mut total_solution_duration_ms: f64 = 0.0;

        run_labeled_jsonl_solution_file(
            "math23k-litex",
            &jsonl_path,
            &mut runtime,
            &mut total_count,
            &mut failed_labels,
            &mut total_solution_duration_ms,
        );

        let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
        println!("--- math23k-litex timing (summary) ---");
        println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
        println!(
            "  solutions: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
            total_count, total_solution_duration_ms, run_wall_ms
        );

        if failed_labels.is_empty() {
            println!("--- math23k-litex: all solutions OK ---");
            return;
        }

        println!("--- math23k-litex failed titles ---");
        for label in failed_labels.iter() {
            println!("{}", label);
        }
        panic!(
            "math23k-litex solution run failed for {} of {} item(s)",
            failed_labels.len(),
            total_count
        );
    }

    // cargo test run_math23k_debug_items -- --ignored --nocapture
    // LITEX_MATH23K_TITLE=Math23k_15120 cargo test run_math23k_debug_items -- --ignored --nocapture
    // LITEX_MATH23K_FILTER=相机 LITEX_MATH23K_LIMIT=5 cargo test run_math23k_debug_items -- --ignored --nocapture
    #[test]
    #[ignore = "local debug helper; filters Math23K items with env vars"]
    fn run_math23k_debug_items() {
        run_with_large_stack(
            "run_math23k_debug_items_large_stack",
            run_math23k_debug_items_impl,
        );
    }

    fn run_math23k_debug_items_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let jsonl_paths = vec![manifest_dir
            .join("scripts")
            .join("math23k-litex")
            .join("math23k.jsonl")];
        run_jsonl_debug_items(
            "math23k",
            jsonl_paths.as_slice(),
            "LITEX_MATH23K",
            false,
            None,
        );
    }

    #[test]
    fn run_metamathqa_litex_solutions() {
        run_with_large_stack(
            "run_metamathqa_litex_solutions_large_stack",
            run_metamathqa_litex_solutions_impl,
        );
    }

    #[test]
    fn run_minif2f_litex_completed() {
        run_with_large_stack(
            "run_minif2f_litex_completed_large_stack",
            run_minif2f_litex_completed_impl,
        );
    }

    fn run_minif2f_litex_completed_impl() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let jsonl_path = manifest_dir
            .parent()
            .unwrap_or(manifest_dir.as_path())
            .join("MiniF2F-litex")
            .join("litex_completed.jsonl");
        assert!(
            jsonl_path.is_file(),
            "MiniF2F-litex/litex_completed.jsonl must exist at {:?}",
            jsonl_path
        );

        let jsonl_path_str = match jsonl_path.to_str() {
            Some(path_string) => path_string.to_string(),
            None => panic!("{:?} must be valid UTF-8", jsonl_path),
        };
        let jsonl_content = match fs::read_to_string(&jsonl_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
        };

        let builtin_start = Instant::now();
        let mut runtime = Runtime::new_with_builtin_code();
        let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
        runtime.new_file_path_new_env_new_name_scope(jsonl_path_str.as_str());

        let run_wall_start = Instant::now();
        let mut total_count: usize = 0;
        let mut failed_labels: Vec<String> = Vec::new();
        let mut total_solution_duration_ms: f64 = 0.0;

        for (line_index, line) in jsonl_content.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            if total_count > 0 {
                runtime.clear_current_env_and_parse_name_scope();
                runtime.set_current_user_lit_file_path(jsonl_path_str.as_str());
            }

            let name = jsonl_string_field(line, "name").unwrap_or_else(|error_message| {
                panic!(
                    "failed to parse name in {:?} line {}: {}",
                    jsonl_path,
                    line_index + 1,
                    error_message
                )
            });
            let litex_code =
                jsonl_string_field(line, "litex_code").unwrap_or_else(|error_message| {
                    panic!(
                        "failed to parse litex_code in {:?} line {} ({}): {}",
                        jsonl_path,
                        line_index + 1,
                        name,
                        error_message
                    )
                });

            let normalized_source = remove_windows_carriage_return(litex_code.as_str());
            let start_time_for_one_solution = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), &mut runtime);
            let duration_ms = start_time_for_one_solution.elapsed().as_secs_f64() * 1000.0;
            total_solution_duration_ms += duration_ms;

            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            total_count += 1;
            if !run_succeeded {
                let label = format!("{}:{}", line_index + 1, name);
                println!(
                    "=== [FAILED] MiniF2F-litex at jsonl line {} ({:.2} ms): {} ===\n{}\n",
                    line_index + 1,
                    duration_ms,
                    name,
                    run_output
                );
                failed_labels.push(label);
            }
        }

        let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
        println!("--- MiniF2F-litex timing (summary) ---");
        println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
        println!(
            "  completed snippets: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
            total_count, total_solution_duration_ms, run_wall_ms
        );

        if failed_labels.is_empty() {
            println!("--- MiniF2F-litex: all completed snippets OK ---");
            return;
        }

        println!("--- MiniF2F-litex failed names ---");
        for label in failed_labels.iter() {
            println!("{}", label);
        }
        panic!(
            "MiniF2F-litex completed snippet run failed for {} of {} item(s)",
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

    #[derive(Clone)]
    struct JsonlDebugItem {
        label: String,
        title: String,
        source: String,
        path_for_runtime: String,
    }

    fn run_jsonl_debug_items(
        dataset_label: &str,
        jsonl_paths: &[PathBuf],
        env_prefix: &str,
        allow_split_filter: bool,
        split_hint: Option<&str>,
    ) {
        let split_key = format!("{}_SPLIT", env_prefix);
        let title_key = format!("{}_TITLE", env_prefix);
        let filter_key = format!("{}_FILTER", env_prefix);
        let limit_key = format!("{}_LIMIT", env_prefix);
        let stop_key = format!("{}_STOP_ON_FIRST_FAILURE", env_prefix);
        let detail_key = format!("{}_DETAIL_OUTPUT", env_prefix);

        let split_filter = if allow_split_filter {
            env_string(split_key.as_str())
                .unwrap_or_else(|| "all".to_string())
                .to_ascii_lowercase()
        } else {
            "all".to_string()
        };
        let title_filter = env_string(title_key.as_str());
        let text_filter = env_string(filter_key.as_str());
        let limit = env_usize(limit_key.as_str());
        let stop_on_first_failure = env_flag_is_set(stop_key.as_str());
        let detail_output = env_flag_is_set(detail_key.as_str());

        if title_filter.is_none() && text_filter.is_none() && limit.is_none() {
            println!("--- run_{}_debug_items: skip ---", dataset_label);
            println!("  Set one of:");
            println!("    {}=<exact title>", title_key);
            println!("    {}=<text substring>", filter_key);
            println!("    {}=5", limit_key);
            println!("  Optional:");
            if let Some(hint) = split_hint {
                println!("    {}={}", split_key, hint);
            }
            println!("    {}=1", detail_key);
            println!("    {}=1", stop_key);
            return;
        }

        let selected_paths =
            select_jsonl_paths_for_debug(jsonl_paths, split_filter.as_str(), allow_split_filter);

        if selected_paths.is_empty() {
            panic!(
                "{} must be one of train, test, all; got {:?}",
                split_key, split_filter
            );
        }

        for jsonl_path in selected_paths.iter() {
            if !jsonl_path.is_file() {
                println!(
                    "--- {} jsonl file missing at {:?}; skip {} debug items ---",
                    dataset_label, jsonl_path, dataset_label
                );
                return;
            }
        }

        let title_filter_lower = title_filter
            .as_ref()
            .map(|value| value.to_ascii_lowercase());
        let text_filter_lower = text_filter.as_ref().map(|value| value.to_ascii_lowercase());
        let mut items: Vec<JsonlDebugItem> = Vec::new();

        for jsonl_path in selected_paths.iter() {
            let jsonl_path_str = match jsonl_path.to_str() {
                Some(path_string) => path_string.to_string(),
                None => panic!("{:?} must be valid UTF-8", jsonl_path),
            };
            let split_label = jsonl_path
                .file_stem()
                .and_then(|file_stem| file_stem.to_str())
                .unwrap_or(dataset_label);
            let jsonl_content = match fs::read_to_string(jsonl_path) {
                Ok(content) => content,
                Err(read_error) => panic!("failed to read {:?}: {}", jsonl_path, read_error),
            };

            for (line_index, line) in jsonl_content.lines().enumerate() {
                if line.trim().is_empty() {
                    continue;
                }

                let title = jsonl_string_field(line, "title").unwrap_or_else(|error_message| {
                    panic!(
                        "failed to parse title in {:?} line {}: {}",
                        jsonl_path,
                        line_index + 1,
                        error_message
                    )
                });
                let description =
                    jsonl_string_field(line, "description").unwrap_or_else(|error_message| {
                        panic!(
                            "failed to parse description in {:?} line {} ({}): {}",
                            jsonl_path,
                            line_index + 1,
                            title,
                            error_message
                        )
                    });
                let solution =
                    jsonl_string_field(line, "solution").unwrap_or_else(|error_message| {
                        panic!(
                            "failed to parse solution in {:?} line {} ({}): {}",
                            jsonl_path,
                            line_index + 1,
                            title,
                            error_message
                        )
                    });

                if let Some(expected_title) = title_filter_lower.as_ref() {
                    if title.to_ascii_lowercase() != *expected_title {
                        continue;
                    }
                }
                if let Some(filter_text) = text_filter_lower.as_ref() {
                    let haystack = format!("{}\n{}", title, description).to_ascii_lowercase();
                    if !haystack.contains(filter_text.as_str()) {
                        continue;
                    }
                }

                items.push(JsonlDebugItem {
                    label: format!("{}:{} (line {})", split_label, title, line_index + 1),
                    title,
                    source: solution,
                    path_for_runtime: jsonl_path_str.clone(),
                });

                if limit.is_some_and(|max_items| items.len() >= max_items) {
                    break;
                }
            }

            if limit.is_some_and(|max_items| items.len() >= max_items) {
                break;
            }
        }

        if items.is_empty() {
            println!(
                "--- run_{}_debug_items: no matching items ---",
                dataset_label
            );
            if allow_split_filter {
                println!("  split: {}", split_filter);
            }
            if let Some(title) = title_filter {
                println!("  title: {}", title);
            }
            if let Some(filter_text) = text_filter {
                println!("  filter: {}", filter_text);
            }
            if let Some(max_items) = limit {
                println!("  limit: {}", max_items);
            }
            return;
        }

        let builtin_start = Instant::now();
        let mut runtime = Runtime::new_with_builtin_code();
        let builtin_duration_ms = builtin_start.elapsed().as_secs_f64() * 1000.0;
        runtime.new_file_path_new_env_new_name_scope(items[0].path_for_runtime.as_str());
        runtime.detail_output = detail_output;
        runtime.module_manager.hide_file_paths_in_output = !detail_output;

        let run_wall_start = Instant::now();
        let mut durations_ms: Vec<(String, f64)> = Vec::new();
        let mut failed_labels: Vec<String> = Vec::new();

        for (item_index, item) in items.iter().enumerate() {
            if item_index > 0 {
                runtime.clear_current_env_and_parse_name_scope();
                runtime.set_current_user_lit_file_path(item.path_for_runtime.as_str());
            }

            let normalized_source = remove_windows_carriage_return(item.source.as_str());
            let start_time = Instant::now();
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), &mut runtime);
            let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            let status_label = if run_succeeded { "OK" } else { "FAILED" };

            println!(
                "=== [{}] {} ({:.2} ms) ===\n# {}\n{}\n",
                status_label, item.label, duration_ms, item.title, run_output
            );

            durations_ms.push((item.label.clone(), duration_ms));
            if !run_succeeded {
                failed_labels.push(item.label.clone());
                if stop_on_first_failure {
                    break;
                }
            }
        }

        let run_wall_ms = run_wall_start.elapsed().as_secs_f64() * 1000.0;
        println!("--- {} debug timing (summary) ---", dataset_label);
        println!("  builtin init (once): {:.2} ms", builtin_duration_ms);
        println!(
            "  items: {} run(s), sum of runs: {:.2} ms | wall: {:.2} ms",
            durations_ms.len(),
            durations_ms
                .iter()
                .map(|(_, duration_ms)| duration_ms)
                .sum::<f64>(),
            run_wall_ms
        );
        print_slowest_run_labels(
            format!("{} debug items", dataset_label).as_str(),
            durations_ms.as_slice(),
        );

        if failed_labels.is_empty() {
            println!("--- {} debug: all selected items OK ---", dataset_label);
            return;
        }

        println!("--- {} debug failed labels ---", dataset_label);
        for label in failed_labels.iter() {
            println!("{}", label);
        }
        panic!(
            "{} debug run failed for {} of {} item(s)",
            dataset_label,
            failed_labels.len(),
            durations_ms.len()
        );
    }

    fn select_jsonl_paths_for_debug(
        jsonl_paths: &[PathBuf],
        split_filter: &str,
        allow_split_filter: bool,
    ) -> Vec<PathBuf> {
        if !allow_split_filter || split_filter == "all" {
            return jsonl_paths.to_vec();
        }

        let mut selected_paths: Vec<PathBuf> = Vec::new();
        for jsonl_path in jsonl_paths.iter() {
            let Some(file_stem) = jsonl_path.file_stem().and_then(|name| name.to_str()) else {
                continue;
            };
            if file_stem.eq_ignore_ascii_case(split_filter) {
                selected_paths.push(jsonl_path.clone());
            }
        }
        selected_paths
    }

    fn run_labeled_jsonl_solution_file(
        dataset_label: &str,
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
                    "=== [FAILED] {} at jsonl line {} ({:.2} ms): {} ===\n{}\n",
                    dataset_label,
                    line_index + 1,
                    duration_ms,
                    title,
                    run_output
                );
                failed_labels.push(label);
            }

            if *total_count % 100 == 0 {
                println!(
                    "--- {} progress: {} solution(s), {} failure(s) ---",
                    dataset_label,
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

    fn env_flag_is_set(name: &str) -> bool {
        match std::env::var(name) {
            Ok(value) => {
                let normalized = value.trim().to_ascii_lowercase();
                !normalized.is_empty() && normalized != "0" && normalized != "false"
            }
            Err(_) => false,
        }
    }

    fn env_string(name: &str) -> Option<String> {
        match std::env::var(name) {
            Ok(value) => {
                let trimmed = value.trim();
                if trimmed.is_empty() {
                    None
                } else {
                    Some(trimmed.to_string())
                }
            }
            Err(_) => None,
        }
    }

    fn env_usize(name: &str) -> Option<usize> {
        let value = env_string(name)?;
        match value.parse::<usize>() {
            Ok(parsed) => Some(parsed),
            Err(parse_error) => {
                panic!(
                    "{} must be a positive integer, got {:?}: {}",
                    name, value, parse_error
                )
            }
        }
    }
}
