#[cfg(test)]
mod run_tmp_lit {
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::pipeline::{run_source_code_from_string, run_source_code_in_file};

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        assert!(path.is_file(), "examples/tmp.lit must exist at {:?}", path);

        let path_str = path
            .to_str()
            .expect("examples/tmp.lit path must be valid UTF-8");

        let source_code = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read examples/tmp.lit: {}", e));

        let start_time = Instant::now();
        let result_from_string = run_source_code_from_string(source_code.as_str(), path_str);
        let duration_string = start_time.elapsed();

        let start_time = Instant::now();
        let result_from_file = run_source_code_in_file(path_str);
        let duration_file = start_time.elapsed();

        println!("\n{}\n", result_from_string);
        println!(
            "Time (from_string): {:?} ({:.2} ms)",
            duration_string,
            duration_string.as_secs_f64() * 1000.0
        );
        println!(
            "Time (in_file): {:?} ({:.2} ms)",
            duration_file,
            duration_file.as_secs_f64() * 1000.0
        );

        assert_eq!(
            result_from_string.trim(),
            result_from_file.trim(),
            "pipeline entry points should agree for the same file content"
        );

        assert!(
            !result_from_string.contains("VerifyError"),
            "examples/tmp.lit should run without verification errors, got:\n{}",
            result_from_string
        );
        assert!(
            result_from_string.contains("Success"),
            "expected Success in output, got:\n{}",
            result_from_string
        );
    }
}

#[cfg(test)]
mod run_source_code_from_string_json_samples {
    use crate::pipeline::run_source_code_from_string_json;

    fn print_json_for_lit_source(sample_label: &str, lit_source_code: &str) {
        let json_output_text = run_source_code_from_string_json(lit_source_code, sample_label);
        println!(
            "\n--- JSON for label {:?} ---\n{}",
            sample_label, json_output_text
        );
    }

    #[test]
    fn print_json_for_sample_lit_strings() {
        let labeled_lit_source_samples: Vec<(&str, &str)> = vec![
            ("trivial_numeric_equality", "prove:\n    1 = 1\n"),
            ("number_comparison_less_builtin", "prove:\n    1 < 2\n"),
            (
                "expanded_square_rational_simplification",
                "prove:\n    have a, b R_nz\n\n    (a + b) ^ 2 = a * a + 2 * a * b + b ^ 2\n",
            ),
        ];

        for (sample_label, lit_source_code) in labeled_lit_source_samples {
            print_json_for_lit_source(sample_label, lit_source_code);
        }
    }

    #[test]
    fn json_for_less_than_contains_builtin_rules_type() {
        let json_output_text =
            run_source_code_from_string_json("prove:\n    1 < 2\n", "json_for_less_than");
        println!("{}", json_output_text);
        assert!(
            json_output_text.contains("\"type\":")
                && json_output_text.contains("fact_verified_by_builtin_rules"),
            "expected JSON with fact_verified_by_builtin_rules, got:\n{}",
            json_output_text
        );
    }

    #[test]
    fn json_for_trivial_equality_contains_success_or_builtin() {
        let json_output_text =
            run_source_code_from_string_json("prove:\n    1 = 1\n", "json_for_one_equals_one");
        assert!(
            json_output_text.contains("\"type\":")
                && (json_output_text.contains("fact_verified_by_builtin_rules")
                    || json_output_text.contains("non_factual_stmt_success")),
            "expected a structured JSON result type, got:\n{}",
            json_output_text
        );
    }
}
