#[cfg(test)]
mod run_tmp_lit {
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::pipeline::run_source_code_in_file_and_return_string;

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        assert!(path.is_file(), "examples/tmp.lit must exist at {:?}", path);

        let path_str = path
            .to_str()
            .expect("examples/tmp.lit path must be valid UTF-8");

        let start_time = Instant::now();
        let result_from_string = run_source_code_in_file_and_return_string(path_str);
        let duration_string = start_time.elapsed();

        let start_time = Instant::now();
        let result_from_file = run_source_code_in_file_and_return_string(path_str);
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
    use crate::pipeline::run_source_code_and_return_json_string;

    fn print_json_for_lit_source(sample_label: &str, lit_source_code: &str) {
        let json_output_text =
            run_source_code_and_return_json_string(lit_source_code, sample_label);
        println!(
            "\n--- JSON for label {:?} ---\n{}",
            sample_label, json_output_text
        );
    }

    #[test]
    fn print_json_for_sample_lit_string() {
        // let code = "prove:\n    1 = 1\n";
        let code = "have a N_pos = 1\na = 1\n1+1=2\n1=1";
        print_json_for_lit_source("test.lit", code);
    }
}
