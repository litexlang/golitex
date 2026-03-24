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

        assert!(
            path.is_file(),
            "examples/tmp.lit must exist at {:?}",
            path
        );

        let path_str = path
            .to_str()
            .expect("examples/tmp.lit path must be valid UTF-8");

        let source_code = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read examples/tmp.lit: {}", e));

        let start_time = Instant::now();
        let result_from_string =
            run_source_code_from_string(source_code.as_str(), path_str);
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
