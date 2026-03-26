#[cfg(test)]
mod run_tmp_lit {
    use std::fs;
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

        let tmp_lit_content = fs::read_to_string(&path).expect("examples/tmp.lit must be readable");
        if tmp_lit_content.trim().is_empty() {
            println!("examples/tmp.lit is empty; skip run_examples_tmp_lit");
            return;
        }

        let start_time = Instant::now();
        let result_from_string = run_source_code_in_file_and_return_string(path_str);
        let duration_string = start_time.elapsed();

        println!("\n{}\n", result_from_string);
        println!(
            "Time (from_string): {:?} ({:.2} ms)",
            duration_string,
            duration_string.as_secs_f64() * 1000.0
        );
    }
}
