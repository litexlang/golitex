#[cfg(test)]
mod run_tmp_lit {
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::pipeline::run_source_code_in_file;

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        let path_str = path
            .to_str()
            .expect("examples/tmp.lit path must be valid UTF-8");
        let start_time = Instant::now();
        let result = run_source_code_in_file(path_str);
        let duration = start_time.elapsed();

        println!("\n{}\n", result);
        println!(
            "Time taken: {:?} ({:.2} ms)",
            duration,
            duration.as_secs_f64() * 1000.0
        );
    }
}
