#[cfg(test)]
mod run_tmp_lit {
    use std::path::PathBuf;

    use crate::pipeline::run_source_code_in_file;

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples").join("tmp.lit");
        if let Some(path_str) = path.to_str() {
            let result = run_source_code_in_file(path_str);
            println!("\n{}\n", result);
            assert!(!result.is_empty(), "run_source_code(examples/tmp.lit) should produce non-empty output");
        } else {
            panic!("examples/tmp.lit must exist");
        }
    }
}
