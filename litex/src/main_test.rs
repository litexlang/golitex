#[cfg(test)]
mod run_tmp_lit {
    use std::path::PathBuf;
    use std::fs;

    use crate::pipeline::run_source_code;

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples").join("tmp.lit");
        let source = fs::read_to_string(&path).expect("examples/tmp.lit must exist");
        let result = run_source_code(&source);
        assert!(!result.is_empty(), "run_source_code(examples/tmp.lit) should produce non-empty output");
    }
}
