// Integration test: run test/test.lit and check the result.

use std::path::PathBuf;
use std::fs;

use litex::run_source_code;

#[test]
fn run_test_lit() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test").join("test.lit");
    let source = fs::read_to_string(&path).expect("test/test.lit must exist");
    let result = run_source_code(&source);
    assert!(!result.is_empty(), "run_source_code(test.lit) should produce non-empty output");
}
