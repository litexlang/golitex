use super::*;

#[test]
fn paired_output_replaces_lit_extension() {
    assert_eq!(
        paired_output_path(Path::new("examples/1_SetSystem.lit")).unwrap(),
        PathBuf::from("examples/1_SetSystem.lean")
    );
}

#[test]
fn paired_output_rejects_non_lit_input() {
    let error = paired_output_path(Path::new("examples/1_SetSystem.lean")).unwrap_err();
    assert!(error.contains("expects a .lit input"));
}
