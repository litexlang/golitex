use crate::builtin_theorem::BuiltinTheoremId;

#[test]
fn builtin_theorem_examples_verify_including_supplementary_tracers() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/stmt_nodes/release_and_expand/builtin_thm");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("lit"))
        .collect();
    paths.sort();
    assert!(
        !paths.is_empty(),
        "builtin theorem example selection is empty"
    );
    let mut native_tracers = 0;
    for path in paths {
        let name = path.file_stem().unwrap().to_str().unwrap();
        // Supplementary examples may exercise a builtin through a differently
        // named source theorem. Their filename is not a reserved theorem ID.
        if let Some(id) = BuiltinTheoremId::from_name(name) {
            assert_eq!(id.as_str(), name);
            native_tracers += 1;
        }
        let code = std::fs::read_to_string(&path).unwrap();
        let mut rt = super::runtime();
        let result = rt.run_litex_code(&code).unwrap();
        assert!(
            result.session_error.is_none() && result.success,
            "{}\n{}",
            path.display(),
            crate::json_output::emit_run_detailed(&result, &rt, "test", None)
        );
    }
    assert!(
        native_tracers > 0,
        "no registered builtin tracers were selected"
    );
}
