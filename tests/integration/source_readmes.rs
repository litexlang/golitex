use std::fs;
use std::path::{Path, PathBuf};

fn directory_contains_rust_source(directory: &Path) -> bool {
    let entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()));
    for entry in entries {
        let path = entry.expect("source directory entry").path();
        if path.is_dir() && directory_contains_rust_source(&path) {
            return true;
        }
        if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            return true;
        }
    }
    false
}

#[test]
fn every_nonempty_top_level_source_subsystem_has_an_example_readme() {
    let source_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
    let source_index_path = source_root.join("README.md");
    let source_index = fs::read_to_string(&source_index_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", source_index_path.display()));

    let mut documented_subsystems = Vec::new();
    for entry in fs::read_dir(&source_root).expect("read src directory") {
        let path = entry.expect("src entry").path();
        if !path.is_dir() || !directory_contains_rust_source(&path) {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("UTF-8 source subsystem name");
        let readme_path = path.join("README.md");
        let readme = fs::read_to_string(&readme_path).unwrap_or_else(|error| {
            panic!(
                "source subsystem `{name}` must have {}: {error}",
                readme_path.display()
            )
        });
        assert!(
            readme.to_ascii_lowercase().contains("example"),
            "{} must explain at least one concrete example",
            readme_path.display()
        );
        assert!(
            readme.contains('`'),
            "{} must show its example as code or an inline expression",
            readme_path.display()
        );
        assert!(
            source_index.contains(&format!("({name}/README.md)")),
            "src/README.md must link the `{name}` subsystem README"
        );
        documented_subsystems.push(name.to_string());
    }

    documented_subsystems.sort();
    assert!(
        documented_subsystems.len() >= 23,
        "expected the current 23 nonempty source subsystems, found {documented_subsystems:?}"
    );

    for important_subsystem in [
        "environment",
        "execute",
        "graph",
        "infer",
        "module_manager",
        "parse",
        "pipeline",
        "rational_expression",
        "result",
        "runtime",
        "stmt_result_to_lean_compiler",
        "verify",
    ] {
        let readme_path = source_root.join(important_subsystem).join("README.md");
        let readme = fs::read_to_string(&readme_path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", readme_path.display()));
        assert!(
            readme.contains("```text"),
            "important subsystem `{important_subsystem}` must show its control flow as pseudocode"
        );
    }
}
