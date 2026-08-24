use std::fs;
use std::path::{Path, PathBuf};

fn rust_files_below(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        for entry in fs::read_dir(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
        {
            let path = entry.expect("directory entry should be readable").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn rust_visibility_does_not_regress_to_crate_only() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let forbidden = ["pub", "(crate)"].concat();
    let offenders: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            fs::read_to_string(path)
                .expect("Rust source should be readable")
                .contains(&forbidden)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "crate-only visibility returned in: {offenders:#?}"
    );
}

#[test]
fn production_sources_contain_loaders_but_no_test_bodies() {
    let source_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let test_attribute = ["#[", "test]"].concat();
    let source_files = rust_files_below(&source_root);
    let offenders: Vec<_> = source_files
        .iter()
        .filter(|path| {
            fs::read_to_string(path)
                .expect("Rust source should be readable")
                .contains(&test_attribute)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "test bodies must live below tests/, not src/: {offenders:#?}"
    );

    let cfg_test = ["#[cfg(", "test)]"].concat();
    let mut non_loader_cfg = Vec::new();
    for path in source_files {
        let source = fs::read_to_string(&path).expect("Rust source should be readable");
        let lines: Vec<_> = source.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if line.trim() != cfg_test {
                continue;
            }
            let next = lines
                .get(index + 1)
                .map(|line| line.trim())
                .unwrap_or_default();
            if !next.starts_with("#[path = ") || !next.contains("tests/unit/") {
                non_loader_cfg.push((path.clone(), index + 1));
            }
        }
    }
    assert!(
        non_loader_cfg.is_empty(),
        "cfg(test) in src/ is reserved for tests/unit loaders: {non_loader_cfg:#?}"
    );
}

#[test]
fn compiler_and_test_directories_follow_the_repository_layout() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let compiler = root.join("src/stmt_result_to_lean_compiler");
    assert!(compiler.join("implementation").is_dir());
    assert!(!compiler.join("stmt_result_to_lean_compiler").exists());
    assert!(root.join("tests/unit").is_dir());
    assert!(root.join("tests/integration").is_dir());
    assert!(root.join("tests/tooling").is_dir());
}
