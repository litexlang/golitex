use std::fs;
use std::path::{Path, PathBuf};

#[test]
fn examples_are_publishable_content_not_run_instructions() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    assert!(
        !root.join("05_compiler_interop").exists(),
        "05_compiler_interop must stay consolidated into 09_compile_to_lean"
    );
    assert!(
        !root.join("_internal/proof_journals").exists(),
        "developer proof journals do not belong in the publishable examples tree"
    );

    let cases = root.join("09_compile_to_lean/cases");
    let case_count = fs::read_dir(&cases)
        .unwrap_or_else(|error| panic!("read {}: {error}", cases.display()))
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().and_then(|value| value.to_str()) == Some("lit"))
        .count();
    assert_eq!(case_count, 24, "09 must own all 24 Litex-to-Lean cases");

    let forbidden = [
        "target/release/litex",
        "cargo test",
        "LITEX_LEAN_PROJECT",
        "LITEX_LAKE",
        "lake build",
        "lake env",
        "python3 scripts/",
        "npm run",
        "## Verification",
        "Focused gate",
        "Source gate:",
        "compiler gate:",
        "Lean gate:",
        "Run this acceptance example",
        "Run one standalone",
    ];

    for path in text_files_under(&root) {
        let content = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        for pattern in forbidden {
            assert!(
                !content.contains(pattern),
                "{} contains operational instruction {pattern:?}",
                path.display()
            );
        }
    }
}

fn text_files_under(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        for entry in
            fs::read_dir(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
        {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if matches!(
                path.extension().and_then(|value| value.to_str()),
                Some("lit" | "md" | "json" | "config")
            ) {
                files.push(path);
            }
        }
    }
    files
}
