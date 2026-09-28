use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

#[test]
fn examples_are_publishable_content_not_run_instructions() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = repo.join("examples");
    assert!(
        !root.join("05_compiler_interop").exists(),
        "05_compiler_interop must stay consolidated into lean/examples"
    );
    assert!(
        !root.join("09_compile_to_lean").exists(),
        "the target-side compiler ledger belongs in lean/examples"
    );
    assert!(
        !root.join("_internal/proof_journals").exists(),
        "developer proof journals do not belong in the publishable examples tree"
    );

    let compiler_examples = repo.join("lean/examples");
    let litex_example_stems = example_file_stems_with_extension(&compiler_examples, "lit");
    let lean_example_stems = example_file_stems_with_extension(&compiler_examples, "lean");
    assert!(
        litex_example_stems.len() >= 57,
        "lean/examples must retain the established compiler ledger"
    );
    assert_eq!(
        litex_example_stems, lean_example_stems,
        "every Litex compiler example must own one same-name generated Lean file"
    );

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

fn example_file_stems_with_extension(root: &Path, extension: &str) -> BTreeSet<String> {
    fs::read_dir(root)
        .unwrap_or_else(|error| panic!("read {}: {error}", root.display()))
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let path = entry.path();
            (path.extension().and_then(|value| value.to_str()) == Some(extension))
                .then(|| path.file_stem()?.to_str().map(str::to_string))?
        })
        .collect()
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
