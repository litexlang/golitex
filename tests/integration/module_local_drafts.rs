use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn local_drafts_directory_is_not_a_module_child() {
    let fixture = Fixture::new("accepted");
    write_module(&fixture.root);
    write_file(
        &fixture.root.join(".drafts/scratch.lit"),
        "this is deliberately not valid Litex\n",
    );

    let output = run_module(&fixture.root);
    assert!(
        output.status.success(),
        "module with local drafts failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"ok\": true"));
}

#[test]
fn lake_build_directory_is_not_a_module_child() {
    let fixture = Fixture::new("lake-build-directory");
    write_module(&fixture.root);
    write_file(
        &fixture.root.join(".lake/build/lib/lean/Main.olean"),
        "generated Lake artifact\n",
    );

    let output = run_module(&fixture.root);
    assert!(
        output.status.success(),
        "module next to Lake build metadata failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"ok\": true"));
}

#[test]
fn ordinary_unexported_paths_are_ignored() {
    let fixture = Fixture::new("ignored");
    write_module(&fixture.root);
    write_file(&fixture.root.join("notes/scratch.lit"), "1 = 0\n");
    write_file(&fixture.root.join("sidecar.lit"), "1 = 0\n");
    write_file(&fixture.root.join("todo.lit"), "1 = 0\n");

    let output = run_module(&fixture.root);
    assert!(
        output.status.success(),
        "module with an unexported directory failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"ok\": true"));
}

#[test]
fn explicitly_selected_unexported_file_is_rejected_by_project_mode() {
    let fixture = Fixture::new("unexported-file-target");
    write_module(&fixture.root);
    let sidecar = fixture.root.join("sidecar.lit");
    write_file(&sidecar, "have sidecar R = 1\n");

    let output = run_file(&sidecar);
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .contains("must be exported exactly once by its containing litex.config"),
        "unexpected output:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn declared_exports_remain_strictly_validated() {
    let missing = Fixture::new("missing-export");
    write_file(
        &missing.root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nmissing = \"./missing.lit\"\n",
    );
    let missing_output = run_module(&missing.root);
    assert!(!missing_output.status.success());
    assert!(
        String::from_utf8_lossy(&missing_output.stdout).contains("[export] target"),
        "unexpected missing-export output:\n{}",
        String::from_utf8_lossy(&missing_output.stdout),
    );

    let duplicate = Fixture::new("duplicate-export-path");
    write_file(
        &duplicate.root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nfirst = \"./main.lit\"\nsecond = \"./main.lit\"\n",
    );
    write_file(&duplicate.root.join("main.lit"), "have value R = 1\n");
    let duplicate_output = run_module(&duplicate.root);
    assert!(!duplicate_output.status.success());
    assert!(
        String::from_utf8_lossy(&duplicate_output.stdout).contains("declared more than once"),
        "unexpected duplicate-export output:\n{}",
        String::from_utf8_lossy(&duplicate_output.stdout),
    );

    let wrong_extension = Fixture::new("wrong-export-extension");
    write_file(
        &wrong_extension.root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nnotes = \"./notes.md\"\n",
    );
    write_file(&wrong_extension.root.join("notes.md"), "sidecar\n");
    let wrong_extension_output = run_module(&wrong_extension.root);
    assert!(!wrong_extension_output.status.success());
    assert!(
        String::from_utf8_lossy(&wrong_extension_output.stdout)
            .contains("file targets must point to a .lit file"),
        "unexpected wrong-extension output:\n{}",
        String::from_utf8_lossy(&wrong_extension_output.stdout),
    );
}

fn write_module(root: &Path) {
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
}

fn run_module(root: &Path) -> Output {
    Command::new(litex_binary())
        .args([
            "-graph",
            "-r",
            root.to_str().expect("fixture path must be UTF-8"),
        ])
        .output()
        .expect("run Litex module")
}

fn run_file(path: &Path) -> Output {
    Command::new(litex_binary())
        .args(["-f", path.to_str().expect("fixture path must be UTF-8")])
        .output()
        .expect("run Litex file")
}

fn litex_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_litex") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/litex")
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture directory");
    }
    fs::write(path, source).expect("write fixture file");
}

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-module-local-drafts-{name}-{}-{id}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).expect("remove stale fixture");
        }
        fs::create_dir_all(&root).expect("create fixture root");
        Fixture { root }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
