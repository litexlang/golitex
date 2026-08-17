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
fn ordinary_unexported_directory_is_still_rejected() {
    let fixture = Fixture::new("rejected");
    write_module(&fixture.root);
    write_file(
        &fixture.root.join("notes/scratch.lit"),
        "have scratch R = 1\n",
    );

    let output = run_module(&fixture.root);
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("unexported Litex module path `notes`"),
        "unexpected output:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
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
            "-compact",
            "-runner",
            "-r",
            root.to_str().expect("fixture path must be UTF-8"),
        ])
        .output()
        .expect("run Litex module")
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
