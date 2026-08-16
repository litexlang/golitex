use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const SOURCE: &str = "examples/09_compile_to_lean/compile_to_lean_examples.lit";
const GENERATED: &str = "examples/09_compile_to_lean/compile_to_lean_examples.lean";

#[test]
fn lean_command_reproduces_the_checked_in_09_examples() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("success");
    let output_path = scratch.new_path("lean");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .args(["-lean", SOURCE])
        .arg(&output_path)
        .output()
        .expect("run -lean");

    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("wrote freshly generated Lean"));

    let generated = fs::read_to_string(&output_path).expect("read generated Lean output");
    let checked_in = fs::read_to_string(root.join(GENERATED)).expect("read checked-in Lean output");
    assert_eq!(generated, checked_in, "the checked-in Lean ledger is stale");
    assert!(generated.starts_with("import Litex.Rules\n"));
    assert!(generated.contains("namespace __Sketch01"));
    assert!(generated.contains("namespace __Sketch24"));
    assert!(generated.contains("example : (1 : Litex.Object) = 1 :="));
    assert!(!generated.contains("sorry"));
}

#[test]
fn lean_command_preserves_existing_output_when_compilation_fails() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("failure");
    let source_path = scratch.new_path("lit");
    let output_path = scratch.new_path("lean");
    let sentinel = "existing output must survive\n";
    fs::write(&source_path, "sketch:\n    abstract_prop p(x)\n    $p(1)\n")
        .expect("write invalid Litex input");
    fs::write(&output_path, sentinel).expect("write existing output");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean")
        .arg(&source_path)
        .arg(&output_path)
        .output()
        .expect("run failing -lean");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("failed to compile"));
    assert_eq!(
        fs::read_to_string(&output_path).expect("read preserved output"),
        sentinel
    );
}

#[test]
fn lean_command_rejects_the_litex_file_as_its_output() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("same-path");
    let source_path = scratch.new_path("lit");
    let source = "sketch:\n    1 = 1\n";
    fs::write(&source_path, source).expect("write Litex input");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean")
        .arg(&source_path)
        .arg(&source_path)
        .output()
        .expect("run same-path -lean");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("Litex input and Lean output paths must be different"));
    assert_eq!(
        fs::read_to_string(&source_path).expect("read preserved input"),
        source
    );
}

struct ScratchFiles {
    prefix: PathBuf,
    paths: Vec<PathBuf>,
}

impl ScratchFiles {
    fn new(label: &str) -> Self {
        let private = Path::new(env!("CARGO_MANIFEST_DIR")).join("private");
        fs::create_dir_all(&private).expect("create private test root");
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos();
        Self {
            prefix: private.join(format!(
                "compile-to-lean-file-cli-{label}-{}-{nonce}",
                std::process::id()
            )),
            paths: Vec::new(),
        }
    }

    fn new_path(&mut self, extension: &str) -> PathBuf {
        let path = self.prefix.with_extension(extension);
        self.paths.push(path.clone());
        path
    }
}

impl Drop for ScratchFiles {
    fn drop(&mut self) {
        for path in &self.paths {
            let _ = fs::remove_file(path);
        }
    }
}
