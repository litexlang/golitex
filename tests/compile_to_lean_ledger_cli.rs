use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const LEDGER: &str = "lean/examples/compile_to_lean_examples.md";

#[test]
fn lean_ledger_command_freshly_compiles_all_entries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("success");
    let output_path = scratch.new_path("lean");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .args(["-lean-ledger", LEDGER])
        .arg(&output_path)
        .output()
        .expect("run -lean-ledger");

    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("wrote 25 freshly generated Lean entries")
    );

    let generated = fs::read_to_string(&output_path).expect("read bundled Lean output");
    assert_eq!(generated.matches("-- BEGIN ENTRY ").count(), 25);
    assert_eq!(generated.matches("import Litex.Rules").count(), 1);
    assert!(!generated.contains("Litex.abiVersion"));
    assert!(generated.contains("__wd0_"));
    assert!(!generated.contains("well_defined_fact_"));
    assert!(generated.contains("-- BEGIN ENTRY 02: trusted_forall_atomic_fact"));
    assert!(generated.contains("namespace Entry02"));
    assert!(generated.contains("axiom __fact3"));
    assert!(generated.contains("theorem __fact4 : p 1 := by"));
    assert!(!generated.contains("Required generated shape"));
}

#[test]
fn lean_ledger_command_does_not_replace_output_when_an_entry_fails() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("failure");
    let ledger_path = scratch.new_path("md");
    let output_path = scratch.new_path("lean");
    let sentinel = "existing output must survive\n";
    fs::write(
        &ledger_path,
        "## broken\n\n```litex\nabstract_prop p(x)\n\n$p(1)\n```\n",
    )
    .expect("write broken ledger");
    fs::write(&output_path, sentinel).expect("write existing output");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean-ledger")
        .arg(&ledger_path)
        .arg(&output_path)
        .output()
        .expect("run failing -lean-ledger");

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("ledger entry broken failed to compile")
    );
    assert_eq!(
        fs::read_to_string(&output_path).expect("read preserved output"),
        sentinel
    );
}

#[test]
fn lean_ledger_command_rejects_the_markdown_file_as_its_output() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("same-path");
    let ledger_path = scratch.new_path("md");
    let ledger = "## reflexivity\n\n```litex\n1 = 1\n```\n";
    fs::write(&ledger_path, ledger).expect("write ledger");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean-ledger")
        .arg(&ledger_path)
        .arg(&ledger_path)
        .output()
        .expect("run same-path -lean-ledger");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("Markdown ledger and Lean output paths must be different"));
    assert_eq!(
        fs::read_to_string(&ledger_path).expect("read preserved ledger"),
        ledger
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
                "compile-to-lean-ledger-cli-{label}-{}-{nonce}",
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
