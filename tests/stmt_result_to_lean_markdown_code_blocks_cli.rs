use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn stmt_result_to_lean_markdown_code_blocks_command_freshly_compiles_all_code_blocks() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("success");
    let markdown_path = scratch.new_path("md");
    let output_path = scratch.new_path("lean");
    fs::write(
        &markdown_path,
        "## reflexivity\n\n```litex\n1 = 1\n```\n\n## arithmetic\n\n```litex\n2 + 3 = 5\n```\n",
    )
    .expect("write Litex Markdown code blocks");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean-ledger")
        .arg(&markdown_path)
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
        String::from_utf8_lossy(&output.stdout).contains("wrote 2 freshly generated Lean entries")
    );

    let generated = fs::read_to_string(&output_path).expect("read bundled Lean output");
    assert_eq!(generated.matches("-- BEGIN ENTRY ").count(), 2);
    assert_eq!(generated.matches("import Litex\n").count(), 1);
    assert!(!generated.contains("import Litex.Rules\n"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(generated.contains("-- BEGIN ENTRY 02: arithmetic"));
    assert!(generated.contains("namespace Entry02"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn stmt_result_to_lean_markdown_code_blocks_command_preserves_output_when_a_code_block_fails() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("failure");
    let markdown_path = scratch.new_path("md");
    let output_path = scratch.new_path("lean");
    let sentinel = "existing output must survive\n";
    fs::write(
        &markdown_path,
        "## broken\n\n```litex\nabstract_prop p(x)\n\n$p(1)\n```\n",
    )
    .expect("write broken Litex Markdown code block");
    fs::write(&output_path, sentinel).expect("write existing output");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean-ledger")
        .arg(&markdown_path)
        .arg(&output_path)
        .output()
        .expect("run failing -lean-ledger");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("Litex Markdown code block broken failed to compile"));
    assert_eq!(
        fs::read_to_string(&output_path).expect("read preserved output"),
        sentinel
    );
}

#[test]
fn stmt_result_to_lean_markdown_code_blocks_command_rejects_the_input_as_its_output() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut scratch = ScratchFiles::new("same-path");
    let markdown_path = scratch.new_path("md");
    let markdown = "## reflexivity\n\n```litex\n1 = 1\n```\n";
    fs::write(&markdown_path, markdown).expect("write Litex Markdown code block");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .current_dir(root)
        .arg("-lean-ledger")
        .arg(&markdown_path)
        .arg(&markdown_path)
        .output()
        .expect("run same-path -lean-ledger");

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("the Markdown input and Lean output paths must be different"));
    assert_eq!(
        fs::read_to_string(&markdown_path).expect("read preserved Markdown"),
        markdown
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
                "stmt-result-to-lean-markdown-code-blocks-cli-{label}-{}-{nonce}",
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
