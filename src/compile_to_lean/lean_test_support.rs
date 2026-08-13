use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

pub(crate) struct SharedLeanTestLibrary {
    project: PathBuf,
    lake: OsString,
    output_root: PathBuf,
    generated_files: Vec<PathBuf>,
}

impl SharedLeanTestLibrary {
    pub(crate) fn new(label: &str) -> Self {
        let project = std::env::var_os("LITEX_LEAN_PROJECT")
            .map(PathBuf::from)
            .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
        let lake = std::env::var_os("LITEX_LAKE").unwrap_or_else(|| "lake".into());
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos();
        let output_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("private")
            .join(format!(
                "litex-shared-lean-{}-{}-{nonce}",
                safe_path_component(label),
                std::process::id()
            ));
        fs::create_dir_all(output_root.join("Litex"))
            .expect("create shared Lean test output directory");

        let library = Self {
            project,
            lake,
            output_root,
            generated_files: Vec::new(),
        };
        library.compile_shared_module("Core");
        library.compile_shared_module("BuiltinRules");
        library
    }

    pub(crate) fn compile_generated(&mut self, label: &str, generated: &str) {
        let path = self
            .output_root
            .join(format!("{}.lean", safe_path_component(label)));
        fs::write(&path, generated).expect("write generated Lean test source");
        self.generated_files.push(path.clone());

        let output = run_lean(
            &self.lake,
            &self.project,
            Some(&self.output_root),
            vec![path.as_os_str().to_owned()],
        );
        assert_lean_success(label, &output, generated);
    }

    pub(crate) fn reject_generated(&mut self, label: &str, generated: &str) {
        let path = self
            .output_root
            .join(format!("{}.lean", safe_path_component(label)));
        fs::write(&path, generated).expect("write rejected Lean test source");
        self.generated_files.push(path.clone());

        let output = run_lean(
            &self.lake,
            &self.project,
            Some(&self.output_root),
            vec![path.as_os_str().to_owned()],
        );
        assert!(
            !output.status.success(),
            "Lean source {label} unexpectedly compiled\nsource:\n{generated}"
        );
    }

    fn compile_shared_module(&self, module: &str) {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let source_root = root.join("lean");
        let source = source_root.join("Litex").join(format!("{module}.lean"));
        let output_path = self
            .output_root
            .join("Litex")
            .join(format!("{module}.olean"));
        let output = run_lean(
            &self.lake,
            &self.project,
            Some(&self.output_root),
            vec![
                "-R".into(),
                source_root.as_os_str().to_owned(),
                "-o".into(),
                output_path.as_os_str().to_owned(),
                source.as_os_str().to_owned(),
            ],
        );
        let source_text = fs::read_to_string(&source).expect("read shared Lean module");
        assert_lean_success(&format!("Litex.{module}"), &output, &source_text);
    }
}

impl Drop for SharedLeanTestLibrary {
    fn drop(&mut self) {
        for path in self.generated_files.iter() {
            let _ = fs::remove_file(path);
        }
        for module in ["BuiltinRules", "Core"] {
            let _ = fs::remove_file(
                self.output_root
                    .join("Litex")
                    .join(format!("{module}.olean")),
            );
        }
        let _ = fs::remove_dir(self.output_root.join("Litex"));
        let _ = fs::remove_dir(&self.output_root);
    }
}

fn run_lean(
    lake: &OsString,
    project: &Path,
    lean_path: Option<&Path>,
    args: Vec<OsString>,
) -> Output {
    let mut command = Command::new(lake);
    command
        .args(["env", "lean"])
        .args(args)
        .current_dir(project);
    if let Some(lean_path) = lean_path {
        command.env("LEAN_PATH", lean_path);
    }
    command
        .output()
        .expect("run Lean through configured Lake project")
}

fn assert_lean_success(label: &str, output: &Output, source: &str) {
    assert!(
        output.status.success(),
        "Lean source {label} failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{source}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn safe_path_component(label: &str) -> String {
    label
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '-' || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect()
}
