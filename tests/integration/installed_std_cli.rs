//! Run release executables from external projects against their bundled std.

use litex::knowledge_base::JsonValue;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

struct Installation(PathBuf);

impl Installation {
    fn new() -> Self {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "litex-installed-std-{}-{unique}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("project")).unwrap();
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/module_manager/installed_std/project");
        for name in ["litex.config", "main.lit"] {
            fs::copy(fixture.join(name), root.join("project").join(name)).unwrap();
        }
        fs::write(
            root.join("project/litex.config"),
            "[import std]\nbasics\n[export]\nmain = \"./main.lit\"\n",
        )
        .unwrap();
        Self(root)
    }

    fn install(&self, binary_directory: &str, std_directory: &str) -> PathBuf {
        let directory = self.0.join(binary_directory);
        fs::create_dir_all(&directory).unwrap();
        let name = if cfg!(windows) { "litex.exe" } else { "litex" };
        let binary = directory.join(name);
        fs::copy(env!("CARGO_BIN_EXE_litex"), &binary).unwrap();
        self.write_std(std_directory, 1);
        binary
    }

    fn write_std(&self, directory: &str, version: i32) {
        let basics = self.0.join(directory).join("basics");
        fs::create_dir_all(&basics).unwrap();
        fs::write(
            basics.join("litex.config"),
            "[export]\nmain = \"./main.lit\"\n",
        )
        .unwrap();
        fs::write(
            basics.join("main.lit"),
            format!("let version = {version}\n"),
        )
        .unwrap();
    }

    fn run(&self, binary: &Path, arguments: &[&str], std: Option<&Path>) -> Output {
        let mut command = Command::new(binary);
        command
            .args(["-lang", "en", "-strict"])
            .args(arguments)
            .current_dir(self.0.join("project"))
            .env_remove("LITEX_STD_PATH");
        if let Some(path) = std {
            command.env("LITEX_STD_PATH", path);
        }
        command.output().unwrap()
    }
}

impl Drop for Installation {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn assert_run(output: &Output, success: bool) {
    assert_eq!(
        output.status.code(),
        Some(if success { 0 } else { 1 }),
        "{output:?}"
    );
    assert!(output.stderr.is_empty(), "{output:?}");
    let value = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    let fields = value.as_object().unwrap();
    assert_eq!(fields.get("kind").unwrap().as_str().unwrap(), "run");
    assert_eq!(fields.get("success").unwrap(), &JsonValue::Bool(success));
    if success {
        assert_eq!(fields.get("session_error").unwrap(), &JsonValue::Null);
    }
}

#[test]
fn bundled_std_is_discovered_in_all_package_layouts() {
    for (binary, std) in [
        ("archive", "archive/std"),
        ("homebrew/bin", "homebrew/bin/std"),
        ("legacy-homebrew/bin", "legacy-homebrew/share/litex/std"),
        ("msi/bin", "msi/std"),
        ("usr/local/bin", "usr/share/litex/std"),
        ("usr/bin", "usr/share/litex/std"),
    ] {
        let installation = Installation::new();
        let executable = installation.install(binary, std);
        for arguments in [
            &["-f", "main.lit"][..],
            &["-e", "basics:::version = 1"][..],
            &["-r", "."][..],
        ] {
            assert_run(&installation.run(&executable, arguments, None), true);
        }
        assert_run(
            &installation.run(&executable, &["-e", "basics:::version = 2"], None),
            false,
        );
    }
}

#[test]
fn explicit_std_override_and_local_project_std_keep_precedence() {
    let installation = Installation::new();
    let executable = installation.install("install", "install/std");
    installation.write_std("override", 2);
    let override_path = installation.0.join("override");
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&override_path)),
        false,
    );
    fs::write(
        installation.0.join("project/main.lit"),
        "basics:::version = 2\n",
    )
    .unwrap();
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&override_path)),
        true,
    );
    let invalid = installation.0.join("absent");
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&invalid)),
        false,
    );
    installation.write_std("project/std", 3);
    fs::write(
        installation.0.join("project/main.lit"),
        "basics:::version = 3\n",
    )
    .unwrap();
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], None),
        true,
    );
}

#[test]
fn bundled_std_does_not_implicitly_import_its_declarations() {
    let installation = Installation::new();
    let executable = installation.install("install", "install/std");
    fs::write(
        installation.0.join("project/litex.config"),
        "[export]\nmain = \"./main.lit\"\n",
    )
    .unwrap();
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], None),
        false,
    );
}

#[test]
fn repl_and_continued_file_session_can_use_bundled_std() {
    let installation = Installation::new();
    let executable = installation.install("install", "install/std");
    for arguments in [&[][..], &["-f", "main.lit", "-session"][..]] {
        let mut child = Command::new(&executable)
            .args(["-lang", "en", "-strict"])
            .args(arguments)
            .current_dir(installation.0.join("project"))
            .env_remove("LITEX_STD_PATH")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"basics:::version = 1\nexit\n")
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let text = std::str::from_utf8(&output.stdout).unwrap();
        assert!(text.contains("litex> success"), "{text}");
    }
}

#[cfg(unix)]
#[test]
fn installed_std_follows_the_real_executable_through_a_symlink() {
    let installation = Installation::new();
    let executable =
        installation.install("cellar/litex/version/bin", "cellar/litex/version/bin/std");
    let symlink = installation.0.join("litex-link");
    std::os::unix::fs::symlink(executable, &symlink).unwrap();
    assert_run(&installation.run(&symlink, &["-f", "main.lit"], None), true);
}
