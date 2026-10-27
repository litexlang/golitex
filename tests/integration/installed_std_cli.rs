//! Run release executables from external projects against their bundled std.

use litex::knowledge_base::JsonValue;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
static INSTALLATION_LOCK: Mutex<()> = Mutex::new(());

struct Installation {
    root: PathBuf,
    _guard: MutexGuard<'static, ()>,
}

impl Installation {
    fn new() -> Self {
        // A concurrent fork can inherit a copied executable's writable descriptor
        // until exec. Keep copies and launches exclusive for the fixture's lifetime.
        let guard = INSTALLATION_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
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
            "[import std]\nbasics\n[alias]\nbasics = basics::main\n[export]\nmain = \"./main.lit\"\n",
        )
        .unwrap();
        Self {
            root,
            _guard: guard,
        }
    }

    fn install(&self, binary_directory: &str, std_directory: &str) -> PathBuf {
        let directory = self.root.join(binary_directory);
        fs::create_dir_all(&directory).unwrap();
        let name = if cfg!(windows) { "litex.exe" } else { "litex" };
        let binary = directory.join(name);
        fs::copy(env!("CARGO_BIN_EXE_litex"), &binary).unwrap();
        self.write_std(std_directory, 1);
        binary
    }

    fn write_std(&self, directory: &str, version: i32) {
        let basics = self.root.join(directory).join("basics");
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
            .current_dir(self.root.join("project"))
            .env_remove("LITEX_STD_PATH");
        if let Some(path) = std {
            command.env("LITEX_STD_PATH", path);
        }
        command.output().unwrap()
    }
}

impl Drop for Installation {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
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
    assert_eq!(
        fields.get("run_result").unwrap().as_str().ok(),
        Some(if success { "success" } else { "failure" })
    );
    if success {
        assert_eq!(
            fields.get("session_terminated").unwrap(),
            &JsonValue::Bool(false)
        );
        assert_eq!(fields.get("termination").unwrap(), &JsonValue::Null);
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
            &["-e", "basics::version = 1"][..],
            &["-r", "."][..],
        ] {
            assert_run(&installation.run(&executable, arguments, None), true);
        }
        assert_run(
            &installation.run(&executable, &["-e", "basics::version = 2"], None),
            false,
        );
    }
}

#[test]
fn explicit_std_override_and_local_project_std_keep_precedence() {
    let installation = Installation::new();
    let executable = installation.install("install", "install/std");
    installation.write_std("override", 2);
    let override_path = installation.root.join("override");
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&override_path)),
        false,
    );
    fs::write(
        installation.root.join("project/main.lit"),
        "basics::version = 2\n",
    )
    .unwrap();
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&override_path)),
        true,
    );
    let invalid = installation.root.join("absent");
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], Some(&invalid)),
        false,
    );
    installation.write_std("project/std", 3);
    fs::write(
        installation.root.join("project/main.lit"),
        "basics::version = 3\n",
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
        installation.root.join("project/litex.config"),
        "[export]\nmain = \"./main.lit\"\n",
    )
    .unwrap();
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], None),
        false,
    );
}

#[test]
fn installed_matrix_entrywise_laws_use_source_theorems_and_keep_guards() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let matrix = installation.root.join("install/std/matrix");
    fs::create_dir_all(&matrix).unwrap();
    for name in ["litex.config", "main.lit"] {
        fs::copy(repository.join("std/matrix").join(name), matrix.join(name)).unwrap();
        fs::copy(
            repository
                .join("examples/algebra/matrix_entrywise")
                .join(name),
            installation.root.join("project").join(name),
        )
        .unwrap();
    }
    assert_run(
        &installation.run(&executable, &["-f", "main.lit"], None),
        true,
    );
    for source in [
        // A retired bare name is not a hidden native alias.
        "release thm matrix_add_commutative(zero_matrix(2,2),zero_matrix(2,2),2,2)",
        // Shape, scalar, arity and parameter-order obligations still apply.
        "release thm Matrix::main::matrix_add_commutative(zero_matrix(2,2),zero_matrix(2,3),2,2)",
        "release thm Matrix::main::matrix_add_zero(zero_matrix(2,2),2,3)",
        "release thm Matrix::main::matrix_scale_distributive({1},zero_matrix(2,2),zero_matrix(2,2),2,2)",
        "release thm Matrix::main::matrix_scale_one(zero_matrix(2,2),2)",
        "release thm Matrix::main::matrix_add_commutative(2,2,zero_matrix(2,2),zero_matrix(2,2))",
        "release thm Matrix::main::matrix_scale_zero(matrix_scale(1/0,zero_matrix(2,2),2,2),2,2)",
        "matrix_scale(0,identity_matrix(2),2,2)=identity_matrix(2)",
    ] {
        assert_run(&installation.run(&executable, &["-e", source], None), false);
    }
}

#[test]
fn repl_and_continued_file_session_can_use_bundled_std() {
    let installation = Installation::new();
    let executable = installation.install("install", "install/std");
    for arguments in [&[][..], &["-f", "main.lit", "-session"][..]] {
        let mut child = Command::new(&executable)
            .args(["-lang", "en", "-strict"])
            .args(arguments)
            .current_dir(installation.root.join("project"))
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
            .write_all(b"basics::version = 1\nexit\n")
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("REPL"),
            "{output:?}"
        );
        let text = std::str::from_utf8(&output.stdout).unwrap();
        assert!(
            text.contains("\"run_result\": \"success\",\n  \"target\": \"repl\""),
            "{text}"
        );
    }
}

#[cfg(unix)]
#[test]
fn installed_std_follows_the_real_executable_through_a_symlink() {
    let installation = Installation::new();
    let executable =
        installation.install("cellar/litex/version/bin", "cellar/litex/version/bin/std");
    let symlink = installation.root.join("litex-link");
    std::os::unix::fs::symlink(executable, &symlink).unwrap();
    assert_run(&installation.run(&symlink, &["-f", "main.lit"], None), true);
}

#[test]
fn installed_higher_derivatives_keep_proof_guards_in_one_session() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let library = installation.root.join("install/std/real_multivariable");
    fs::create_dir_all(&library).unwrap();
    for entry in fs::read_dir(repository.join("std/real_multivariable")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "lit")
            || path.file_name().is_some_and(|name| name == "litex.config")
        {
            fs::copy(&path, library.join(path.file_name().unwrap())).unwrap();
        }
    }
    let ordered = repository.join("examples/real_analysis/multivariable/higher_order");
    let unary = repository.join("examples/real_analysis/higher_derivatives");
    let source = format!(
        "{}\n{}",
        fs::read_to_string(ordered.join("main.lit")).unwrap(),
        fs::read_to_string(unary.join("main.lit")).unwrap(),
    );
    fs::write(installation.root.join("project/main.lit"), source).unwrap();
    fs::copy(
        ordered.join("litex.config"),
        installation.root.join("project/litex.config"),
    )
    .unwrap();

    // File declarations belong to main::. The REPL has its own root namespace.
    let mut turns: Vec<(String, bool, Option<String>)> = vec![
        ("\\Calc::higher_order::ordered_partial<2,cart_n(R,2),3>(main::polynomial,main::p,main::path)=24".into(), true, None),
        ("\\Calc::unary_higher_order::nth_derivative<R,3>(main::cubic,2)=6".into(), true, None),
    ];
    for fixture in [
        ordered.join("boundaries.json"),
        unary.join("boundaries.json"),
    ] {
        let data = JsonValue::parse(&fs::read_to_string(fixture).unwrap()).unwrap();
        let fields = data.as_object().unwrap();
        for source in fields.get("setup").unwrap().as_array().unwrap() {
            turns.push((source.as_str().unwrap().into(), true, None));
        }
        for case in fields.get("cases").unwrap().as_array().unwrap() {
            let case = case.as_object().unwrap();
            let category = case
                .get("expected_category")
                .and_then(|value| value.as_str().ok())
                .map(str::to_owned);
            turns.push((
                case.get("source").unwrap().as_str().unwrap().into(),
                false,
                category,
            ));
            turns.push(("0=0".into(), true, None));
        }
    }
    assert_installed_session(
        &executable,
        &installation.root.join("project"),
        "main.lit",
        &turns,
    );
}

fn assert_installed_session(
    binary: &Path,
    project: &Path,
    target: &str,
    turns: &[(String, bool, Option<String>)],
) {
    let rejected = turns.iter().filter(|(_, success, _)| !success).count();
    let mut script = String::new();
    for (source, _, _) in turns {
        script.push_str(source);
        script.push_str("\n\n");
    }
    script.push_str("exit\n");
    let mut child = Command::new(binary)
        .args(["-lang", "en", "-strict", "-f", target, "-session"])
        .current_dir(project)
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
        .write_all(script.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    // Soft proof rejections keep the Session usable and do not fail its process.
    // Their per-turn verdicts and the final aggregate errors are asserted below.
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    let stdout = std::str::from_utf8(&output.stdout).unwrap();
    let mut frames = Vec::new();
    let mut pending = String::new();
    for line in stdout.lines() {
        pending.push_str(line);
        pending.push('\n');
        if let Ok(frame) = JsonValue::parse(&pending) {
            frames.push(frame);
            pending.clear();
        }
    }
    assert!(pending.trim().is_empty(), "incomplete JSON: {pending}");
    assert_eq!(frames.len(), turns.len() + 1, "{stdout}");
    for (frame, (source, success, category)) in frames.iter().zip(turns) {
        let fields = frame.as_object().unwrap();
        assert_eq!(
            fields.get("target").unwrap().as_str().unwrap(),
            "repl",
            "{source}"
        );
        assert_eq!(
            fields.get("run_result").unwrap().as_str().unwrap(),
            if *success { "success" } else { "failure" },
            "{source}: {frame:?}"
        );
        assert_eq!(
            fields.get("session_terminated").unwrap(),
            &JsonValue::Bool(false),
            "{source}"
        );
        assert_eq!(
            fields.get("termination").unwrap(),
            &JsonValue::Null,
            "{source}"
        );
        if let Some(category) = category {
            let errors = fields.get("errors").unwrap().as_array().unwrap();
            assert_eq!(
                errors[0]
                    .as_object()
                    .unwrap()
                    .get("category")
                    .unwrap()
                    .as_str()
                    .unwrap(),
                category,
                "{source}"
            );
        }
    }
    let final_fields = frames.last().unwrap().as_object().unwrap();
    assert_eq!(
        final_fields
            .get("errors")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        rejected
    );
}

#[test]
fn installed_higher_derivative_functions_keep_actual_domains() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let library = installation.root.join("install/std/real_multivariable");
    fs::create_dir_all(&library).unwrap();
    for entry in fs::read_dir(repository.join("std/real_multivariable")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "lit")
            || path.file_name().is_some_and(|name| name == "litex.config")
        {
            fs::copy(&path, library.join(path.file_name().unwrap())).unwrap();
        }
    }
    let fixture = repository.join("examples/real_analysis/higher_derivatives");
    for name in ["main.lit", "mixed.lit", "coherence.lit", "litex.config"] {
        fs::copy(
            fixture.join(name),
            installation.root.join("project").join(name),
        )
        .unwrap();
    }
    let mut turns: Vec<(String, bool, Option<String>)> = vec![
        ("coherence::first_map(2)=12".into(), true, None),
        (
            "$has_derivative_at(coherence::first_map,2,12)".into(),
            true,
            None,
        ),
        ("coherence::second_map(2)=12".into(), true, None),
        (
            "$has_derivative_at(coherence::second_map,2,6)".into(),
            true,
            None,
        ),
    ];
    let data =
        JsonValue::parse(&fs::read_to_string(fixture.join("coherence_boundaries.json")).unwrap())
            .unwrap();
    let fields = data.as_object().unwrap();
    for source in fields.get("setup").unwrap().as_array().unwrap() {
        turns.push((source.as_str().unwrap().into(), true, None));
    }
    for case in fields.get("cases").unwrap().as_array().unwrap() {
        let case = case.as_object().unwrap();
        turns.push((
            case.get("source").unwrap().as_str().unwrap().into(),
            false,
            Some(
                case.get("expected_category")
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .into(),
            ),
        ));
        turns.push(("0=0".into(), true, None));
    }
    assert_installed_session(
        &executable,
        &installation.root.join("project"),
        "coherence.lit",
        &turns,
    );
}

#[test]
fn installed_higher_derivative_laws_use_source_candidates() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    for package in ["real_multivariable", "real_higher_order_laws"] {
        let library = installation.root.join("install/std").join(package);
        fs::create_dir_all(&library).unwrap();
        for entry in fs::read_dir(repository.join("std").join(package)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "lit")
                || path.file_name().is_some_and(|name| name == "litex.config")
            {
                fs::copy(&path, library.join(path.file_name().unwrap())).unwrap();
            }
        }
    }
    let fixture = repository.join("examples/real_analysis/higher_derivative_laws");
    for name in ["main.lit", "ordered.lit", "litex.config"] {
        fs::copy(
            fixture.join(name),
            installation.root.join("project").join(name),
        )
        .unwrap();
    }
    for (target, boundaries, positives) in [
        (
            "main.lit",
            "boundaries.json",
            vec![
                "\\Calc::unary_higher_order::nth_derivative<R,3>(main::law_sum,0)=5",
                "$Calc::unary_higher_order::has_nth_derivative_at(R,3,main::law_difference,0,7)",
                "$Calc::unary_higher_order::has_nth_derivative_at(R,3,main::law_scaled,0,20)",
                "$Calc::unary_higher_order::has_nth_derivative_at(R,0,main::law_sum,0,0)",
            ],
        ),
        (
            "ordered.lit",
            "ordered_boundaries.json",
            vec![
                "\\Calc::higher_order::ordered_partial<2,cart_n(R,2),2>(ordered::law_partial_sum,ordered::law_point,ordered::law_path)=2",
                "$Calc::higher_order::has_ordered_partial_at(2,cart_n(R,2),2,ordered::law_partial_scaled,ordered::law_point,ordered::law_path,6)",
                "$Calc::higher_order::has_ordered_partial_at(2,cart_n(R,2),0,ordered::law_partial_sum,ordered::law_point,tuple(),25)",
            ],
        ),
    ] {
        let mut turns: Vec<(String, bool, Option<String>)> = positives
            .into_iter()
            .map(|source| (source.into(), true, None))
            .collect();
        let data =
            JsonValue::parse(&fs::read_to_string(fixture.join(boundaries)).unwrap()).unwrap();
        let fields = data.as_object().unwrap();
        for source in fields.get("setup").unwrap().as_array().unwrap() {
            turns.push((source.as_str().unwrap().into(), true, None));
        }
        for case in fields.get("cases").unwrap().as_array().unwrap() {
            let case = case.as_object().unwrap();
            turns.push((
                case.get("source").unwrap().as_str().unwrap().into(),
                false,
                Some(
                    case.get("expected_category")
                        .unwrap()
                        .as_str()
                        .unwrap()
                        .into(),
                ),
            ));
            turns.push(("0=0".into(), true, None));
        }
        assert_installed_session(
            &executable,
            &installation.root.join("project"),
            target,
            &turns,
        );
    }
}

#[test]
fn installed_real_regularity_keeps_open_domains_and_candidates() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    for package in [
        "real_multivariable",
        "real_higher_order_laws",
        "real_regularity",
        "real_regularity_laws",
    ] {
        let library = installation.root.join("install/std").join(package);
        fs::create_dir_all(&library).unwrap();
        for entry in fs::read_dir(repository.join("std").join(package)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "lit")
                || path.file_name().is_some_and(|name| name == "litex.config")
            {
                fs::copy(&path, library.join(path.file_name().unwrap())).unwrap();
            }
        }
    }
    let fixture = repository.join("examples/real_analysis/regularity");
    for name in ["main.lit", "scalar.lit", "litex.config"] {
        fs::copy(
            fixture.join(name),
            installation.root.join("project").join(name),
        )
        .unwrap();
    }
    for (target, boundaries, positives) in [
        (
            "main.lit",
            "boundaries.json",
            vec![
                "$Reg::main::is_unary_c_k_on_open(R,3,main::regularity_cubic)",
                "$Reg::main::is_unary_c_k_on_open(R,0,main::regularity_absolute)",
                "$Reg::main::is_unary_smooth_on_open(R,main::regularity_unary_constant)",
                "$Reg::main::is_scalar_smooth_on_open(2,cart_n(R,2),main::regularity_scalar_constant)",
                "\\Calc::unary_higher_order::nth_derivative<R,3>(main::regularity_cubic,0)=6",
            ],
        ),
        (
            "scalar.lit",
            "scalar_boundaries.json",
            vec![
                "$Reg::main::is_scalar_c_k_on_open(2,cart_n(R,2),2,scalar::regularity_product)",
                "\\Calc::higher_order::ordered_partial<2,cart_n(R,2),2>(scalar::regularity_product,scalar::regularity_point,scalar::regularity_forward)=1",
                "\\Calc::higher_order::ordered_partial<2,cart_n(R,2),2>(scalar::regularity_product,scalar::regularity_point,scalar::regularity_reverse)=1",
            ],
        ),
    ] {
        let mut turns: Vec<(String, bool, Option<String>)> = positives
            .into_iter()
            .map(|source| (source.into(), true, None))
            .collect();
        let data =
            JsonValue::parse(&fs::read_to_string(fixture.join(boundaries)).unwrap()).unwrap();
        let fields = data.as_object().unwrap();
        for source in fields.get("setup").unwrap().as_array().unwrap() {
            turns.push((source.as_str().unwrap().into(), true, None));
        }
        for case in fields.get("cases").unwrap().as_array().unwrap() {
            let case = case.as_object().unwrap();
            turns.push((
                case.get("source").unwrap().as_str().unwrap().into(),
                false,
                Some(
                    case.get("expected_category")
                        .unwrap()
                        .as_str()
                        .unwrap()
                        .into(),
                ),
            ));
            turns.push(("0=0".into(), true, None));
        }
        assert_installed_session(
            &executable,
            &installation.root.join("project"),
            target,
            &turns,
        );
    }

    // The law example reuses Base through normal relative imports and explicit
    // definition/theorem release, so its fixture must keep that directory layout.
    let base = installation.root.join("regularity");
    fs::create_dir_all(&base).unwrap();
    for name in ["main.lit", "scalar.lit", "litex.config"] {
        fs::copy(fixture.join(name), base.join(name)).unwrap();
    }
    let laws = repository.join("examples/real_analysis/regularity_laws");
    let law_project = installation.root.join("law-project");
    fs::create_dir_all(&law_project).unwrap();
    for name in ["main.lit", "litex.config"] {
        fs::copy(laws.join(name), law_project.join(name)).unwrap();
    }
    let mut law_turns: Vec<(String, bool, Option<String>)> = [
        "$Reg::main::is_unary_c_k_on_open(R,3,main::shifted_cubic)",
        "$Reg::main::is_scalar_c_k_on_open(2,cart_n(R,2),2,main::shifted_product)",
        "$Reg::main::is_unary_smooth_on_open(R,main::smooth_unary_sum)",
        "$Reg::main::is_scalar_smooth_on_open(2,cart_n(R,2),main::smooth_scalar_sum)",
    ]
    .into_iter()
    .map(|source| (source.into(), true, None))
    .collect();
    let data =
        JsonValue::parse(&fs::read_to_string(laws.join("boundaries.json")).unwrap()).unwrap();
    for case in data
        .as_object()
        .unwrap()
        .get("cases")
        .unwrap()
        .as_array()
        .unwrap()
    {
        let case = case.as_object().unwrap();
        law_turns.push((
            case.get("source").unwrap().as_str().unwrap().into(),
            false,
            Some(
                case.get("expected_category")
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .into(),
            ),
        ));
        law_turns.push(("0=0".into(), true, None));
    }
    assert_installed_session(
        &executable,
        &installation.root,
        "law-project/main.lit",
        &law_turns,
    );
}

#[test]
fn installed_finite_function_sums_keep_domains_and_prefix_guards() {
    let installation = Installation::new();
    let executable = installation.install("install/bin", "install/std");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    for package in [
        "real_multivariable",
        "real_function_sums",
        "real_scalar_function_sums",
    ] {
        let library = installation.root.join("install/std").join(package);
        fs::create_dir_all(&library).unwrap();
        for entry in fs::read_dir(repository.join("std").join(package)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "lit")
                || path.file_name().is_some_and(|name| name == "litex.config")
            {
                fs::copy(&path, library.join(path.file_name().unwrap())).unwrap();
            }
        }
    }
    for (relative, directory, positives) in [
        (
            "examples/real_analysis/function_sums",
            "unary-project",
            vec![
                "$has_derivative_at(\\Sums::main::unary_function_prefix_sum<R,3>(main::terms,2),0,1)",
                "$is_continuous_at(\\Sums::main::unary_function_prefix_sum<R,3>(main::terms,3),0)",
                "$has_derivative_at(\\Sums::main::unary_function_prefix_sum<R,3>(main::terms,0),0,0)",
                "\\Sums::main::finite_real_prefix_sum<0>(main::empty_values,0)=0",
            ],
        ),
        (
            "examples/real_analysis/multivariable/function_sums",
            "scalar-project",
            vec![
                "$has_partial_derivative_at(\\MultiSums::main::scalar_function_prefix_sum<2,cart_n(R,2),2>(main::terms,2),main::point,2,1,2)",
                "$is_multi_continuous_at(\\MultiSums::main::scalar_function_prefix_sum<2,cart_n(R,2),2>(main::terms,2),main::point,2)",
            ],
        ),
    ] {
        let fixture = repository.join(relative);
        let project = installation.root.join(directory);
        fs::create_dir_all(&project).unwrap();
        for name in ["main.lit", "litex.config"] {
            fs::copy(fixture.join(name), project.join(name)).unwrap();
        }
        let mut turns: Vec<(String, bool, Option<String>)> = positives
            .into_iter()
            .map(|source| (source.into(), true, None))
            .collect();
        let data = JsonValue::parse(&fs::read_to_string(fixture.join("boundaries.json")).unwrap())
            .unwrap();
        let data = data.as_object().unwrap();
        for source in data.get("setup").unwrap().as_array().unwrap() {
            turns.push((source.as_str().unwrap().into(), true, None));
        }
        for case in data.get("cases").unwrap().as_array().unwrap() {
            let case = case.as_object().unwrap();
            turns.push((
                case.get("source").unwrap().as_str().unwrap().into(),
                false,
                Some(
                    case.get("expected_category")
                        .unwrap()
                        .as_str()
                        .unwrap()
                        .into(),
                ),
            ));
            turns.push(("0=0".into(), true, None));
        }
        assert_installed_session(&executable, &project, "main.lit", &turns);
    }
}
