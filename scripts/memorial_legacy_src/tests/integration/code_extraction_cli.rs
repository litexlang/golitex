use std::fs;
use std::process::Command;

#[test]
fn direct_inline_extraction_uses_the_new_python_and_c_commands() {
    let python = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-extractpython", "have a R = 1"])
        .output()
        .expect("run Python extraction CLI");
    assert!(python.status.success(), "{python:?}");
    let python_stdout = String::from_utf8(python.stdout).expect("Python stdout is UTF-8");
    assert!(python_stdout.contains("\"kind\": \"artifact\""));
    assert!(python_stdout.contains("\"format\": \"python\""));
    assert!(python_stdout.contains("\"content\": \"a = 1.0\""));
    assert!(python_stdout.contains("\"error\": null"));

    let c = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-extractc", "have a R = 1"])
        .output()
        .expect("run C extraction CLI");
    assert!(c.status.success(), "{c:?}");
    let c_stdout = String::from_utf8(c.stdout).expect("C stdout is UTF-8");
    assert!(c_stdout.contains("\"kind\": \"artifact\""));
    assert!(c_stdout.contains("\"format\": \"c\""));
    assert!(c_stdout.contains("\"content\": \"double a = 1.0;\""));
    assert!(c_stdout.contains("\"error\": null"));
}

#[test]
fn central_whitelist_rejects_the_old_extraction_inline_selector() {
    for flag in ["-extractpython", "-extractc"] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args([flag, "-e", "have a R = 1"])
            .output()
            .expect("run extraction CLI with retired -e selector");
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
        assert!(
            stdout.contains("\"kind\": \"cli_error\"")
                && stdout.contains("unsupported CLI command combination"),
            "{stdout}"
        );
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn c_extraction_emits_a_c99_function_shape() {
    let source = "have fn f(x R) R = x + 1\nhave algo for f(x):\n    x + 1";
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-extractc", source])
        .output()
        .expect("run C function extraction CLI");
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("C stdout is UTF-8");
    assert!(stdout.contains("\"kind\": \"artifact\""), "{stdout}");
    assert!(stdout.contains("double f(double x) {"), "{stdout}");
    assert!(stdout.contains("return (x + 1.0);"), "{stdout}");
}

#[test]
fn plain_file_extraction_uses_markers_while_latex_still_uses_the_full_file() {
    let directory = std::env::temp_dir().join(format!(
        "litex-isolated-file-conversions-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create isolated conversion fixture");
    let file = directory.join("standalone.lit");
    fs::write(&file, "# [-extract]\nhave a R = 1\n# [end of -extract]\n")
        .expect("write standalone Litex source");
    let path = file.to_str().expect("fixture path is UTF-8");

    let python = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-extractpython", "-f", path])
        .output()
        .expect("extract Python from auto-isolated file");
    assert!(python.status.success(), "{python:?}");
    let python_stdout = String::from_utf8(python.stdout).expect("Python stdout is UTF-8");
    assert!(python_stdout.contains("\"format\": \"python\""));
    assert!(python_stdout.contains("\"content\": \"a = 1.0\""));
    assert!(python_stdout.contains("\"error\": null"));

    let latex = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-latex", "-f", path])
        .output()
        .expect("render LaTeX from auto-isolated file");
    assert!(latex.status.success(), "{latex:?}");
    let latex_stdout = String::from_utf8(latex.stdout).expect("LaTeX stdout is UTF-8");
    assert!(latex_stdout.contains("\"format\": \"latex\""));
    assert!(latex_stdout.contains("\"content\":"));
    assert!(latex_stdout.contains("\"error\": null"));

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn file_extraction_concatenates_marked_blocks_and_ignores_other_statements() {
    let directory = extraction_fixture_directory("multiple-blocks");
    let file = directory.join("selected.lit");
    fs::write(
        &file,
        "1 = 2\n\n  # [-extract]  \nhave first R = 1\n\t# [end of -extract]\t\n\n1 = 2\n\n# [-extract]\nhave second R = 2\n# [end of -extract]\n\n1 = 2\n",
    )
    .expect("write marked extraction fixture");
    let path = file.to_str().expect("fixture path is UTF-8");

    for (flag, first, second) in [
        ("-extractpython", "first = 1.0", "second = 2.0"),
        ("-extractc", "double first = 1.0;", "double second = 2.0;"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args([flag, "-f", path])
            .output()
            .expect("extract marked file");
        assert!(output.status.success(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).expect("extraction stdout is UTF-8");
        let first_position = stdout.find(first).unwrap_or_else(|| panic!("{stdout}"));
        let second_position = stdout.find(second).unwrap_or_else(|| panic!("{stdout}"));
        assert!(first_position < second_position, "{stdout}");
        assert!(stdout.contains("\"error\": null"), "{stdout}");
    }

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn file_extraction_rejects_missing_and_malformed_markers() {
    let directory = extraction_fixture_directory("marker-errors");
    let cases = [
        (
            "missing.lit",
            "have a R = 1\n",
            "file extraction requires at least one `# [-extract]` block",
        ),
        (
            "unmatched-end.lit",
            "# [end of -extract]\n",
            "has no matching `# [-extract]` marker",
        ),
        (
            "nested.lit",
            "# [-extract]\n# [-extract]\nhave a R = 1\n# [end of -extract]\n",
            "nested `# [-extract]` marker",
        ),
        (
            "unclosed.lit",
            "# [-extract]\nhave a R = 1\n",
            "has no matching `# [end of -extract]` marker",
        ),
    ];

    for (name, source, expected_message) in cases {
        let file = directory.join(name);
        fs::write(&file, source).expect("write malformed marker fixture");
        let path = file.to_str().expect("fixture path is UTF-8");
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(["-extractpython", "-f", path])
            .output()
            .expect("run malformed marker extraction");
        assert!(!output.status.success(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).expect("error stdout is UTF-8");
        assert!(stdout.contains(expected_message), "{stdout}");
        assert!(stdout.contains("\"content\": null"), "{stdout}");
    }

    let no_marker = directory.join("missing.lit");
    let c_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-extractc",
            "-f",
            no_marker.to_str().expect("fixture path is UTF-8"),
        ])
        .output()
        .expect("run C extraction without markers");
    assert!(!c_output.status.success(), "{c_output:?}");

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn selected_source_errors_keep_the_original_file_line() {
    let directory = extraction_fixture_directory("source-lines");
    let file = directory.join("line-number.lit");
    fs::write(
        &file,
        "# ignored line\n# [-extract]\nhave broken R = missing_name\n# [end of -extract]\n",
    )
    .expect("write line-number fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-extractpython",
            "-f",
            file.to_str().expect("fixture path is UTF-8"),
        ])
        .output()
        .expect("run selected-source failure");
    assert!(!output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("error stdout is UTF-8");
    assert!(stdout.contains("\"line\": 3"), "{stdout}");

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn repository_extraction_does_not_require_file_markers() {
    let directory = extraction_fixture_directory("repository-control");
    fs::write(
        directory.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nmain = \"./main.lit\"\n",
    )
    .expect("write repository config");
    fs::write(directory.join("main.lit"), "have repo_value R = 3\n")
        .expect("write repository source");

    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-extractpython",
            "-r",
            directory.to_str().expect("fixture path is UTF-8"),
        ])
        .output()
        .expect("run repository extraction control");
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("repository stdout is UTF-8");
    assert!(stdout.contains("repo_value = 3.0"), "{stdout}");

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn marked_file_extraction_does_not_load_a_registered_project_prefix() {
    let directory = extraction_fixture_directory("no-project-prefix");
    fs::write(
        directory.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\n",
    )
    .expect("write repository config");
    fs::write(directory.join("before.lit"), "have shared R = 1\n")
        .expect("write repository prefix");
    let target = directory.join("target.lit");
    fs::write(
        &target,
        "# [-extract]\nhave result R = before::shared + 1\n# [end of -extract]\n",
    )
    .expect("write marked target");

    let file_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-extractpython",
            "-f",
            target.to_str().expect("fixture path is UTF-8"),
        ])
        .output()
        .expect("run marked target extraction");
    assert!(!file_output.status.success(), "{file_output:?}");
    let file_stdout = String::from_utf8(file_output.stdout).expect("file stdout is UTF-8");
    assert!(file_stdout.contains("before::shared"), "{file_stdout}");
    assert!(file_stdout.contains("not defined"), "{file_stdout}");

    let _ = fs::remove_dir_all(&directory);
}

fn extraction_fixture_directory(label: &str) -> std::path::PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "litex-code-extraction-{label}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create extraction fixture directory");
    directory
}
