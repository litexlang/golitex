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
fn isolated_file_conversions_read_the_standalone_source() {
    let directory = std::env::temp_dir().join(format!(
        "litex-isolated-file-conversions-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create isolated conversion fixture");
    let file = directory.join("standalone.lit");
    fs::write(&file, "have a R = 1\n").expect("write standalone Litex source");
    let path = file.to_str().expect("fixture path is UTF-8");

    let python = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-isolated", "-extractpython", "-f", path])
        .output()
        .expect("extract Python from isolated file");
    assert!(python.status.success(), "{python:?}");
    let python_stdout = String::from_utf8(python.stdout).expect("Python stdout is UTF-8");
    assert!(python_stdout.contains("\"format\": \"python\""));
    assert!(python_stdout.contains("\"content\": \"a = 1.0\""));
    assert!(python_stdout.contains("\"error\": null"));

    let latex = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-isolated", "-latex", "-f", path])
        .output()
        .expect("render LaTeX from isolated file");
    assert!(latex.status.success(), "{latex:?}");
    let latex_stdout = String::from_utf8(latex.stdout).expect("LaTeX stdout is UTF-8");
    assert!(latex_stdout.contains("\"format\": \"latex\""));
    assert!(latex_stdout.contains("\"content\":"));
    assert!(latex_stdout.contains("\"error\": null"));

    let _ = fs::remove_dir_all(&directory);
}
