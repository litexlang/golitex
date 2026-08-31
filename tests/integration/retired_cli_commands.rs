use std::process::Command;

#[test]
fn retired_placeholder_commands_are_rejected_and_absent_from_help() {
    for flag in [
        "-fmt",
        "-install",
        "-uninstall",
        "-list",
        "-update",
        "-tutorial",
        "-trace-pipeline",
        "-trust-before-line",
        "-python",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .arg(flag)
            .output()
            .expect("run litex CLI");

        assert_eq!(output.status.code(), Some(2), "{flag}");
        let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
        assert!(
            stderr.contains("unsupported CLI command combination"),
            "{stderr}"
        );
        let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
        assert!(
            !stdout.contains(format!("litex {flag}").as_str()),
            "{stdout}"
        );
    }
}
