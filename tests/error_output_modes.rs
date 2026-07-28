use std::path::PathBuf;
use std::process::{Command, Output};

#[test]
fn error_output_cli_modes_emit_the_same_detailed_runtime_error() {
    let compact = run_litex(&["-compact", "-e", "1 = 0"]);
    let normal = run_litex(&["-e", "1 = 0"]);
    let detailed = run_litex(&["-detail", "-e", "1 = 0"]);

    assert_eq!(compact.status.code(), normal.status.code());
    assert_eq!(normal.status.code(), detailed.status.code());

    let compact_stdout = String::from_utf8(compact.stdout).expect("compact output must be UTF-8");
    let normal_stdout = String::from_utf8(normal.stdout).expect("normal output must be UTF-8");
    let detailed_stdout =
        String::from_utf8(detailed.stdout).expect("detailed output must be UTF-8");

    assert_eq!(compact_stdout.trim(), normal_stdout.trim());
    assert_eq!(normal_stdout.trim(), detailed_stdout.trim());
    assert!(detailed_stdout.contains("\"phases\": {"));
    assert!(detailed_stdout.contains("\"previous_error\":"));
    assert!(detailed_stdout.contains("\"failed_goal\": \"1 = 0\""));
    assert!(detailed_stdout.contains("\"unknown_result\": {"));
}

#[test]
fn error_output_cli_modes_keep_their_selected_success_projection() {
    let compact = run_litex(&["-compact", "-e", "1 = 1"]);
    let normal = run_litex(&["-e", "1 = 1"]);
    let detailed = run_litex(&["-detail", "-e", "1 = 1"]);

    assert!(compact.status.success());
    assert!(normal.status.success());
    assert!(detailed.status.success());

    let compact_stdout = String::from_utf8(compact.stdout).expect("compact output must be UTF-8");
    let normal_stdout = String::from_utf8(normal.stdout).expect("normal output must be UTF-8");
    let detailed_stdout =
        String::from_utf8(detailed.stdout).expect("detailed output must be UTF-8");

    assert!(!compact_stdout.contains("\"verification\": {"));
    assert!(!compact_stdout.contains("\"phases\": {"));
    assert!(normal_stdout.contains("\"why_verified\": {"));
    assert!(!normal_stdout.contains("\"phases\": {"));
    assert!(detailed_stdout.contains("\"verification\": {"));
    assert!(detailed_stdout.contains("\"phases\": {"));
}

fn run_litex(args: &[&str]) -> Output {
    Command::new(litex_binary())
        .args(args)
        .output()
        .expect("run Litex CLI")
}

fn litex_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_litex") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/litex")
}
