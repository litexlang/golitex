use std::path::PathBuf;
use std::process::{Command, Output};

#[test]
fn verifier_errors_use_the_canonical_detailed_run_json() {
    let normal = run_litex(&["-e", "1 = 0"]);

    assert_eq!(normal.status.code(), Some(1));

    let normal_stdout = String::from_utf8(normal.stdout).expect("normal output must be UTF-8");

    assert!(normal_stdout.contains("\"kind\": \"run\""));
    assert!(normal_stdout.contains("\"ok\": false"));
    assert!(normal_stdout.contains("\"kind\": \"verify_error\""));
    assert!(!normal_stdout.contains("\"phases\":"));
    assert!(normal_stdout.contains("\"previous_error\":"));
    assert!(normal_stdout.contains("\"failed_goal\": \"1 = 0\""));
    assert!(normal_stdout.contains("\"unknown_result\": {"));
    assert!(!normal_stdout.contains("\"summary\":"));
}

#[test]
fn successful_runs_use_the_canonical_detailed_run_json_without_summary() {
    let normal = run_litex(&["-e", "1 = 1"]);

    assert!(normal.status.success());

    let normal_stdout = String::from_utf8(normal.stdout).expect("normal output must be UTF-8");

    assert!(normal_stdout.contains("\"kind\": \"run\""));
    assert!(normal_stdout.contains("\"ok\": true"));
    assert!(normal_stdout.contains("\"statement_results\": ["));
    assert!(!normal_stdout.contains("\"schema\":"));
    assert!(!normal_stdout.contains("\"summary\":"));
    assert!(normal_stdout.contains("\"outcome\": \"success\""));
    assert!(normal_stdout.contains("\"verification\": {"));
    assert!(normal_stdout.contains("\"well_definedness\": {"));
    assert!(normal_stdout.contains("\"store\": {"));
    assert!(!normal_stdout.contains(&["execution", "trace"].join("_")));
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
