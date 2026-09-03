use super::run_session_loop_with_readers_and_target;
use crate::prelude::{OutputDetail, OutputLanguage, SessionTarget};
use crate::runtime::{ExecutionOption, RunOption, RunOptions, SummaryOption};
use std::fs;
use std::io::{self, BufRead, Cursor, Write};
use std::path::{Path, PathBuf};

fn run_session_loop_with_readers(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    output_detail: OutputDetail,
    strict_mode: bool,
    output_language: OutputLanguage,
    isolated: bool,
) -> io::Result<()> {
    let run = if strict_mode {
        RunOption::StrictExecute(if isolated {
            ExecutionOption::IsolatedSession
        } else {
            ExecutionOption::Session
        })
    } else {
        RunOption::Execute(if isolated {
            ExecutionOption::IsolatedSession
        } else {
            ExecutionOption::Session
        })
    };
    run_session_loop_with_readers_and_target(
        stdin_reader,
        stdout_writer,
        directory,
        RunOptions::new(run, output_detail, output_language, SummaryOption::None),
        if isolated {
            SessionTarget::Isolated
        } else {
            SessionTarget::CurrentDirectory
        },
    )
}

fn session_test_dir(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("litex-session-{}-{}", name, std::process::id()))
}

fn run_frame(id: &str, source: &str) -> String {
    format!("run {} {}\n{}", id, source.as_bytes().len(), source)
}

fn run_isolated_session(name: &str, input: String) -> String {
    run_isolated_session_with_style(name, input, OutputDetail::Normal)
}

#[test]
fn project_session_keeps_previous_blocks() {
    let root = session_test_dir("project");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
        root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nmain = \"./main.lit\"\n",
    )
    .expect("write config");
    fs::write(root.join("main.lit"), "have planned_value R = 9\n").expect("write plan file");

    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame("definition", "have x R = 1\n"),
        run_frame("proof", "have y R = x + 1\ny = 2\n"),
    );
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();

    run_session_loop_with_readers(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputDetail::Normal,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\""));
    assert!(output.contains("\"content\":{\"mode\":\"project\"}"));
    assert!(output.contains("\"event\":\"result\",\"id\":\"definition\""));
    assert!(output.contains("\"event\":\"result\",\"id\":\"proof\""));
    assert!(output.contains("y = 2"));
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(output.contains("litex-fact-graph"));
    assert!(output.contains("litex-definition-graph"));
    assert!(output.contains("\"kind\":\"session\""));
    assert!(output.contains("session"), "{output}");
    assert!(!output.contains("<session>"), "{output}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_file_session_preloads_registered_prefix() {
    let root = session_test_dir("project-file-preload");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
        root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\nafter = \"./after.lit\"\n",
    )
    .expect("write config");
    fs::write(root.join("before.lit"), "have planned_value R = 9\n").expect("write prefix file");
    fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

    let input = format!(
        "{}artifacts final\nclose\n",
        run_frame("use_prefix", "before::planned_value = 9\n"),
    );
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    let preload = root.join("before.lit");

    run_session_loop_with_readers_and_target(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        RunOptions::default(),
        SessionTarget::File {
            path: preload.to_string_lossy().into_owned(),
        },
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\""));
    assert!(output.contains("\"content\":{\"mode\":\"project\"}"));
    assert!(output.contains("\"event\":\"result\",\"id\":\"use_prefix\""));
    assert!(output.contains("before::planned_value = 9"));
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(!output.contains("1 = 0"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_file_session_reports_a_failing_prefix_before_ready() {
    let root = session_test_dir("project-file-preload-failure");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
        root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nbroken = \"./broken.lit\"\n",
    )
    .expect("write config");
    fs::write(root.join("broken.lit"), "1 = 0\n").expect("write broken prefix file");

    let mut stdin_reader = Cursor::new(b"close\n".to_vec());
    let mut stdout_writer = Vec::new();
    let preload = root.join("broken.lit");

    run_session_loop_with_readers_and_target(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        RunOptions::default(),
        SessionTarget::File {
            path: preload.to_string_lossy().into_owned(),
        },
    )
    .expect("session must report startup failure");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"startup_error\""));
    assert!(output.contains("\"kind\":\"verify_error\""));
    assert!(output.contains("1 = 0"));
    assert!(!output.contains("\"event\":\"ready\""));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn explicit_isolated_session_ignores_a_broken_current_directory_project() {
    let root = session_test_dir("explicit-isolated");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create isolated fixture");
    fs::write(root.join("litex.config"), "not a valid project config\n")
        .expect("write broken config");

    let input = format!("{}close\n", run_frame("proof", "1 = 1\n"));
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    run_session_loop_with_readers(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputDetail::Normal,
        false,
        OutputLanguage::English,
        true,
    )
    .expect("isolated session must bypass project discovery");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\""));
    assert!(output.contains("\"content\":{\"mode\":\"isolated\"}"));
    assert!(output.contains("\"event\":\"result\",\"id\":\"proof\""));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn isolated_file_session_preloads_the_standalone_file() {
    let root = session_test_dir("isolated-file");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create isolated fixture");
    let preload = root.join("scratch.lit");
    fs::write(&preload, "have from_file R = 7\n").expect("write isolated file");

    let input = format!("{}close\n", run_frame("use_file", "from_file = 7\n"));
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    run_session_loop_with_readers_and_target(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        RunOptions::default(),
        SessionTarget::IsolatedFile {
            path: preload.to_string_lossy().into_owned(),
        },
    )
    .expect("isolated file session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\""));
    assert!(output.contains("\"content\":{\"mode\":\"isolated\"}"));
    assert!(output.contains("\"event\":\"result\",\"id\":\"use_file\""));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn plain_file_session_auto_selects_isolated_context_without_config() {
    let root = session_test_dir("auto-isolated-file");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create standalone fixture");
    let preload = root.join("scratch.lit");
    fs::write(&preload, "have from_file R = 7\n").expect("write standalone file");

    let input = format!("{}close\n", run_frame("use_file", "from_file = 7\n"));
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    run_session_loop_with_readers_and_target(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        RunOptions::execute(ExecutionOption::Session),
        SessionTarget::File {
            path: preload.to_string_lossy().into_owned(),
        },
    )
    .expect("auto-isolated file session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\""));
    assert!(output.contains("\"content\":{\"mode\":\"isolated\"}"));
    assert!(output.contains("\"event\":\"result\",\"id\":\"use_file\""));
    assert!(output.contains("from_file = 7"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn session_accepts_a_multiline_code_block() {
    let root = session_test_dir("multiline");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create isolated fixture");

    let input = format!("{}close\n", run_frame("block", "sketch:\n    1 = 1\n"));
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();

    run_session_loop_with_readers(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputDetail::Normal,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"result\",\"id\":\"block\""));
    assert!(!output.contains("block header missing body"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn session_run_frames_do_not_dispatch_terminal_import_commands() {
    let input = format!(
        "{}{}close\n",
        run_frame("import", "import std basics\n"),
        run_frame("next", "1 = 1\n"),
    );
    let output = run_isolated_session("source-only-import-boundary", input);

    assert!(
        output
            .contains("\"ok\":false,\"stream\":\"session\",\"event\":\"result\",\"id\":\"import\""),
        "{output}"
    );
    assert!(
        output.contains("`import` is a terminal command, not a Litex statement"),
        "{output}"
    );
    assert!(!output.contains("terminal import\""), "{output}");
    assert!(output.contains("\"event\":\"skipped\",\"id\":\"next\""));
}

#[test]
fn session_stops_when_try_source_never_forms_an_ast() {
    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame(
            "failed_try",
            "try:\n    have candidate R\n    have candidate R\n",
        ),
        run_frame("next", "have candidate R\ncandidate = candidate\n"),
    );
    let output = run_isolated_session("failed-try-parse", input);

    assert!(output.contains(
        "\"ok\":false,\"stream\":\"session\",\"event\":\"result\",\"id\":\"failed_try\""
    ));
    assert!(output.contains("\"event\":\"skipped\",\"id\":\"next\""));
    assert!(output.contains("\"event\":\"artifacts_unavailable\",\"id\":\"final\""));
}

#[test]
fn session_stops_when_try_source_cannot_be_tokenized() {
    let input = format!(
        "{}{}close\n",
        run_frame(
            "failed_try",
            "try:\n    prop malformed:\n        1 = 1\n            2 = 2\n",
        ),
        run_frame("next", "try:\n    1 = 1\n"),
    );
    let output = run_isolated_session("failed-try-block-tokenization", input);

    assert!(output.contains(
        "\"ok\":false,\"stream\":\"session\",\"event\":\"result\",\"id\":\"failed_try\""
    ));
    assert!(output.contains("\"event\":\"skipped\",\"id\":\"next\""));
}

#[test]
fn session_continues_after_a_try_rolls_back() {
    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame("failed_try", "try:\n    1 = 0\n"),
        run_frame("next", "have after_try R = 2\nafter_try = 2\n"),
    );
    let output = run_isolated_session("failed-try-execution", input);

    assert!(output
        .contains("\"ok\":true,\"stream\":\"session\",\"event\":\"result\",\"id\":\"failed_try\""));
    assert!(output.contains("\"kind\":\"RolledBack\""));
    assert!(output.contains("\"event\":\"result\",\"id\":\"next\""));
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(!output.contains("\"event\":\"skipped\""));
}

#[test]
fn session_stops_after_failed_non_try_statement() {
    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame("failed", "have ordinary R\nhave ordinary R\n"),
        run_frame("next", "1 = 1\n"),
    );
    let output = run_isolated_session("failed-non-try", input);

    assert!(output
        .contains("\"ok\":false,\"stream\":\"session\",\"event\":\"result\",\"id\":\"failed\""));
    assert!(output.contains("\"event\":\"skipped\",\"id\":\"next\""));
    assert!(output.contains("\"kind\":\"earlier_block_failed\""));
    assert!(output.contains("\"event\":\"artifacts_unavailable\",\"id\":\"final\""));
}

#[test]
fn nested_try_does_not_make_outer_statement_recoverable() {
    let input = format!(
        "{}{}close\n",
        run_frame(
            "failed_claim",
            "claim:\n    ? 1 = 1\n    try:\n        have nested R\n        have nested R\n",
        ),
        run_frame("next", "1 = 1\n"),
    );
    let output = run_isolated_session("nested-failed-try", input);

    assert!(output.contains(
        "\"ok\":false,\"stream\":\"session\",\"event\":\"result\",\"id\":\"failed_claim\""
    ));
    assert!(output.contains("\"event\":\"skipped\",\"id\":\"next\""));
    assert!(output.contains("\"kind\":\"earlier_block_failed\""));
}

#[test]
fn rolled_back_try_output_is_detailed_in_every_style() {
    let mut rollback_events = Vec::new();
    for output_detail in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let input = format!(
            "{}{}close\n",
            run_frame("failed_try", "try:\n    1 = 0\n"),
            run_frame("next", "try:\n    1 = 1\n"),
        );
        let output = run_isolated_session_with_style(
            format!("error-output-try-{:?}", output_detail).as_str(),
            input,
            output_detail,
        );

        let rollback_event = output
            .lines()
            .find(|line| line.contains("\"id\":\"failed_try\""))
            .expect("session should emit the rolled-back try event")
            .to_string();
        assert!(rollback_event.contains("\"ok\":true"));
        assert!(rollback_event.contains("\"kind\":\"RolledBack\""));
        assert!(!rollback_event.contains("\"phases\":"));
        assert!(rollback_event.contains("\"previous_error\":"));
        assert!(rollback_event.contains("\"failed_goal\":\"1 = 0\""));
        assert!(rollback_event.contains("\"unknown_result\":"));
        assert!(output.contains("\"event\":\"result\",\"id\":\"next\""));
        assert!(!output.contains("\"event\":\"skipped\""));
        rollback_events.push(rollback_event);
    }

    assert_eq!(rollback_events[0], rollback_events[1]);
    assert_eq!(rollback_events[1], rollback_events[2]);
}

fn run_isolated_session_with_style(
    name: &str,
    input: String,
    output_detail: OutputDetail,
) -> String {
    let root = session_test_dir(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create isolated fixture");

    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    run_session_loop_with_readers(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        output_detail,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    let _ = fs::remove_dir_all(&root);
    output
}
