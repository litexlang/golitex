use super::{run_session_loop_with_readers_and_preload, SessionPreload};
use crate::prelude::OutputLanguage;
use crate::runtime::OutputStyle;
use std::fs;
use std::io::{self, BufRead, Cursor, Write};
use std::path::{Path, PathBuf};

fn run_session_loop_with_readers(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> io::Result<()> {
    run_session_loop_with_readers_and_preload(
        stdin_reader,
        stdout_writer,
        directory,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
        SessionPreload::None,
    )
}

fn session_test_dir(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("litex-session-{}-{}", name, std::process::id()))
}

fn run_frame(id: &str, source: &str) -> String {
    format!("run {} {}\n{}", id, source.as_bytes().len(), source)
}

fn run_isolated_session(name: &str, input: String) -> String {
    run_isolated_session_with_style(name, input, OutputStyle::Normal)
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
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
    assert!(output.contains("\"id\":\"definition\",\"ok\":true"));
    assert!(output.contains("\"id\":\"proof\",\"ok\":true"));
    assert!(output.contains("y = 2"));
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(output.contains("litex-fact-graph"));
    assert!(output.contains("litex-definition-graph"));
    assert!(output.contains("\\\"kind\\\": \\\"session\\\""));

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

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::ThroughFile(preload.to_string_lossy().into_owned()),
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
    assert!(output.contains("\"id\":\"use_prefix\",\"ok\":true"));
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

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::ThroughFile(preload.to_string_lossy().into_owned()),
    )
    .expect("session must report startup failure");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"startup_error\""));
    assert!(output.contains("\"trace\""));
    assert!(output.contains("1 = 0"));
    assert!(!output.contains("\"event\":\"ready\""));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_before_file_session_skips_the_target_and_uses_its_environment() {
    let root = session_test_dir("project-before-file");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write config");
    fs::write(root.join("before.lit"), "have planned_value R = 9\n").expect("write prefix file");
    fs::write(root.join("target.lit"), "    have broken_draft R = 1\n")
        .expect("write invalid draft target");
    fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

    let input = format!(
        "{}{}{}artifacts final\nclose\n",
        run_frame("use_prefix", "before::planned_value = 9\n"),
        run_frame(
            "draft",
            "try:\n    have draft_value R = before::planned_value + 1\n",
        ),
        run_frame("use_draft", "try:\n    target::draft_value = 10\n"),
    );
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    let target = root.join("target.lit");

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
    assert!(output.contains("\"id\":\"use_prefix\",\"ok\":true"));
    assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
    assert!(
        output.contains("\"id\":\"use_draft\",\"ok\":true"),
        "{output}"
    );
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(!output.contains("unexpected indent"), "{output}");
    assert!(!output.contains("1 = 0"), "{output}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_before_file_session_reports_a_failing_predecessor() {
    let root = session_test_dir("project-before-failing-prefix");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
        root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\n",
    )
    .expect("write config");
    fs::write(root.join("before.lit"), "    have broken_prefix R = 1\n")
        .expect("write invalid prefix file");
    fs::write(root.join("target.lit"), "").expect("write target file");

    let mut stdin_reader = Cursor::new(b"close\n".to_vec());
    let mut stdout_writer = Vec::new();
    let target = root.join("target.lit");

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
    )
    .expect("session must report startup failure");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"startup_error\""), "{output}");
    assert!(output.contains("unexpected indent"), "{output}");
    assert!(!output.contains("\"event\":\"ready\""), "{output}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_before_first_export_starts_with_an_empty_prefix() {
    let root = session_test_dir("project-before-first-export");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create project fixture");
    fs::write(
        root.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
    )
    .expect("write config");
    fs::write(root.join("target.lit"), "    have broken_draft R = 1\n")
        .expect("write invalid draft target");
    fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

    let input = format!(
        "{}{}close\n",
        run_frame("draft", "try:\n    have draft_value R = 4\n"),
        run_frame("use_draft", "try:\n    target::draft_value = 4\n"),
    );
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    let target = root.join("target.lit");

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
    )
    .expect("first-export session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
    assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
    assert!(
        output.contains("\"id\":\"use_draft\",\"ok\":true"),
        "{output}"
    );
    assert!(!output.contains("unexpected indent"), "{output}");
    assert!(!output.contains("1 = 0"), "{output}");

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn project_before_file_session_follows_nested_export_order() {
    let root = session_test_dir("project-before-nested");
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("B")).expect("create nested project fixture");
    fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nroot_before = \"./root_before.lit\"\nB = \"./B\"\nroot_after = \"./root_after.lit\"\n",
        )
        .expect("write root config");
    fs::write(root.join("root_before.lit"), "have root_value R = 2\n")
        .expect("write root prefix file");
    fs::write(root.join("root_after.lit"), "1 = 0\n").expect("write root later file");
    fs::write(
            root.join("B/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write nested config");
    fs::write(
        root.join("B/before.lit"),
        "root_before::root_value = 2\nhave nested_value R = 3\n",
    )
    .expect("write nested prefix file");
    fs::write(root.join("B/target.lit"), "    have broken_draft R = 1\n")
        .expect("write invalid nested target");
    fs::write(root.join("B/after.lit"), "1 = 0\n").expect("write nested later file");

    let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame(
                "draft",
                "try:\n    root_before::root_value = 2\n    B::before::nested_value = 3\n    have draft_value R = 4\n",
            ),
            run_frame("use_draft", "try:\n    B::target::draft_value = 4\n"),
        );
    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    let target = root.join("B/target.lit");

    run_session_loop_with_readers_and_preload(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
    )
    .expect("nested session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
    assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
    assert!(
        output.contains("\"id\":\"use_draft\",\"ok\":true"),
        "{output}"
    );
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(!output.contains("unexpected indent"), "{output}");
    assert!(!output.contains("1 = 0"), "{output}");

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
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    assert!(output.contains("\"id\":\"block\",\"ok\":true"));
    assert!(!output.contains("block header missing body"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn session_continues_after_failed_try_parse() {
    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame(
            "failed_try",
            "try:\n    have candidate R\n    have candidate R\n",
        ),
        run_frame("next", "have candidate R\ncandidate = candidate\n"),
    );
    let output = run_isolated_session("failed-try-parse", input);

    assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
    assert!(output.contains("\"id\":\"next\",\"ok\":true"));
    assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
    assert!(!output.contains("\"event\":\"skipped\""));
}

#[test]
fn session_continues_after_failed_try_block_tokenization() {
    let input = format!(
        "{}{}close\n",
        run_frame(
            "failed_try",
            "try:\n    prop malformed:\n        1 = 1\n            2 = 2\n",
        ),
        run_frame("next", "try:\n    1 = 1\n"),
    );
    let output = run_isolated_session("failed-try-block-tokenization", input);

    assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
    assert!(output.contains("\"id\":\"next\",\"ok\":true"));
    assert!(!output.contains("\"event\":\"skipped\""));
}

#[test]
fn session_continues_after_failed_try_execution() {
    let input = format!(
        "{}{}artifacts final\nclose\n",
        run_frame("failed_try", "try:\n    1 = 0\n"),
        run_frame("next", "have after_try R = 2\nafter_try = 2\n"),
    );
    let output = run_isolated_session("failed-try-execution", input);

    assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
    assert!(output.contains("\"id\":\"next\",\"ok\":true"));
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

    assert!(output.contains("\"id\":\"failed\",\"ok\":false"));
    assert!(output
        .contains("\"event\":\"skipped\",\"id\":\"next\",\"error\":\"an earlier block failed\""));
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

    assert!(output.contains("\"id\":\"failed_claim\",\"ok\":false"));
    assert!(output
        .contains("\"event\":\"skipped\",\"id\":\"next\",\"error\":\"an earlier block failed\""));
}

#[test]
fn error_output_session_failed_try_is_detailed_in_every_style() {
    let mut failed_events = Vec::new();
    for output_style in [
        OutputStyle::Compact,
        OutputStyle::Normal,
        OutputStyle::Detailed,
    ] {
        let input = format!(
            "{}{}close\n",
            run_frame("failed_try", "try:\n    1 = 0\n"),
            run_frame("next", "try:\n    1 = 1\n"),
        );
        let output = run_isolated_session_with_style(
            format!("error-output-try-{:?}", output_style).as_str(),
            input,
            output_style,
        );

        let failed_event = output
            .lines()
            .find(|line| line.contains("\"id\":\"failed_try\""))
            .expect("session should emit the failed try event")
            .to_string();
        assert!(failed_event.contains("\"ok\":false"));
        assert!(failed_event.contains("\\\"phases\\\": {"));
        assert!(failed_event.contains("\\\"previous_error\\\":"));
        assert!(failed_event.contains("\\\"failed_goal\\\": \\\"1 = 0\\\""));
        assert!(failed_event.contains("\\\"unknown_result\\\": {"));
        assert!(output.contains("\"id\":\"next\",\"ok\":true"));
        assert!(!output.contains("\"event\":\"skipped\""));
        failed_events.push(failed_event);
    }

    assert_eq!(failed_events[0], failed_events[1]);
    assert_eq!(failed_events[1], failed_events[2]);
}

fn run_isolated_session_with_style(name: &str, input: String, output_style: OutputStyle) -> String {
    let root = session_test_dir(name);
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).expect("create isolated fixture");

    let mut stdin_reader = Cursor::new(input.into_bytes());
    let mut stdout_writer = Vec::new();
    run_session_loop_with_readers(
        &mut stdin_reader,
        &mut stdout_writer,
        &root,
        output_style,
        false,
        OutputLanguage::English,
        false,
    )
    .expect("session must run");

    let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
    let _ = fs::remove_dir_all(&root);
    output
}
