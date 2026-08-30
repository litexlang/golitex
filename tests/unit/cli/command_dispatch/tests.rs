use super::super::command_handlers::read_optional_graph_save_path;
use super::super::messages::{help_message, upgrade_message};
use crate::cli::arguments::{parse_global_options, read_session_preload, validate_session_preload};
use crate::graph::GraphKind;
use crate::output::{language::OutputLanguage, style::OutputStyle};
use crate::pipeline::SessionPreload;

#[test]
fn global_cli_options_preserve_every_run_option_value() {
    let mut args = vec![
        "-compact".to_string(),
        "-strict".to_string(),
        "-summarize".to_string(),
        "-isolated".to_string(),
        "-lang".to_string(),
        "zh-Hans".to_string(),
        "-e".to_string(),
        "1 = 1".to_string(),
    ];

    let run_options = parse_global_options(&mut args).expect("global CLI options should parse");

    assert_eq!(run_options.output_style, OutputStyle::Compact);
    assert!(run_options.strict_mode);
    assert!(run_options.summarize);
    assert!(run_options.force_isolated);
    assert_eq!(
        run_options.output_language,
        OutputLanguage::SimplifiedChinese
    );
    assert_eq!(args, ["-e", "1 = 1"]);
}

#[test]
fn help_lists_upgrade_command() {
    let message = help_message();
    assert!(message.contains("litex -upgrade"));
}

#[test]
fn help_lists_strict_command() {
    let message = help_message();
    assert!(message.contains("litex -strict"));
}

#[test]
fn help_lists_summarize_command() {
    let message = help_message();
    assert!(message.contains("litex -summarize"));
}

#[test]
fn help_names_simplified_and_traditional_chinese_unambiguously() {
    let message = help_message();
    assert!(message.contains("zh|zh-Hans|zh-Hant"));
}

#[test]
fn help_lists_compact_output() {
    let message = help_message();
    assert!(message.contains("litex -compact"));
    assert!(message.contains("RuntimeError output always uses full detailed diagnostics"));
}

#[test]
fn help_lists_session_command() {
    let message = help_message();
    assert!(message.contains("litex -session"));
    assert!(message.contains("litex -session -f <file>"));
    assert!(message.contains("litex -session -before <file>"));
}

#[test]
fn session_accepts_an_optional_file_preload() {
    let args = vec![
        "-session".to_string(),
        "-f".to_string(),
        "chap4.lit".to_string(),
    ];
    let mut index = 1;

    let preload = read_session_preload(args.as_slice(), &mut index)
        .expect("session file target should parse");

    assert_eq!(
        preload,
        SessionPreload::ThroughFile("chap4.lit".to_string())
    );
    assert_eq!(index, args.len());
}

#[test]
fn session_accepts_a_before_file_preload() {
    let args = vec![
        "-session".to_string(),
        "-before".to_string(),
        "chap5.lit".to_string(),
    ];
    let mut index = 1;

    let preload = read_session_preload(args.as_slice(), &mut index)
        .expect("session before target should parse");

    assert_eq!(preload, SessionPreload::BeforeFile("chap5.lit".to_string()));
    assert_eq!(index, args.len());
}

#[test]
fn session_rejects_non_file_targets() {
    let args = vec!["-session".to_string(), "-r".to_string(), "Demo".to_string()];
    let mut index = 1;

    let error = read_session_preload(args.as_slice(), &mut index)
        .expect_err("session repository target should be rejected");

    assert!(error.contains("-f <file> or -before <file>"));
}

#[test]
fn session_rejects_combined_preload_targets() {
    let args = vec![
        "-session".to_string(),
        "-before".to_string(),
        "chap5.lit".to_string(),
        "-f".to_string(),
        "chap4.lit".to_string(),
    ];
    let mut index = 1;

    let error = read_session_preload(args.as_slice(), &mut index)
        .expect_err("session preload targets must be mutually exclusive");

    assert!(error.contains("does not accept additional arguments"));
}

#[test]
fn session_rejects_a_missing_before_file() {
    let args = vec!["-session".to_string(), "-before".to_string()];
    let mut index = 1;

    let error = read_session_preload(args.as_slice(), &mut index)
        .expect_err("a before target requires a file");

    assert!(error.contains("-before requires a value"));
}

#[test]
fn session_rejects_isolated_before_target() {
    let preload = SessionPreload::BeforeFile("chap5.lit".to_string());

    let error = validate_session_preload(true, &preload)
        .expect_err("a before target requires project discovery");

    assert!(error.contains("-isolated cannot be used with -session -before"));
    assert!(validate_session_preload(false, &preload).is_ok());
}

#[test]
fn help_lists_code_extraction_commands_without_the_retired_python_flag() {
    let message = help_message();
    assert!(message.contains("litex -extractpython <code>"));
    assert!(message.contains("litex -extractc <code>"));
    assert!(!message.contains("litex -python"));
}

#[test]
fn help_lists_single_file_lean_and_ledger_commands() {
    let message = help_message();
    assert!(message.contains("litex -f <input.lit> -isolated -lean <output.lean>"));
    assert!(!message.contains("litex -lean <input.lit> <output.lean>"));
    assert!(message.contains("litex -lean-ledger <markdown> <output.lean>"));
}

#[test]
fn help_lists_graph_command() {
    let message = help_message();
    assert!(message.contains("litex -graph -f <file> <json>"));
}

#[test]
fn help_lists_fact_graph_command() {
    let message = help_message();
    assert!(message.contains("litex -factgraph -f <file> <json>"));
}

#[test]
fn help_lists_definition_graph_command() {
    let message = help_message();
    assert!(message.contains("litex -defgraph -f <file> <json>"));
}

#[test]
fn graph_kinds_keep_their_public_flags_and_output_names() {
    for (kind, flag, output_name) in [
        (GraphKind::Result, "-graph", "graph"),
        (GraphKind::Fact, "-factgraph", "fact graph"),
        (GraphKind::Definition, "-defgraph", "definition graph"),
    ] {
        assert_eq!(kind.flag(), flag);
        assert_eq!(kind.output_name(), output_name);
    }
}

#[test]
fn shared_graph_save_path_parser_keeps_command_specific_errors() {
    for flag in ["-graph", "-factgraph", "-defgraph"] {
        let args = vec!["graph.json".to_string(), "extra".to_string()];
        let mut index = 0;
        let error = read_optional_graph_save_path(&args, &mut index, flag)
            .expect_err("a graph command accepts only one optional save path");

        assert_eq!(
            error,
            format!("unexpected argument after {flag} target: extra")
        );
    }
}

#[test]
fn help_explains_project_file_and_run_plan_modes() {
    let message = help_message();
    assert!(message.contains("module prefix through this file"));
    assert!(message.contains("litex -isolated -f <file>"));
    assert!(message.contains("recursive [export] tree"));
    assert!(message.contains("selected submodule"));
}

#[test]
fn upgrade_message_mentions_version_and_release_page() {
    let message = upgrade_message("test-version");
    assert!(message.contains("Litex version test-version"));
    assert!(message.contains("https://github.com/litexlang/golitex/releases/latest"));
    assert!(message.contains("https://litexlang.com/doc/cli#install-litex-locally"));
}
