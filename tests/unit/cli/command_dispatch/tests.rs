use super::super::command_handlers::read_optional_graph_save_path;
use super::super::messages::{help_message, upgrade_message};
use crate::cli::arguments::{
    read_session_preload, remove_trust_before_line_flag, validate_session_preload,
    validate_trust_before_line_invocation,
};
use crate::graph::GraphKind;
use crate::pipeline::SessionPreload;

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
fn help_lists_trust_before_line_command() {
    let message = help_message();
    assert!(message.contains("litex -f <file> -trust-before-line <X>"));
    assert!(message.contains("exact top-level statement header line"));
    assert!(message.contains("cannot be used with -strict"));
}

#[test]
fn trust_before_line_accepts_a_positive_ascii_decimal() {
    let mut args = vec![
        "-trust-before-line".to_string(),
        "420".to_string(),
        "-f".to_string(),
        "chapter.lit".to_string(),
    ];

    let line = remove_trust_before_line_flag(&mut args).expect("a positive line should parse");

    assert_eq!(line, Some(420));
    assert_eq!(args, vec!["-f".to_string(), "chapter.lit".to_string()]);
}

#[test]
fn trust_before_line_accepts_the_flag_after_the_file_target() {
    let mut args = vec![
        "-f".to_string(),
        "chapter.lit".to_string(),
        "-trust-before-line".to_string(),
        "420".to_string(),
    ];

    let line = remove_trust_before_line_flag(&mut args)
        .expect("the global flag may follow the primary command");

    assert_eq!(line, Some(420));
    assert_eq!(args, vec!["-f".to_string(), "chapter.lit".to_string()]);
}

#[test]
fn trust_before_line_rejects_a_missing_value() {
    let mut args = vec![
        "-f".to_string(),
        "chapter.lit".to_string(),
        "-trust-before-line".to_string(),
    ];

    let error = remove_trust_before_line_flag(&mut args).expect_err("the flag requires a value");

    assert!(error.contains("requires a positive ASCII decimal line number"));
}

#[test]
fn trust_before_line_rejects_zero_negative_and_non_ascii_decimal_values() {
    for value in ["0", "-1", "+1", "1.5", "１２"] {
        let mut args = vec!["-trust-before-line".to_string(), value.to_string()];

        let error = remove_trust_before_line_flag(&mut args)
            .expect_err("only a positive ASCII decimal should parse");

        assert!(
            error.contains("positive ASCII decimal") || error.contains("greater than 0"),
            "unexpected error for {value}: {error}"
        );
    }
}

#[test]
fn trust_before_line_rejects_overflow() {
    let overflow = format!("{}0", usize::MAX);
    let mut args = vec!["-trust-before-line".to_string(), overflow];

    let error = remove_trust_before_line_flag(&mut args).expect_err("overflow should be rejected");

    assert!(error.contains("exceeds the supported range"));
}

#[test]
fn trust_before_line_rejects_duplicate_flags() {
    let mut args = vec![
        "-trust-before-line".to_string(),
        "10".to_string(),
        "-f".to_string(),
        "chapter.lit".to_string(),
        "-trust-before-line".to_string(),
        "20".to_string(),
    ];

    let error =
        remove_trust_before_line_flag(&mut args).expect_err("the flag must not be repeated");

    assert!(error.contains("may be provided only once"));
}

#[test]
fn trust_before_line_accepts_only_an_exact_direct_file_command() {
    let file_args = vec!["-f".to_string(), "chapter.lit".to_string()];
    assert!(validate_trust_before_line_invocation(&file_args, false, Some(420)).is_ok());

    for args in [
        vec!["-r".to_string(), "Demo".to_string()],
        vec!["-e".to_string(), "1 = 1".to_string()],
        vec!["-session".to_string()],
        vec![
            "-runner".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
        ],
        vec![
            "-graph".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
            "graph.json".to_string(),
        ],
        vec![
            "-python".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
        ],
        vec![
            "-latex".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
        ],
        vec![
            "-f".to_string(),
            "chapter.lit".to_string(),
            "extra".to_string(),
        ],
        vec!["-f".to_string(), "-session".to_string()],
    ] {
        let error = validate_trust_before_line_invocation(&args, false, Some(420))
            .expect_err("only exact direct file commands should be accepted");
        assert!(
            error.contains("supported only") || error.contains("direct -f <file> target"),
            "unexpected error for {args:?}: {error}"
        );
    }
}

#[test]
fn trust_before_line_rejects_strict_mode() {
    let args = vec!["-f".to_string(), "chapter.lit".to_string()];

    let error = validate_trust_before_line_invocation(&args, true, Some(420))
        .expect_err("strict and trusted-prefix execution are incompatible");

    assert!(error.contains("cannot be used with -strict"));
}

#[test]
fn trust_before_line_validation_does_not_change_flagless_commands() {
    let args = vec![
        "-runner".to_string(),
        "-f".to_string(),
        "chapter.lit".to_string(),
    ];

    assert!(validate_trust_before_line_invocation(&args, true, None).is_ok());
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
fn help_lists_python_command() {
    let message = help_message();
    assert!(message.contains("litex -python -f <file>"));
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
}
