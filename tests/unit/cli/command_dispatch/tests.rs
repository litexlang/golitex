use super::super::command_handlers::read_optional_graph_save_path;
use super::super::messages::help_message;
use crate::cli::arguments::{parse_global_options, read_session_target, validate_cli_combination};
use crate::graph::GraphKind;
use crate::output::{language::OutputLanguage, style::OutputStyle};
use crate::pipeline::{FileRunMode, SessionTarget};

#[test]
fn global_cli_flags_parse_directly_into_run_options() {
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
    assert!(run_options.is_isolated);
    assert_eq!(
        run_options.output_language,
        OutputLanguage::SimplifiedChinese
    );
    assert_eq!(args, ["-e", "1 = 1"]);
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
    assert!(!message.contains("litex -session -before <file>"));
}

#[test]
fn session_accepts_an_optional_file_preload() {
    let args = vec![
        "-session".to_string(),
        "-f".to_string(),
        "chap4.lit".to_string(),
    ];
    let mut index = 1;

    let target = read_session_target(args.as_slice(), &mut index, false)
        .expect("session file target should parse");

    assert_eq!(
        target,
        SessionTarget::File {
            path: "chap4.lit".to_string(),
            mode: FileRunMode::Project,
        }
    );
    assert_eq!(index, args.len());
}

#[test]
fn isolated_session_file_has_an_explicit_isolated_mode() {
    let args = vec![
        "-session".to_string(),
        "-f".to_string(),
        "chap5.lit".to_string(),
    ];
    let mut index = 1;

    let target = read_session_target(args.as_slice(), &mut index, true)
        .expect("isolated session file target should parse");

    assert_eq!(
        target,
        SessionTarget::File {
            path: "chap5.lit".to_string(),
            mode: FileRunMode::Isolated,
        }
    );
    assert_eq!(index, args.len());
}

#[test]
fn session_without_a_file_keeps_current_directory_and_isolated_modes_distinct() {
    let args = vec!["-session".to_string()];

    assert_eq!(
        read_session_target(args.as_slice(), &mut 1, false).unwrap(),
        SessionTarget::CurrentDirectory
    );
    assert_eq!(
        read_session_target(args.as_slice(), &mut 1, true).unwrap(),
        SessionTarget::Isolated
    );
}

#[test]
fn session_rejects_non_file_targets() {
    let args = vec!["-session".to_string(), "-r".to_string(), "Demo".to_string()];
    let mut index = 1;

    let error = read_session_target(args.as_slice(), &mut index, false)
        .expect_err("session repository target should be rejected");

    assert!(error.contains("only an optional -f <file>"));
}

#[test]
fn session_rejects_the_retired_before_target() {
    let args = vec![
        "-session".to_string(),
        "-before".to_string(),
        "chap5.lit".to_string(),
    ];
    let mut index = 1;

    let error = read_session_target(args.as_slice(), &mut index, false)
        .expect_err("the retired before target must be rejected");

    assert!(error.contains("only an optional -f <file>"));
}

#[test]
fn cli_whitelist_accepts_every_supported_command_family() {
    for (isolated, args) in [
        (false, vec![]),
        (true, vec![]),
        (false, vec!["-help"]),
        (false, vec!["-version"]),
        (false, vec!["-e", "1 = 1"]),
        (false, vec!["-f", "main.lit"]),
        (true, vec!["-f", "main.lit"]),
        (false, vec!["-r", "project"]),
        (false, vec!["-session"]),
        (true, vec!["-session"]),
        (false, vec!["-session", "-f", "main.lit"]),
        (true, vec!["-session", "-f", "main.lit"]),
        (true, vec!["-f", "main.lit", "-lean", "main.lean"]),
        (false, vec!["-latex"]),
        (false, vec!["-latex", "-e", "1 = 1"]),
        (false, vec!["-latex", "-f", "main.lit"]),
        (true, vec!["-latex", "-f", "main.lit"]),
        (false, vec!["-latex", "-r", "project"]),
        (false, vec!["-extractpython", "have a R = 1"]),
        (false, vec!["-extractpython", "-f", "main.lit"]),
        (true, vec!["-extractpython", "-f", "main.lit"]),
        (false, vec!["-extractpython", "-r", "project"]),
        (false, vec!["-extractc", "have a R = 1"]),
        (false, vec!["-extractc", "-f", "main.lit"]),
        (true, vec!["-extractc", "-f", "main.lit"]),
        (false, vec!["-extractc", "-r", "project"]),
    ] {
        let args: Vec<String> = args.into_iter().map(str::to_string).collect();
        validate_cli_combination(&args, isolated)
            .unwrap_or_else(|error| panic!("{args:?}, isolated={isolated}: {error}"));
    }

    for graph in ["-graph", "-factgraph", "-defgraph"] {
        for target in ["-e", "-f", "-r"] {
            for output in [None, Some("graph.json")] {
                let mut args = vec![graph.to_string(), target.to_string(), "target".to_string()];
                if let Some(output) = output {
                    args.push(output.to_string());
                }
                validate_cli_combination(&args, false).unwrap();
                assert_eq!(
                    validate_cli_combination(&args, true).is_ok(),
                    target == "-f",
                    "{args:?}"
                );
            }
        }
    }
}

#[test]
fn cli_whitelist_rejects_retired_malformed_and_meaningless_combinations() {
    for (isolated, args) in [
        (false, vec!["-upgrade"]),
        (false, vec!["-runner", "-e", "1 = 1"]),
        (false, vec!["-runner", "-f", "main.lit"]),
        (false, vec!["-runner", "-r", "project"]),
        (false, vec!["-lean-ledger", "notes.md", "notes.lean"]),
        (true, vec!["-help"]),
        (true, vec!["-version"]),
        (true, vec!["-e", "1 = 1"]),
        (true, vec!["-r", "project"]),
        (true, vec!["-graph", "-e", "1 = 1"]),
        (true, vec!["-defgraph", "-r", "project"]),
        (true, vec!["-latex"]),
        (true, vec!["-latex", "-e", "1 = 1"]),
        (true, vec!["-latex", "-r", "project"]),
        (true, vec!["-extractpython", "have a R = 1"]),
        (true, vec!["-extractc", "-r", "project"]),
        (false, vec!["-e"]),
        (false, vec!["-f", "main.lit", "extra"]),
        (false, vec!["-r", "project", "extra"]),
        (false, vec!["-help", "extra"]),
        (false, vec!["-session", "-r", "project"]),
        (false, vec!["-latex", "-f", "main.lit", "extra"]),
        (false, vec!["-extractpython", "-e", "1 = 1"]),
    ] {
        let args: Vec<String> = args.into_iter().map(str::to_string).collect();
        let error = validate_cli_combination(&args, isolated)
            .expect_err("unsupported CLI combination must be rejected");
        assert_eq!(error, "unsupported CLI command combination", "{args:?}");
    }
}

#[test]
fn help_lists_code_extraction_commands_without_the_retired_python_flag() {
    let message = help_message();
    assert!(message.contains("litex -extractpython <code>"));
    assert!(message.contains("litex -extractc <code>"));
    assert!(!message.contains("litex -python"));
}

#[test]
fn help_lists_only_the_single_file_lean_command() {
    let message = help_message();
    assert!(message.contains("litex -f <input.lit> -isolated -lean <output.lean>"));
    assert!(!message.contains("litex -lean <input.lit> <output.lean>"));
    assert!(!message.contains("litex -lean-ledger"));
}

#[test]
fn help_omits_retired_commands() {
    let message = help_message();
    for retired in ["litex -upgrade", "litex -runner", "litex -lean-ledger"] {
        assert!(!message.contains(retired), "{retired}");
    }
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
