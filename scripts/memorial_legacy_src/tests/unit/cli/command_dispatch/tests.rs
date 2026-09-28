use super::super::command::{parse_command_line_command, CliCommand};
use super::super::messages::help_message;
use crate::graph::GraphKind;
use crate::output::{language::OutputLanguage, style::OutputDetail};
use crate::pipeline::{LitexExecution, RuntimeOptions, SummaryOption, VerifyStrictnessPolicy};

#[test]
fn canonical_cli_prefix_maps_to_one_typed_command() {
    let args = vec![
        "-strict".to_string(),
        "-lang".to_string(),
        "zh-Hans".to_string(),
        "-e".to_string(),
        "1 = 1".to_string(),
    ];

    let command = parse_command_line_command(&args).expect("canonical CLI options should parse");
    let CliCommand::Execute { target, options } = command else {
        panic!("expected typed eval command");
    };

    assert_eq!(options.execution, LitexExecution::Eval);
    assert_eq!(
        options.execution_output.verify_strictness,
        VerifyStrictnessPolicy::Strict
    );
    assert_eq!(
        options.execution_output.output_detail,
        OutputDetail::Detailed
    );
    assert!(!options.litex_execution_options().should_summarize());
    assert!(!matches!(
        options.execution,
        LitexExecution::IsolatedFile | LitexExecution::IsolatedSession
    ));
    assert_eq!(
        options.execution_output.output_language,
        OutputLanguage::SimplifiedChinese
    );
    assert_eq!(target, "1 = 1");
}

#[test]
fn graph_tracer_resolves_every_argument_before_dispatch() {
    // Before this migration, parsing stopped at LitexExecutionOptions + command_index and run_cli
    // interpreted the graph, target, and save path from the same raw argv a second time.
    let args = [
        "-strict",
        "-isolated",
        "-graph",
        "-f",
        "main.lit",
        "graph.json",
    ]
    .map(str::to_string);

    let command = parse_command_line_command(&args).expect("graph tracer should parse");
    let CliCommand::Graph {
        kind,
        target,
        save_path,
        options,
    } = command
    else {
        panic!("expected typed graph command");
    };

    assert_eq!(kind, GraphKind::Result);
    assert_eq!(target, "main.lit");
    assert_eq!(save_path.as_deref(), Some("graph.json"));
    assert_eq!(options.execution, LitexExecution::IsolatedFile);
    assert_eq!(
        options.execution_output.verify_strictness,
        VerifyStrictnessPolicy::Strict
    );
    assert_eq!(
        options.execution_output.output_detail,
        OutputDetail::Detailed
    );
    assert!(matches!(
        options.execution,
        LitexExecution::IsolatedFile | LitexExecution::IsolatedSession
    ));
}

#[test]
fn strictness_is_carried_by_execution_options() {
    for options in [RuntimeOptions::ordinary(
        OutputDetail::Normal,
        OutputLanguage::English,
        SummaryOption::None,
    )] {
        assert!(!options.is_strict(), "{:?}", options.verify_strictness());
    }

    for options in [RuntimeOptions::strict(
        OutputDetail::Normal,
        OutputLanguage::English,
        SummaryOption::None,
    )] {
        assert!(options.is_strict(), "{:?}", options.verify_strictness());
    }
}

#[test]
fn help_lists_strict_command() {
    let message = help_message();
    assert!(message.contains("\"usage\": \"-strict\""));
}

#[test]
fn help_omits_retired_output_flags() {
    let message = help_message();
    for retired in ["-compact", "-detail", "-summarize"] {
        assert!(!message.contains(retired), "{retired}");
    }
}

#[test]
fn help_names_simplified_and_traditional_chinese_unambiguously() {
    let message = help_message();
    assert!(message.contains("\"usage\": \"-lang <language>\""));
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
    let args = ["-session", "-f", "chap4.lit"].map(str::to_string);
    let CliCommand::Session { file_path, options } =
        parse_command_line_command(&args).expect("session file target should parse")
    else {
        panic!("expected typed session command");
    };

    assert_eq!(file_path.as_deref(), Some("chap4.lit"));
    assert_eq!(options.execution, LitexExecution::Session);
}

#[test]
fn isolated_session_file_has_an_explicit_isolated_mode() {
    let args = ["-isolated", "-session", "-f", "chap5.lit"].map(str::to_string);
    let CliCommand::Session { file_path, options } =
        parse_command_line_command(&args).expect("isolated session file target should parse")
    else {
        panic!("expected typed session command");
    };

    assert_eq!(file_path.as_deref(), Some("chap5.lit"));
    assert_eq!(options.execution, LitexExecution::IsolatedSession);
}

#[test]
fn session_without_a_file_keeps_current_directory_and_isolated_modes_distinct() {
    let project = ["-session"].map(str::to_string);
    let isolated = ["-isolated", "-session"].map(str::to_string);

    let CliCommand::Session {
        file_path: project_file,
        options: project_options,
    } = parse_command_line_command(&project).unwrap()
    else {
        panic!("expected typed project session");
    };
    let CliCommand::Session {
        file_path: isolated_file,
        options: isolated_options,
    } = parse_command_line_command(&isolated).unwrap()
    else {
        panic!("expected typed isolated session");
    };

    assert!(project_file.is_none());
    assert_eq!(project_options.execution, LitexExecution::Session);
    assert!(isolated_file.is_none());
    assert_eq!(isolated_options.execution, LitexExecution::IsolatedSession);
}

#[test]
fn session_rejects_non_file_targets() {
    let args = ["-session", "-r", "Demo"].map(str::to_string);
    let error = parse_command_line_command(&args)
        .expect_err("session repository target should be rejected");

    assert_eq!(error, "unsupported CLI command combination");
}

#[test]
fn session_rejects_the_retired_before_target() {
    let args = ["-session", "-before", "chap5.lit"].map(str::to_string);
    let error =
        parse_command_line_command(&args).expect_err("the retired before target must be rejected");

    assert_eq!(error, "unsupported CLI command combination");
}

#[test]
fn cli_whitelist_accepts_every_supported_command_family() {
    for args in [
        vec![],
        vec!["-strict"],
        vec!["-help"],
        vec!["-version"],
        vec!["-e", "1 = 1"],
        vec!["-strict", "-e", "1 = 1"],
        vec!["-f", "main.lit"],
        vec!["-isolated", "-f", "main.lit"],
        vec!["-strict", "-isolated", "-f", "main.lit"],
        vec!["-r", "project"],
        vec!["-session"],
        vec!["-strict", "-session"],
        vec!["-isolated", "-session"],
        vec!["-session", "-f", "main.lit"],
        vec!["-isolated", "-session", "-f", "main.lit"],
        vec!["-isolated", "-f", "main.lit", "-lean", "main.lean"],
        vec!["-latex"],
        vec!["-latex", "-e", "1 = 1"],
        vec!["-latex", "-f", "main.lit"],
        vec!["-isolated", "-latex", "-f", "main.lit"],
        vec!["-latex", "-r", "project"],
        vec!["-extractpython", "have a R = 1"],
        vec!["-extractpython", "-f", "main.lit"],
        vec!["-isolated", "-extractpython", "-f", "main.lit"],
        vec!["-extractpython", "-r", "project"],
        vec!["-extractc", "have a R = 1"],
        vec!["-extractc", "-f", "main.lit"],
        vec!["-isolated", "-extractc", "-f", "main.lit"],
        vec!["-extractc", "-r", "project"],
    ] {
        let args: Vec<String> = args.into_iter().map(str::to_string).collect();
        parse_command_line_command(&args).unwrap_or_else(|error| panic!("{args:?}: {error}"));
    }

    for graph in ["-graph", "-factgraph", "-defgraph"] {
        for target in ["-e", "-f", "-r"] {
            for output in [None, Some("graph.json")] {
                let mut args = vec![graph.to_string(), target.to_string(), "target".to_string()];
                if let Some(output) = output {
                    args.push(output.to_string());
                }
                parse_command_line_command(&args).unwrap();

                let mut strict = vec!["-strict".to_string()];
                if target == "-f" {
                    strict.push("-isolated".to_string());
                }
                strict.extend(args);
                parse_command_line_command(&strict).unwrap();
            }
        }
    }
}

#[test]
fn cli_whitelist_rejects_retired_malformed_and_meaningless_combinations() {
    for args in [
        vec!["-upgrade"],
        vec!["-runner", "-e", "1 = 1"],
        vec!["-runner", "-f", "main.lit"],
        vec!["-runner", "-r", "project"],
        vec!["-lean-ledger", "notes.md", "notes.lean"],
        vec!["-strict", "-help"],
        vec!["-strict", "-version"],
        vec!["-strict", "-latex", "-f", "main.lit"],
        vec!["-strict", "-extractpython", "-f", "main.lit"],
        vec!["-isolated"],
        vec!["-isolated", "-e", "1 = 1"],
        vec!["-isolated", "-r", "project"],
        vec!["-isolated", "-graph", "-e", "1 = 1"],
        vec!["-isolated", "-defgraph", "-r", "project"],
        vec!["-isolated", "-latex"],
        vec!["-isolated", "-latex", "-e", "1 = 1"],
        vec!["-isolated", "-extractpython", "have a R = 1"],
        vec!["-isolated", "-extractc", "-r", "project"],
        vec!["-summarize"],
        vec!["-summarize", "-session"],
        vec!["-summarize", "-graph", "-f", "main.lit"],
        vec!["-compact", "-e", "1 = 1"],
        vec!["-detail", "-e", "1 = 1"],
        vec!["-e"],
        vec!["-f", "main.lit", "extra"],
        vec!["-r", "project", "extra"],
        vec!["-help", "extra"],
        vec!["-session", "-r", "project"],
        vec!["-latex", "-f", "main.lit", "extra"],
        vec!["-extractpython", "-e", "1 = 1"],
        vec!["-e", "1 = 1", "-strict"],
        vec!["-strict", "-strict", "-e", "1 = 1"],
        vec!["-strict", "-compact", "-e", "1 = 1"],
        vec!["-lang", "en", "-help"],
        vec!["-isolated", "-f", "main.lit", "-strict"],
    ] {
        let args: Vec<String> = args.into_iter().map(str::to_string).collect();
        let error = parse_command_line_command(&args)
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
    assert!(message.contains("litex -isolated -f <input.lit> -lean <output.lean>"));
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
    assert!(message.contains("litex -graph <-e|-f|-r> <target> [output.json]"));
}

#[test]
fn help_lists_fact_graph_command() {
    let message = help_message();
    assert!(message.contains("litex -factgraph <-e|-f|-r> <target> [output.json]"));
}

#[test]
fn help_lists_definition_graph_command() {
    let message = help_message();
    assert!(message.contains("litex -defgraph <-e|-f|-r> <target> [output.json]"));
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
fn graph_command_rejects_more_than_one_save_path() {
    for flag in ["-graph", "-factgraph", "-defgraph"] {
        let args = [flag, "-f", "main.lit", "graph.json", "extra"].map(str::to_string);
        let error = parse_command_line_command(&args)
            .expect_err("a graph command accepts only one optional save path");

        assert_eq!(error, "unsupported CLI command combination");
    }
}

#[test]
fn help_explains_project_file_and_run_plan_modes() {
    let message = help_message();
    assert!(message.contains("\"kind\": \"help\""));
    assert!(message.contains("\"entries\": ["));
    assert!(message.contains(
        "Run a file using project context when directly configured, otherwise in isolation."
    ));
    assert!(message.contains("litex -isolated -f <file>"));
    assert!(message.contains("litex -r <directory>"));
}
