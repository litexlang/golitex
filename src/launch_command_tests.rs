use crate::launch_command::{parse_launch_command, LatexInput, LaunchCommand, OutputLanguage};
use std::path::PathBuf;

fn args(parts: &[&str]) -> Vec<String> {
    parts.iter().map(|s| (*s).to_string()).collect()
}

#[test]
fn parses_eval_command() {
    let command = parse_launch_command(&args(&["-e", "1 + 1 = 2"])).unwrap();
    assert_eq!(
        command,
        LaunchCommand::Eval {
            code: "1 + 1 = 2".to_string(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        }
    );
}

#[test]
fn parses_negative_leading_eval_code_and_surrounding_flags() {
    for parts in [
        vec!["-e", "-2 < 0"],
        vec!["-strict", "-e", "-2 < 0"],
        vec!["-e", "-2 < 0", "-strict"],
    ] {
        assert_eq!(
            parse_launch_command(&args(&parts)).unwrap(),
            LaunchCommand::Eval {
                code: "-2 < 0".to_string(),
                session: false,
                strict: parts.contains(&"-strict"),
                language: OutputLanguage::English,
            }
        );
    }
}

#[test]
fn eval_operand_is_source_even_when_it_spells_a_cli_option() {
    for code in [
        "-strict",
        "--strict",
        "-session",
        "--session",
        "-lang",
        "--lang",
        "-f",
        "-r",
        "-e",
        "-help",
        "-unknown",
    ] {
        assert_eq!(
            parse_launch_command(&args(&["-e", code])).unwrap(),
            LaunchCommand::Eval {
                code: code.to_string(),
                session: false,
                strict: false,
                language: OutputLanguage::English,
            }
        );
    }
    assert_eq!(
        parse_launch_command(&args(&["-lang", "zh", "-e", "-strict", "-session"])).unwrap(),
        LaunchCommand::Eval {
            code: "-strict".to_string(),
            session: true,
            strict: false,
            language: OutputLanguage::Chinese,
        }
    );
}

#[test]
fn parses_session_and_strict_with_file() {
    assert_eq!(
        parse_launch_command(&args(&["-strict", "-f", "a.lit", "-session"])).unwrap(),
        LaunchCommand::File {
            path: PathBuf::from("a.lit"),
            session: true,
            strict: true,
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-session", "-f", "a.lit"])).unwrap(),
        LaunchCommand::File {
            path: PathBuf::from("a.lit"),
            session: true,
            strict: false,
            language: OutputLanguage::English,
        }
    );
}

#[test]
fn parses_help_version_and_repl() {
    assert_eq!(
        parse_launch_command(&args(&[])).unwrap(),
        LaunchCommand::Repl {
            strict: false,
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-session"])).unwrap(),
        LaunchCommand::Repl {
            strict: false,
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-strict"])).unwrap(),
        LaunchCommand::Repl {
            strict: true,
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-help"])).unwrap(),
        LaunchCommand::Help {
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-version"])).unwrap(),
        LaunchCommand::Version {
            language: OutputLanguage::English,
        }
    );
}

#[test]
fn parses_lang_flag() {
    assert_eq!(
        parse_launch_command(&args(&["-lang", "zh", "-e", "1 = 1"]))
            .unwrap()
            .output_language(),
        OutputLanguage::Chinese
    );
    assert_eq!(
        parse_launch_command(&args(&["-lang", "chinese", "-f", "a.lit"]))
            .unwrap()
            .output_language(),
        OutputLanguage::Chinese
    );
    assert_eq!(
        parse_launch_command(&args(&["-lang", "en", "-r", "repo"]))
            .unwrap()
            .output_language(),
        OutputLanguage::English
    );
    assert_eq!(
        parse_launch_command(&args(&["-lang", "english"]))
            .unwrap()
            .output_language(),
        OutputLanguage::English
    );
    assert_eq!(
        parse_launch_command(&args(&["-lang", "zh", "-help"])).unwrap(),
        LaunchCommand::Help {
            language: OutputLanguage::Chinese,
        }
    );
}

#[test]
fn rejects_unknown_shape_and_bad_lang() {
    assert!(parse_launch_command(&args(&["-e"])).is_err());
    assert!(parse_launch_command(&args(&["-e", ""])).is_err());
    assert!(parse_launch_command(&args(&["-e", "1 = 1", "-foo"])).is_err());
    assert!(parse_launch_command(&args(&["-e", "1 = 1", "2 = 2"])).is_err());
    assert!(parse_launch_command(&args(&["-foo", "-e", "1 = 1"])).is_err());
    assert!(parse_launch_command(&args(&["-strict", "-help"])).is_err());
    assert!(parse_launch_command(&args(&["-lang"])).is_err());
    assert!(parse_launch_command(&args(&["-lang", "de", "-e", "1 = 1"])).is_err());
}

#[test]
fn parses_extract_commands() {
    use crate::launch_command::{CodeExtractionTarget, ExtractInput};

    assert_eq!(
        parse_launch_command(&args(&["-extractpython", "have a R = 1"])).unwrap(),
        LaunchCommand::ExtractExecutableCode {
            target: CodeExtractionTarget::Python,
            input: ExtractInput::Code("have a R = 1".to_string()),
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-extractc", "-f", "main.lit"])).unwrap(),
        LaunchCommand::ExtractExecutableCode {
            target: CodeExtractionTarget::C,
            input: ExtractInput::File(PathBuf::from("main.lit")),
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-extractpython", "-r", "project"])).unwrap(),
        LaunchCommand::ExtractExecutableCode {
            target: CodeExtractionTarget::Python,
            input: ExtractInput::Repository(PathBuf::from("project")),
            language: OutputLanguage::English,
        }
    );
    assert!(parse_launch_command(&args(&["-session", "-extractpython", "have a R = 1"])).is_err());
}

#[test]
fn dash_leading_extraction_source_is_not_an_option() {
    use crate::launch_command::{CodeExtractionTarget, ExtractInput};
    for (flag, target) in [
        ("-extractpython", CodeExtractionTarget::Python),
        ("-extractc", CodeExtractionTarget::C),
    ] {
        for code in ["-2 < 0", "-strict", "--session", "-lang", "-unknown"] {
            for parts in [
                vec!["-lang", "zh", flag, code],
                vec![flag, code, "-lang", "zh"],
            ] {
                assert_eq!(
                    parse_launch_command(&args(&parts)).unwrap(),
                    LaunchCommand::ExtractExecutableCode {
                        target,
                        input: ExtractInput::Code(code.to_string()),
                        language: OutputLanguage::Chinese,
                    }
                );
            }
        }
        for parts in [
            vec![flag],
            vec![flag, ""],
            vec![flag, "-f"],
            vec![flag, "-r"],
            vec![flag, "-2 < 0", "extra"],
            vec!["-strict", flag, "-2 < 0"],
        ] {
            assert!(parse_launch_command(&args(&parts)).is_err(), "{parts:?}");
        }
    }
}

#[test]
fn file_and_repository_operands_can_spell_options() {
    use crate::launch_command::{CodeExtractionTarget, ExtractInput};
    for path in ["-chapter.lit", "-strict", "--session", "-lang", "-f", "-r"] {
        assert_eq!(
            parse_launch_command(&args(&["-f", path, "-strict"])).unwrap(),
            LaunchCommand::File {
                path: PathBuf::from(path),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            }
        );
        assert_eq!(
            parse_launch_command(&args(&["-r", path, "-session"])).unwrap(),
            LaunchCommand::Repository {
                path: PathBuf::from(path),
                session: true,
                strict: false,
                language: OutputLanguage::English,
            }
        );
        for (flag, target) in [
            ("-extractpython", CodeExtractionTarget::Python),
            ("-extractc", CodeExtractionTarget::C),
        ] {
            for (mode, input) in [
                ("-f", ExtractInput::File(PathBuf::from(path))),
                ("-r", ExtractInput::Repository(PathBuf::from(path))),
            ] {
                assert_eq!(
                    parse_launch_command(&args(&[flag, mode, path, "-lang", "zh"])).unwrap(),
                    LaunchCommand::ExtractExecutableCode {
                        target,
                        input,
                        language: OutputLanguage::Chinese,
                    }
                );
            }
        }
    }
    for mode in ["-f", "-r"] {
        assert!(parse_launch_command(&args(&[mode])).is_err());
        assert!(parse_launch_command(&args(&[mode, ""])).is_err());
    }
}

#[test]
fn parses_all_output_languages_and_preserves_source() {
    for language in OutputLanguage::ALL {
        let command =
            parse_launch_command(&args(&["-lang", language.as_str(), "-e", "1 + 2 = 3"])).unwrap();
        assert_eq!(command.output_language(), language);
        match command {
            LaunchCommand::Eval { code, .. } => assert_eq!(code, "1 + 2 = 3"),
            _ => panic!("expected eval"),
        }
        assert_eq!(
            OutputLanguage::parse_token(&format!("  {}  ", language.as_str().to_ascii_uppercase()))
                .unwrap(),
            language
        );
    }
    for (alias, language) in [
        ("english", OutputLanguage::English),
        ("chinese", OutputLanguage::Chinese),
        ("zh-hans", OutputLanguage::Chinese),
        ("french", OutputLanguage::French),
        ("russian", OutputLanguage::Russian),
        ("spanish", OutputLanguage::Spanish),
        ("arabic", OutputLanguage::Arabic),
        ("japanese", OutputLanguage::Japanese),
        ("korean", OutputLanguage::Korean),
        ("vietnamese", OutputLanguage::Vietnamese),
    ] {
        assert_eq!(OutputLanguage::parse_token(alias).unwrap(), language);
    }
    assert!(OutputLanguage::parse_token("zh-unknown").is_err());
    assert!(OutputLanguage::parse_token("").is_err());
}

#[test]
fn latex_is_a_separate_command_for_every_input_and_locale() {
    for language in OutputLanguage::ALL {
        for (flag, value, input) in [
            ("-e", "1 = 2", LatexInput::Code("1 = 2".into())),
            (
                "-f",
                "identity.lit",
                LatexInput::File("identity.lit".into()),
            ),
            ("-r", "project", LatexInput::Repository("project".into())),
        ] {
            for document in [false, true] {
                let mut parts = vec![flag, value, "-lang", language.as_str(), "--latex"];
                if document {
                    parts.push("--document");
                }
                let command = parse_launch_command(&args(&parts)).unwrap();
                assert_eq!(command.output_language(), language);
                assert!(!command.is_strict());
                assert_eq!(
                    command,
                    LaunchCommand::CompileToLatex {
                        input: input.clone(),
                        language,
                        document,
                    }
                );
            }
        }
    }
}

#[test]
fn latex_options_do_not_capture_source_or_path_operands() {
    use crate::launch_command::{CodeExtractionTarget, ExtractInput};
    for value in [
        "-latex",
        "--latex",
        "-document",
        "--document",
        "-strict",
        "-lang",
    ] {
        assert_eq!(
            parse_launch_command(&args(&["-e", value])).unwrap(),
            LaunchCommand::Eval {
                code: value.into(),
                session: false,
                strict: false,
                language: OutputLanguage::English,
            }
        );
        for (flag, input) in [
            ("-e", LatexInput::Code(value.into())),
            ("-f", LatexInput::File(value.into())),
            ("-r", LatexInput::Repository(value.into())),
        ] {
            assert_eq!(
                parse_launch_command(&args(&["-latex", flag, value])).unwrap(),
                LaunchCommand::CompileToLatex {
                    input,
                    language: OutputLanguage::English,
                    document: false
                }
            );
        }
        for (flag, target) in [
            ("-extractc", CodeExtractionTarget::C),
            ("-extractpython", CodeExtractionTarget::Python),
        ] {
            assert_eq!(
                parse_launch_command(&args(&[flag, value])).unwrap(),
                LaunchCommand::ExtractExecutableCode {
                    target,
                    input: ExtractInput::Code(value.into()),
                    language: OutputLanguage::English,
                }
            );
        }
    }
}

#[test]
fn latex_rejects_incompatible_modes_duplicates_and_missing_inputs() {
    for parts in [
        vec!["-latex"],
        vec!["-latex", "-e"],
        vec!["-latex", "-f", ""],
        vec!["-latex", "-r", ""],
        vec!["-latex", "-e", "1 = 1", "-session"],
        vec!["-latex", "-e", "1 = 1", "-strict"],
        vec!["-latex", "--latex", "-e", "1 = 1"],
        vec!["-latex", "-document", "--document", "-e", "1 = 1"],
        vec!["-latex", "-extractc", "1 = 1"],
        vec!["-extractpython", "1 = 1", "-latex"],
        vec!["-latex", "-e", "1 = 1", "-f", "identity.lit"],
        vec!["-latex", "-help"],
        vec!["-latex", "-version"],
        vec!["-document", "-e", "1 = 1"],
    ] {
        assert!(parse_launch_command(&args(&parts)).is_err(), "{parts:?}");
    }
}
