use crate::launch_command::{parse_launch_command, LaunchCommand, OutputLanguage};
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
        LaunchCommand::Extract {
            target: CodeExtractionTarget::Python,
            input: ExtractInput::Code("have a R = 1".to_string()),
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-extractc", "-f", "main.lit"])).unwrap(),
        LaunchCommand::Extract {
            target: CodeExtractionTarget::C,
            input: ExtractInput::File(PathBuf::from("main.lit")),
            language: OutputLanguage::English,
        }
    );
    assert_eq!(
        parse_launch_command(&args(&["-extractpython", "-r", "project"])).unwrap(),
        LaunchCommand::Extract {
            target: CodeExtractionTarget::Python,
            input: ExtractInput::Repository(PathBuf::from("project")),
            language: OutputLanguage::English,
        }
    );
    assert!(parse_launch_command(&args(&["-session", "-extractpython", "have a R = 1"])).is_err());
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
