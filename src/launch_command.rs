use crate::runtime::{RuntimeError, RuntimeResult};
use std::path::PathBuf;

/// Natural language for user-facing JSON / status text. Litex source is unchanged.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OutputLanguage {
    #[default]
    English,
    Chinese,
}

impl OutputLanguage {
    pub fn as_str(self) -> &'static str {
        match self {
            OutputLanguage::English => "en",
            OutputLanguage::Chinese => "zh",
        }
    }

    pub fn parse_token(token: &str) -> RuntimeResult<Self> {
        match token.trim().to_ascii_lowercase().as_str() {
            "en" | "english" => Ok(OutputLanguage::English),
            "zh" | "chinese" => Ok(OutputLanguage::Chinese),
            _ => Err(RuntimeError::InvalidArguments(format!(
                "`-lang` expects en|english|zh|chinese, got `{token}`"
            ))),
        }
    }
}

/// Target language for `-extractpython` / `-extractc`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodeExtractionTarget {
    Python,
    C,
}

impl CodeExtractionTarget {
    pub fn format_name(self) -> &'static str {
        match self {
            Self::Python => "python",
            Self::C => "c",
        }
    }
}

/// Input shape for `-extractpython` / `-extractc`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExtractInput {
    Code(String),
    File(PathBuf),
    Repository(PathBuf),
}

/// How a Runtime session was launched. Shared by `run` and `runtime` (no cycle).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LaunchCommand {
    Help {
        language: OutputLanguage,
    },
    Version {
        language: OutputLanguage,
    },
    Repl {
        strict: bool,
        language: OutputLanguage,
    },
    Eval {
        code: String,
        session: bool,
        strict: bool,
        language: OutputLanguage,
    },
    File {
        path: PathBuf,
        session: bool,
        strict: bool,
        language: OutputLanguage,
    },
    Repository {
        path: PathBuf,
        session: bool,
        strict: bool,
        language: OutputLanguage,
    },
    Extract {
        target: CodeExtractionTarget,
        input: ExtractInput,
        language: OutputLanguage,
    },
}

impl LaunchCommand {
    pub fn is_strict(&self) -> bool {
        match self {
            LaunchCommand::Repl { strict, .. }
            | LaunchCommand::Eval { strict, .. }
            | LaunchCommand::File { strict, .. }
            | LaunchCommand::Repository { strict, .. } => *strict,
            LaunchCommand::Help { .. }
            | LaunchCommand::Version { .. }
            | LaunchCommand::Extract { .. } => false,
        }
    }

    pub fn output_language(&self) -> OutputLanguage {
        match self {
            LaunchCommand::Help { language }
            | LaunchCommand::Version { language }
            | LaunchCommand::Repl { language, .. }
            | LaunchCommand::Eval { language, .. }
            | LaunchCommand::File { language, .. }
            | LaunchCommand::Repository { language, .. }
            | LaunchCommand::Extract { language, .. } => *language,
        }
    }
}

pub fn parse_launch_command(args: &[String]) -> RuntimeResult<LaunchCommand> {
    let mut session = false;
    let mut strict = false;
    let mut language = OutputLanguage::English;
    let mut rest = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        if arg == "-e" {
            rest.push(arg.clone());
            i += 1;
            // The next argv item is source, even when it spells a shared flag.
            if let Some(code) = args.get(i) {
                rest.push(code.clone());
                i += 1;
            }
        } else if arg == "-session" || arg == "--session" {
            session = true;
            i += 1;
        } else if arg == "-strict" || arg == "--strict" {
            strict = true;
            i += 1;
        } else if arg == "-lang" || arg == "--lang" {
            i += 1;
            let Some(token) = args.get(i) else {
                return Err(RuntimeError::InvalidArguments(
                    "`-lang` requires a value: en|english|zh|chinese".to_string(),
                ));
            };
            language = OutputLanguage::parse_token(token)?;
            i += 1;
        } else {
            rest.push(arg.clone());
            i += 1;
        }
    }

    match rest.as_slice() {
        [] => Ok(LaunchCommand::Repl { strict, language }),
        [flag] if flag == "-help" || flag == "--help" || flag == "-h" => {
            if session || strict {
                return Err(RuntimeError::InvalidArguments(
                    "`-help` does not take `-session` or `-strict`".to_string(),
                ));
            }
            Ok(LaunchCommand::Help { language })
        }
        [flag] if flag == "-version" || flag == "--version" => {
            if session || strict {
                return Err(RuntimeError::InvalidArguments(
                    "`-version` does not take `-session` or `-strict`".to_string(),
                ));
            }
            Ok(LaunchCommand::Version { language })
        }
        [flag, value] if flag == "-e" && !value.is_empty() => Ok(LaunchCommand::Eval {
            code: value.clone(),
            session,
            strict,
            language,
        }),
        [flag, value] if flag == "-f" && is_value(value) => Ok(LaunchCommand::File {
            path: PathBuf::from(value),
            session,
            strict,
            language,
        }),
        [flag, value] if flag == "-r" && is_value(value) => Ok(LaunchCommand::Repository {
            path: PathBuf::from(value),
            session,
            strict,
            language,
        }),
        [flag, value]
            if (flag == "-extractpython" || flag == "-extractc") && is_value(value) =>
        {
            reject_session_strict_for_extract(session, strict)?;
            Ok(LaunchCommand::Extract {
                target: extraction_target(flag),
                input: ExtractInput::Code(value.clone()),
                language,
            })
        }
        [flag, mode, value]
            if (flag == "-extractpython" || flag == "-extractc")
                && mode == "-f"
                && is_value(value) =>
        {
            reject_session_strict_for_extract(session, strict)?;
            Ok(LaunchCommand::Extract {
                target: extraction_target(flag),
                input: ExtractInput::File(PathBuf::from(value)),
                language,
            })
        }
        [flag, mode, value]
            if (flag == "-extractpython" || flag == "-extractc")
                && mode == "-r"
                && is_value(value) =>
        {
            reject_session_strict_for_extract(session, strict)?;
            Ok(LaunchCommand::Extract {
                target: extraction_target(flag),
                input: ExtractInput::Repository(PathBuf::from(value)),
                language,
            })
        }
        _ => Err(RuntimeError::InvalidArguments(
            "supports bare REPL, `-e <code>`, `-f <file>`, `-r <repository>`, `-extractpython` / `-extractc` with code / `-f` / `-r`, optional `-session` / `-strict` / `-lang <en|zh>`, `-help`, `-version`"
                .to_string(),
        )),
    }
}

fn extraction_target(flag: &str) -> CodeExtractionTarget {
    if flag == "-extractc" {
        CodeExtractionTarget::C
    } else {
        CodeExtractionTarget::Python
    }
}

fn reject_session_strict_for_extract(session: bool, strict: bool) -> RuntimeResult<()> {
    if session || strict {
        return Err(RuntimeError::InvalidArguments(
            "`-extractpython` / `-extractc` do not take `-session` or `-strict`".to_string(),
        ));
    }
    Ok(())
}

fn is_value(token: &str) -> bool {
    !token.is_empty() && !token.starts_with('-')
}
