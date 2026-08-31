use crate::prelude::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ExtractionKind {
    Python,
    C,
}

#[derive(Debug)]
pub(super) enum CliCommand {
    Repl(RunOptions),
    Help,
    Version,
    Execute {
        target: String,
        options: RunOptions,
    },
    Graph {
        kind: GraphKind,
        target: String,
        save_path: Option<String>,
        options: RunOptions,
    },
    Session {
        file_path: Option<String>,
        options: RunOptions,
    },
    LatexRepl,
    Latex {
        target: String,
        options: RunOptions,
    },
    Extract {
        kind: ExtractionKind,
        target: String,
        options: RunOptions,
    },
    Lean {
        input_path: String,
        output_path: String,
    },
}

pub(super) fn parse_cli_command(args: &[String]) -> Result<CliCommand, String> {
    let mut index = 0;
    let output_style = match args.get(index).map(String::as_str) {
        Some("-compact") => {
            index += 1;
            Some(OutputStyle::Compact)
        }
        Some("-detail") => {
            index += 1;
            Some(OutputStyle::Detailed)
        }
        _ => None,
    };
    let strict = if args.get(index).is_some_and(|arg| arg == "-strict") {
        index += 1;
        true
    } else {
        false
    };
    let summary = if args.get(index).is_some_and(|arg| arg == "-summarize") {
        index += 1;
        SummaryOption::Summarize
    } else {
        SummaryOption::None
    };
    let output_language = if args.get(index).is_some_and(|arg| arg == "-lang") {
        let Some(language) = args.get(index + 1) else {
            return Err(format!(
                "-lang requires a value: {}",
                OutputLanguage::supported_codes_text()
            ));
        };
        index += 2;
        Some(OutputLanguage::from_cli_lang(language)?)
    } else {
        None
    };
    let isolated = if args.get(index).is_some_and(|arg| arg == "-isolated") {
        index += 1;
        true
    } else {
        false
    };

    let command = &args[index..];
    let modifiers = ParsedModifiers {
        output_style,
        strict,
        summary,
        output_language,
        isolated,
    };
    let is_value = |index: usize| {
        command
            .get(index)
            .is_some_and(|value| !value.starts_with('-'))
    };
    let summary_was_set = modifiers.summary == SummaryOption::Summarize;
    let no_modifiers = modifiers.output_style.is_none()
        && !modifiers.strict
        && !summary_was_set
        && modifiers.output_language.is_none()
        && !modifiers.isolated;

    if command.is_empty() {
        if modifiers.isolated || summary_was_set {
            return unsupported();
        }
        return Ok(CliCommand::Repl(run_options(
            ExecutionOption::Repl,
            modifiers,
        )));
    }

    if command.len() == 1 && command[0] == "-help" {
        if !no_modifiers {
            return unsupported();
        }
        return Ok(CliCommand::Help);
    }

    if command.len() == 1 && command[0] == "-version" {
        if !no_modifiers {
            return unsupported();
        }
        return Ok(CliCommand::Version);
    }

    if command.len() == 2 && command[0] == "-e" && is_value(1) {
        if modifiers.isolated {
            return unsupported();
        }
        return Ok(CliCommand::Execute {
            target: command[1].clone(),
            options: run_options(ExecutionOption::Eval, modifiers),
        });
    }

    if command.len() == 2 && command[0] == "-f" && is_value(1) {
        let execution = if modifiers.isolated {
            ExecutionOption::IsolatedFile
        } else {
            ExecutionOption::File
        };
        return Ok(CliCommand::Execute {
            target: command[1].clone(),
            options: run_options(execution, modifiers),
        });
    }

    if command.len() == 2 && command[0] == "-r" && is_value(1) {
        if modifiers.isolated {
            return unsupported();
        }
        return Ok(CliCommand::Execute {
            target: command[1].clone(),
            options: run_options(ExecutionOption::Repo, modifiers),
        });
    }

    if command.len() == 4
        && command[0] == "-f"
        && is_value(1)
        && command[2] == "-lean"
        && is_value(3)
    {
        if modifiers.output_style.is_some()
            || modifiers.strict
            || summary_was_set
            || modifiers.output_language.is_some()
            || !modifiers.isolated
        {
            return unsupported();
        }
        return Ok(CliCommand::Lean {
            input_path: command[1].clone(),
            output_path: command[3].clone(),
        });
    }

    if matches!(
        command.first().map(String::as_str),
        Some("-graph" | "-factgraph" | "-defgraph")
    ) && matches!(command.len(), 3 | 4)
        && matches!(command[1].as_str(), "-e" | "-f" | "-r")
        && is_value(2)
        && (command.len() == 3 || is_value(3))
    {
        if summary_was_set || (modifiers.isolated && command[1] != "-f") {
            return unsupported();
        }
        let execution = execution_option(command[1].as_str(), modifiers.isolated);
        let kind = match command[0].as_str() {
            "-graph" => GraphKind::Result,
            "-factgraph" => GraphKind::Fact,
            "-defgraph" => GraphKind::Definition,
            _ => unreachable!("graph command was already validated"),
        };
        return Ok(CliCommand::Graph {
            kind,
            target: command[2].clone(),
            save_path: command.get(3).cloned(),
            options: run_options(execution, modifiers),
        });
    }

    if (command.len() == 1 && command[0] == "-session")
        || (command.len() == 3 && command[0] == "-session" && command[1] == "-f" && is_value(2))
    {
        if summary_was_set {
            return unsupported();
        }
        let execution = if modifiers.isolated {
            ExecutionOption::IsolatedSession
        } else {
            ExecutionOption::Session
        };
        return Ok(CliCommand::Session {
            file_path: command.get(2).cloned(),
            options: run_options(execution, modifiers),
        });
    }

    if command.len() == 1 && command[0] == "-latex" {
        if !no_modifiers {
            return unsupported();
        }
        return Ok(CliCommand::LatexRepl);
    }

    if command.len() == 3
        && command[0] == "-latex"
        && matches!(command[1].as_str(), "-e" | "-f" | "-r")
        && is_value(2)
    {
        if modifiers.output_style.is_some()
            || modifiers.strict
            || summary_was_set
            || (modifiers.isolated && command[1] != "-f")
        {
            return unsupported();
        }
        let execution = execution_option(command[1].as_str(), modifiers.isolated);
        return Ok(CliCommand::Latex {
            target: command[2].clone(),
            options: run_options(execution, modifiers),
        });
    }

    if command.len() == 2
        && matches!(command[0].as_str(), "-extractpython" | "-extractc")
        && is_value(1)
    {
        if modifiers.output_style.is_some()
            || modifiers.strict
            || summary_was_set
            || modifiers.isolated
        {
            return unsupported();
        }
        return Ok(CliCommand::Extract {
            kind: extraction_kind(command[0].as_str()),
            target: command[1].clone(),
            options: run_options(ExecutionOption::Eval, modifiers),
        });
    }

    if command.len() == 3
        && matches!(command[0].as_str(), "-extractpython" | "-extractc")
        && matches!(command[1].as_str(), "-f" | "-r")
        && is_value(2)
    {
        if modifiers.output_style.is_some()
            || modifiers.strict
            || summary_was_set
            || (modifiers.isolated && command[1] != "-f")
        {
            return unsupported();
        }
        let execution = execution_option(command[1].as_str(), modifiers.isolated);
        return Ok(CliCommand::Extract {
            kind: extraction_kind(command[0].as_str()),
            target: command[2].clone(),
            options: run_options(execution, modifiers),
        });
    }

    unsupported()
}

#[derive(Clone, Copy)]
struct ParsedModifiers {
    output_style: Option<OutputStyle>,
    strict: bool,
    summary: SummaryOption,
    output_language: Option<OutputLanguage>,
    isolated: bool,
}

fn run_options(execution: ExecutionOption, modifiers: ParsedModifiers) -> RunOptions {
    let options = if modifiers.strict {
        RunOptions::strict_execute(execution)
    } else {
        RunOptions::execute(execution)
    };
    options
        .with_output_style(modifiers.output_style.unwrap_or(OutputStyle::Normal))
        .with_output_language(modifiers.output_language.unwrap_or(OutputLanguage::English))
        .with_summary(modifiers.summary)
}

fn execution_option(flag: &str, isolated: bool) -> ExecutionOption {
    match flag {
        "-e" => ExecutionOption::Eval,
        "-f" if isolated => ExecutionOption::IsolatedFile,
        "-f" => ExecutionOption::File,
        "-r" => ExecutionOption::Repo,
        _ => unreachable!("command input flag was already validated"),
    }
}

fn extraction_kind(flag: &str) -> ExtractionKind {
    match flag {
        "-extractpython" => ExtractionKind::Python,
        "-extractc" => ExtractionKind::C,
        _ => unreachable!("extraction command was already validated"),
    }
}

fn unsupported<T>() -> Result<T, String> {
    Err("unsupported CLI command combination".to_string())
}
