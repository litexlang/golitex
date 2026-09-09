use crate::prelude::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ExtractionKind {
    /// Extract Python source.
    Python,

    /// Extract C source.
    C,
}

/// Verification and output settings shared by commands that execute Litex.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LitexExecutionOutputSettings {
    /// Policy controlling dependency verification.
    pub(super) verify_strictness: VerifyStrictnessPolicy,

    /// Detail level used for rendered output.
    pub(super) output_detail: OutputDetail,

    /// Language used for rendered output.
    pub(super) output_language: OutputLanguage,
}

impl LitexExecutionOutputSettings {
    pub(super) fn litex_execution_options(self) -> RuntimeOptions {
        RuntimeOptions::new(
            self.verify_strictness,
            self.output_detail,
            self.output_language,
            SummaryOption::None,
        )
    }
}

/// Options accepted by the interactive Litex REPL command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReplCommandOptions {
    /// Verification and output settings for REPL evaluations.
    pub(super) execution_output: LitexExecutionOutputSettings,
}

impl ReplCommandOptions {
    pub(super) fn litex_execution_options(self) -> RuntimeOptions {
        self.execution_output.litex_execution_options()
    }
}

/// Options accepted by a batch Litex execution command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ExecuteEvalFileRepoCommandOptions {
    /// Source entry point selected by `-e`, `-f`, or `-r`.
    pub(super) execution: LitexExecution,

    /// Verification and output settings for the selected source.
    pub(super) execution_output: LitexExecutionOutputSettings,
}

impl ExecuteEvalFileRepoCommandOptions {
    pub(super) fn litex_execution_options(self) -> RuntimeOptions {
        self.execution_output.litex_execution_options()
    }
}

/// Options accepted by a graph-producing Litex command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct GraphCommandOptions {
    /// Source entry point whose definitions or results are graphed.
    pub(super) execution: LitexExecution,

    /// Verification and output settings for the selected source.
    pub(super) execution_output: LitexExecutionOutputSettings,
}

impl GraphCommandOptions {
    pub(super) fn litex_execution_options(self) -> RuntimeOptions {
        self.execution_output.litex_execution_options()
    }
}

/// Options accepted by a persistent Litex session command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SessionCommandOptions {
    /// Session source mode, with or without configured project context.
    pub(super) execution: LitexExecution,

    /// Verification and output settings for the session.
    pub(super) execution_output: LitexExecutionOutputSettings,
}

impl SessionCommandOptions {
    pub(super) fn litex_execution_options(self) -> RuntimeOptions {
        self.execution_output.litex_execution_options()
    }
}

/// Options accepted by LaTeX and code-extraction conversion commands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConversionCommandOptions {
    /// Source entry point selected for conversion.
    pub(super) execution: LitexExecution,

    /// Language used for conversion diagnostics.
    pub(super) output_language: OutputLanguage,
}

#[derive(Debug)]
pub(super) enum CliCommand {
    /// Start the interactive REPL with its command-specific settings.
    Repl(ReplCommandOptions),

    /// Print the CLI help message.
    Help,

    /// Print the CLI version.
    Version,

    /// Execute one source target and render its run result.
    Execute {
        /// Source text, file path, or repository target.
        target: String,

        /// Options accepted by the execution command.
        options: ExecuteEvalFileRepoCommandOptions,
    },

    /// Execute one target and render its graph artifact.
    Graph {
        /// Graph flavor to render.
        kind: GraphKind,

        /// Source text, file path, or repository target.
        target: String,

        /// Optional path for the rendered graph JSON.
        save_path: Option<String>,

        /// Options accepted by the graph command.
        options: GraphCommandOptions,
    },

    /// Start a persistent session, optionally preloading a file.
    Session {
        /// Optional project or isolated file to preload.
        file_path: Option<String>,

        /// Options accepted by the session command.
        options: SessionCommandOptions,
    },

    /// Start the LaTeX conversion REPL.
    LatexRepl,

    /// Convert one source target to LaTeX.
    Latex {
        /// Source text, file path, or repository target.
        target: String,

        /// Options accepted by the conversion command.
        options: ConversionCommandOptions,
    },

    /// Extract another programming language from one Litex target.
    Extract {
        /// Requested extraction language.
        kind: ExtractionKind,

        /// Source text, file path, or repository target.
        target: String,

        /// Options accepted by the conversion command.
        options: ConversionCommandOptions,
    },

    /// Compile one Litex file to a Lean file.
    Lean {
        /// Litex input file path.
        input_path: String,

        /// Lean output file path.
        output_path: String,
    },
}

pub(super) fn parse_command_line_command(args: &[String]) -> Result<CliCommand, String> {
    let mut index = 0;
    let strict = if args.get(index).is_some_and(|arg| arg == "-strict") {
        index += 1;
        true
    } else {
        false
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
        strict,
        output_language,
        isolated,
    };
    let is_value = |index: usize| {
        command
            .get(index)
            .is_some_and(|value| !value.starts_with('-'))
    };
    let no_modifiers =
        !modifiers.strict && modifiers.output_language.is_none() && !modifiers.isolated;

    if command.is_empty() {
        if modifiers.isolated {
            return unsupported();
        }
        return Ok(CliCommand::Repl(repl_command_options(modifiers)));
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
            options: execute_command_options(LitexExecution::Eval, modifiers),
        });
    }

    if command.len() == 2 && command[0] == "-f" && is_value(1) {
        let execution = if modifiers.isolated {
            LitexExecution::IsolatedFile
        } else {
            LitexExecution::File
        };
        return Ok(CliCommand::Execute {
            target: command[1].clone(),
            options: execute_command_options(execution, modifiers),
        });
    }

    if command.len() == 2 && command[0] == "-r" && is_value(1) {
        if modifiers.isolated {
            return unsupported();
        }
        return Ok(CliCommand::Execute {
            target: command[1].clone(),
            options: execute_command_options(LitexExecution::Repository, modifiers),
        });
    }

    if command.len() == 4
        && command[0] == "-f"
        && is_value(1)
        && command[2] == "-lean"
        && is_value(3)
    {
        if modifiers.strict || modifiers.output_language.is_some() || !modifiers.isolated {
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
        if modifiers.isolated && command[1] != "-f" {
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
            options: graph_command_options(execution, modifiers),
        });
    }

    if (command.len() == 1 && command[0] == "-session")
        || (command.len() == 3 && command[0] == "-session" && command[1] == "-f" && is_value(2))
    {
        let execution = if modifiers.isolated {
            LitexExecution::IsolatedSession
        } else {
            LitexExecution::Session
        };
        return Ok(CliCommand::Session {
            file_path: command.get(2).cloned(),
            options: session_command_options(execution, modifiers),
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
        if modifiers.strict || (modifiers.isolated && command[1] != "-f") {
            return unsupported();
        }
        let execution = execution_option(command[1].as_str(), modifiers.isolated);
        return Ok(CliCommand::Latex {
            target: command[2].clone(),
            options: conversion_command_options(execution, modifiers),
        });
    }

    if command.len() == 2
        && matches!(command[0].as_str(), "-extractpython" | "-extractc")
        && is_value(1)
    {
        if modifiers.strict || modifiers.isolated {
            return unsupported();
        }
        return Ok(CliCommand::Extract {
            kind: extraction_kind(command[0].as_str()),
            target: command[1].clone(),
            options: conversion_command_options(LitexExecution::Eval, modifiers),
        });
    }

    if command.len() == 3
        && matches!(command[0].as_str(), "-extractpython" | "-extractc")
        && matches!(command[1].as_str(), "-f" | "-r")
        && is_value(2)
    {
        if modifiers.strict || (modifiers.isolated && command[1] != "-f") {
            return unsupported();
        }
        let execution = execution_option(command[1].as_str(), modifiers.isolated);
        return Ok(CliCommand::Extract {
            kind: extraction_kind(command[0].as_str()),
            target: command[2].clone(),
            options: conversion_command_options(execution, modifiers),
        });
    }

    unsupported()
}

#[derive(Clone, Copy)]
struct ParsedModifiers {
    /// Whether dependency verification is required.
    strict: bool,

    /// Optional language for user-facing output.
    output_language: Option<OutputLanguage>,

    /// Whether filesystem execution must avoid project context.
    isolated: bool,
}

fn strictness(modifiers: ParsedModifiers) -> VerifyStrictnessPolicy {
    if modifiers.strict {
        VerifyStrictnessPolicy::Strict
    } else {
        VerifyStrictnessPolicy::Ordinary
    }
}

fn repl_command_options(modifiers: ParsedModifiers) -> ReplCommandOptions {
    ReplCommandOptions {
        execution_output: litex_execution_output_settings(modifiers),
    }
}

fn execute_command_options(
    execution: LitexExecution,
    modifiers: ParsedModifiers,
) -> ExecuteEvalFileRepoCommandOptions {
    ExecuteEvalFileRepoCommandOptions {
        execution,
        execution_output: litex_execution_output_settings(modifiers),
    }
}

fn graph_command_options(
    execution: LitexExecution,
    modifiers: ParsedModifiers,
) -> GraphCommandOptions {
    GraphCommandOptions {
        execution,
        execution_output: litex_execution_output_settings(modifiers),
    }
}

fn session_command_options(
    execution: LitexExecution,
    modifiers: ParsedModifiers,
) -> SessionCommandOptions {
    SessionCommandOptions {
        execution,
        execution_output: litex_execution_output_settings(modifiers),
    }
}

fn conversion_command_options(
    execution: LitexExecution,
    modifiers: ParsedModifiers,
) -> ConversionCommandOptions {
    ConversionCommandOptions {
        execution,
        output_language: modifiers.output_language.unwrap_or(OutputLanguage::English),
    }
}

fn litex_execution_output_settings(modifiers: ParsedModifiers) -> LitexExecutionOutputSettings {
    LitexExecutionOutputSettings {
        verify_strictness: strictness(modifiers),
        output_detail: OutputDetail::Detailed,
        output_language: modifiers.output_language.unwrap_or(OutputLanguage::English),
    }
}

fn execution_option(flag: &str, isolated: bool) -> LitexExecution {
    match flag {
        "-e" => LitexExecution::Eval,
        "-f" if isolated => LitexExecution::IsolatedFile,
        "-f" => LitexExecution::File,
        "-r" => LitexExecution::Repository,
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
