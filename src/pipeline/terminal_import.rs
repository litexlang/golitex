use super::render_runtime_error_json;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::module_system::{discover_terminal_module_import, discover_terminal_std_import};
use crate::module_system::{ImportTarget, ModuleStatus, UnverifiedImportKind};
use crate::output::json_value::{render_json_value, JsonValue};
use crate::parsing::Tokenizer;
use crate::runtime::{TrustedOrRequireVerify, Runtime};
use crate::syntax::keywords::{AS, DOUBLE_QUOTE, IMPORT, STD};
use crate::syntax::name_validation::is_valid_litex_name;
use crate::syntax::source_conventions::{default_line_file, LineFile};
use std::fmt;

#[derive(Clone)]
enum TerminalImportCommand {
    Module {
        path: String,
        alias: String,
        line_file: LineFile,
    },
    Std {
        name: String,
        line_file: LineFile,
    },
}

impl TerminalImportCommand {
    fn line_file(&self) -> LineFile {
        match self {
            Self::Module { line_file, .. } | Self::Std { line_file, .. } => line_file.clone(),
        }
    }

    fn diagnostic_kind(&self) -> UnverifiedImportKind {
        match self {
            Self::Module { .. } => UnverifiedImportKind::TerminalImport,
            Self::Std { .. } => UnverifiedImportKind::TerminalStdImport,
        }
    }
}

impl fmt::Display for TerminalImportCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module { path, alias, .. } => {
                write!(f, "{} \"{}\" {} {}", IMPORT, path, AS, alias)
            }
            Self::Std { name, .. } => write!(f, "{} {} {}", IMPORT, STD, name),
        }
    }
}

pub(super) fn terminal_input_starts_with_import(source: &str) -> bool {
    source.split_ascii_whitespace().next() == Some(IMPORT)
}

pub(super) fn run_terminal_import(source: &str, runtime: &mut Runtime) -> (bool, String) {
    let command = match parse_terminal_import(source, runtime.current_file_path_rc()) {
        Ok(command) => command,
        Err(error) => return (false, render_runtime_error_json(runtime, &error, false)),
    };

    let module_manager_before = runtime.module_manager.clone();
    let discovery = match &command {
        TerminalImportCommand::Module {
            path,
            alias,
            line_file,
        } => discover_terminal_module_import(
            runtime,
            path.as_str(),
            alias.as_str(),
            line_file.clone(),
        ),
        TerminalImportCommand::Std { name, line_file } => {
            discover_terminal_std_import(runtime, name.as_str(), line_file.clone())
        }
    };
    let module_id = match discovery {
        Ok(module_id) => module_id,
        Err(error) => {
            runtime.module_manager = module_manager_before;
            return (false, render_runtime_error_json(runtime, &error, false));
        }
    };
    let module_status_before = runtime
        .module_manager
        .module(module_id)
        .expect("terminal import module should be registered")
        .status;
    let execution_mode = if runtime.execution_options.is_strict() {
        TrustedOrRequireVerify::RequireVerification
    } else {
        let name = runtime
            .module_manager
            .canonical_name_for_target(ImportTarget::Module(module_id))
            .unwrap_or("terminal import")
            .to_string();
        runtime.record_unverified_import(command.diagnostic_kind(), name, command.line_file());
        TrustedOrRequireVerify::Trusted
    };
    let (_, runtime_error) = super::repository_execution::run_repository_module_target_with_mode(
        runtime,
        module_id,
        execution_mode,
    );
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before;
        return (false, render_runtime_error_json(runtime, &error, false));
    }

    let target = runtime
        .module_manager
        .canonical_name_for_target(ImportTarget::Module(module_id))
        .unwrap_or("terminal import")
        .to_string();
    let result = render_json_value(
        &JsonValue::Object(vec![
            (
                "result".to_string(),
                JsonValue::JsonString("success".to_string()),
            ),
            (
                "type".to_string(),
                JsonValue::JsonString("terminal import".to_string()),
            ),
            (
                "command".to_string(),
                JsonValue::JsonString(command.to_string()),
            ),
            ("target".to_string(), JsonValue::JsonString(target)),
            (
                "execution".to_string(),
                JsonValue::JsonString(
                    if module_status_before == ModuleStatus::Loaded {
                        "reused"
                    } else {
                        "executed"
                    }
                    .to_string(),
                ),
            ),
            (
                "execution_mode".to_string(),
                JsonValue::JsonString(
                    match execution_mode {
                        TrustedOrRequireVerify::RequireVerification => "verified",
                        TrustedOrRequireVerify::Trusted => "trusted",
                    }
                    .to_string(),
                ),
            ),
        ]),
        0,
    );
    (true, result)
}

fn parse_terminal_import(
    source: &str,
    source_path: std::rc::Rc<str>,
) -> Result<TerminalImportCommand, RuntimeError> {
    let mut blocks = Tokenizer::new().parse_blocks(source, source_path)?;
    if blocks.len() != 1 {
        return Err(terminal_import_error(
            default_line_file(),
            "terminal import expects exactly one command",
        ));
    }
    let mut block = blocks
        .pop()
        .expect("one terminal import block should exist");
    block.skip_token(IMPORT)?;
    if block.current_token_is_equal_to(STD) {
        block.skip_token(STD)?;
        let name = block.advance()?;
        if !block.exceed_end_of_head() {
            return Err(terminal_import_error(
                block.line_file.clone(),
                "import std: expected one standard package name",
            ));
        }
        is_valid_litex_name(name.as_str())
            .map_err(|message| terminal_import_error(block.line_file.clone(), message.as_str()))?;
        return Ok(TerminalImportCommand::Std {
            name,
            line_file: block.line_file.clone(),
        });
    }

    block.skip_token(DOUBLE_QUOTE)?;
    let mut path_parts = vec![];
    while !block.exceed_end_of_head() && !block.current_token_is_equal_to(DOUBLE_QUOTE) {
        path_parts.push(block.advance()?);
    }
    if path_parts.is_empty() {
        return Err(terminal_import_error(
            block.line_file.clone(),
            "import: module path cannot be empty",
        ));
    }
    block.skip_token(DOUBLE_QUOTE)?;
    block.skip_token(AS)?;
    let alias = block.advance()?;
    is_valid_litex_name(alias.as_str())
        .map_err(|message| terminal_import_error(block.line_file.clone(), message.as_str()))?;
    if !block.exceed_end_of_head() {
        return Err(terminal_import_error(
            block.line_file.clone(),
            "import: expected a quoted path followed by as and an alias",
        ));
    }
    Ok(TerminalImportCommand::Module {
        path: path_parts.join(""),
        alias,
        line_file: block.line_file.clone(),
    })
}

fn terminal_import_error(line_file: LineFile, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        line_file,
    ))
    .into()
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/terminal_import/tests.rs"]
mod tests;
