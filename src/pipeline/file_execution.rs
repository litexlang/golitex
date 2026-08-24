use super::{
    execute_repository_target, execute_source_with_options, RepositoryExecutionOptions,
    SourceRunOptions,
};
use crate::common::helper::remove_windows_carriage_return;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::module_manager::{discover_repository_for_file, RepositoryFileTarget};
use crate::parse::Tokenizer;
use crate::result::StmtResult;
use crate::runtime::{ExecutionLayer, Runtime, TrustedPrefixPolicy, TrustedPrefixReport};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Resolve a source-file target against the process working directory.
pub fn resolve_source_file_path(file_path: &str) -> Result<String, String> {
    let path = remove_windows_carriage_return(file_path);
    let absolute_path = if Path::new(path.as_str()).is_absolute() {
        PathBuf::from(path.as_str())
    } else {
        let working_directory = env::current_dir()
            .map_err(|error| format!("failed to get current working directory: {}", error))?;
        working_directory.join(path.as_str())
    };

    if absolute_path.parent().is_none() {
        return Err("could not get parent directory of file path".to_string());
    }

    absolute_path
        .to_str()
        .map(str::to_string)
        .ok_or_else(|| "file path is not valid UTF-8".to_string())
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FileExecutionOptions {
    pub force_isolated: bool,
    pub trust_before_line: Option<usize>,
}

pub fn execute_file_in_runtime(
    entry_file_path: &str,
    runtime: &mut Runtime,
    options: FileExecutionOptions,
) -> (
    Vec<StmtResult>,
    Option<RuntimeError>,
    Option<TrustedPrefixReport>,
    bool,
) {
    let FileExecutionOptions {
        force_isolated,
        trust_before_line,
    } = options;
    let path = Path::new(entry_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                entry_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
            None,
            false,
        );
    }
    let mut trusted_prefix_report = None;
    if let Some(before_line) = trust_before_line {
        let source_code = match fs::read_to_string(entry_file_path) {
            Ok(content) => content,
            Err(error) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        format!("could not read file: {}", error).as_str(),
                    )),
                    None,
                    false,
                )
            }
        };
        let source_code = remove_windows_carriage_return(source_code.as_str());
        let blocks =
            match Tokenizer::new().parse_blocks(source_code.as_str(), Rc::from(entry_file_path)) {
                Ok(blocks) => blocks,
                Err(error) => return (vec![], Some(error), None, false),
            };
        let statement_lines = blocks
            .iter()
            .map(|block| block.line_file.0)
            .collect::<Vec<_>>();
        if !statement_lines.contains(&before_line) {
            let message = super::source_execution::trusted_prefix_boundary_error_message(
                entry_file_path,
                before_line,
                &statement_lines,
            );
            return (
                vec![],
                Some(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        message,
                        (before_line, Rc::from(entry_file_path)),
                    ))
                    .into(),
                ),
                None,
                true,
            );
        }
        let trusted_top_level_statements = statement_lines
            .iter()
            .filter(|line| **line < before_line)
            .count();
        trusted_prefix_report = Some(TrustedPrefixReport::new(
            entry_file_path.to_string(),
            before_line,
            trusted_top_level_statements,
            before_line,
        ));
    }
    if !force_isolated {
        match discover_repository_for_file(runtime, entry_file_path) {
            Ok(Some(target)) => {
                let (stmt_results, runtime_error) = if let Some(before_line) = trust_before_line {
                    let (module_id, layer) = match target {
                        RepositoryFileTarget::Module(module_id) => {
                            (module_id, ExecutionLayer::Main)
                        }
                        RepositoryFileTarget::File { module_id, file_id } => {
                            (module_id, ExecutionLayer::File(file_id))
                        }
                    };
                    let policy = TrustedPrefixPolicy::new(module_id, layer, before_line);
                    execute_repository_target(
                        runtime,
                        target,
                        RepositoryExecutionOptions {
                            trusted_prefix: Some(policy),
                        },
                    )
                } else {
                    execute_repository_target(
                        runtime,
                        target,
                        RepositoryExecutionOptions::default(),
                    )
                };
                return (stmt_results, runtime_error, trusted_prefix_report, false);
            }
            Ok(None) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        "litex -f requires a litex.config in the same folder; use `litex -isolated -f <file>` for an isolated file",
                    )),
                    trusted_prefix_report,
                    false,
                )
            }
            Err(error) => return (vec![], Some(error), trusted_prefix_report, false),
        }
    }

    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(error) => {
            return (
                vec![],
                Some(file_target_error(
                    entry_file_path,
                    format!("could not read file: {}", error).as_str(),
                )),
                trusted_prefix_report,
                false,
            )
        }
    };
    runtime.start_isolated_source(entry_file_path);
    runtime.set_current_source_allows_inline_imports(true);
    let outcome = execute_source_with_options(
        remove_windows_carriage_return(source_code.as_str()).as_str(),
        runtime,
        SourceRunOptions {
            trust_before_line,
            ..SourceRunOptions::default()
        },
    );
    (
        outcome.stmt_results,
        outcome.runtime_error,
        trusted_prefix_report,
        false,
    )
}

fn file_target_error(entry_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(entry_file_path)),
    ))
    .into()
}
