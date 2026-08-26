use super::{execute_repository_target, SourceImportPolicy};
use crate::common::helper::remove_windows_carriage_from_str;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::module_manager::discover_repository_for_file;
use crate::result::StmtResult;
use crate::runtime::Runtime;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Resolve a source-file target against the process working directory.
pub fn resolve_source_file_path(file_path: &str) -> Result<String, String> {
    let path = remove_windows_carriage_from_str(file_path);
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
}

pub fn execute_file_in_runtime(
    entry_file_path: &str,
    runtime: &mut Runtime,
    options: FileExecutionOptions,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let FileExecutionOptions { force_isolated } = options;
    let path = Path::new(entry_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                entry_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
        );
    }
    if !force_isolated {
        match discover_repository_for_file(runtime, entry_file_path) {
            Ok(Some(target)) => {
                return execute_repository_target(runtime, target);
            }
            Ok(None) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        "litex -f requires a litex.config in the same folder; use `litex -isolated -f <file>` for an isolated file",
                    )),
                )
            }
            Err(error) => return (vec![], Some(error)),
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
            )
        }
    };
    runtime.start_isolated_source(entry_file_path);
    runtime.set_current_source_allows_inline_imports(true);
    let outcome = runtime.execute_source(
        remove_windows_carriage_from_str(source_code.as_str()).as_str(),
        SourceImportPolicy::UseRuntimePolicy,
    );
    (outcome.stmt_results, outcome.runtime_error)
}

fn file_target_error(entry_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(entry_file_path)),
    ))
    .into()
}
