use super::execute_repository_target;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::module_system::discover_repository_for_file;
use crate::result::StmtResult;
use crate::runtime::{ExecutionOption, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;
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

pub fn file_execution_option(file_path: &str) -> ExecutionOption {
    let path = fs::canonicalize(file_path).unwrap_or_else(|_| PathBuf::from(file_path));
    let has_direct_project_config = path
        .parent()
        .is_some_and(|parent| parent.join("litex.config").is_file());
    if has_direct_project_config {
        ExecutionOption::File
    } else {
        ExecutionOption::IsolatedFile
    }
}

pub fn execute_file_in_runtime(
    target_file_path: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let path = Path::new(target_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                target_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
        );
    }
    match discover_repository_for_file(runtime, target_file_path) {
        Ok(Some(target)) => execute_repository_target(runtime, target),
        Ok(None) => (
            vec![],
            Some(file_target_error(
                target_file_path,
                "project file execution requires a litex.config in the same folder",
            )),
        ),
        Err(error) => (vec![], Some(error)),
    }
}

pub fn execute_isolated_file_in_runtime(
    target_file_path: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let path = Path::new(target_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                target_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
        );
    }

    let source_code = match fs::read_to_string(target_file_path) {
        Ok(content) => content,
        Err(error) => {
            return (
                vec![],
                Some(file_target_error(
                    target_file_path,
                    format!("could not read file: {}", error).as_str(),
                )),
            )
        }
    };

    runtime.start_real_file(target_file_path);
    let outcome =
        runtime.execute_source(remove_windows_carriage_from_str(source_code.as_str()).as_str());
    (outcome.stmt_results, outcome.runtime_error)
}

fn file_target_error(target_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(target_file_path)),
    ))
    .into()
}
