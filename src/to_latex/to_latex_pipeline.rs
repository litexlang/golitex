use crate::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

fn latex_fragment(math_blocks: &[String]) -> String {
    let mut blocks = Vec::new();
    if math_blocks.is_empty() {
        blocks.push("% No statements parsed.".to_string());
    } else {
        for block in math_blocks.iter() {
            let t = block.trim();
            if t.is_empty() {
                continue;
            }
            blocks.push(format!("\\[\n{}\n\\]", t));
        }
        if blocks.is_empty() {
            blocks.push("% No non-empty LaTeX blocks.".to_string());
        }
    }
    blocks.join("\n\n")
}

// Parse-only path: one blank-separated block per top-level stmt via `Stmt::to_latex_string`.
// Returns a LaTeX fragment; callers can embed it in their own document wrapper if needed.
pub fn to_latex(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut math_blocks: Vec<String> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        math_blocks.push(stmt.to_latex_string());
        if matches!(
            stmt,
            Stmt::Command(CommandStmt::ImportStmt(_))
                | Stmt::Command(CommandStmt::TrustImportStmt(_))
        ) {
            run_stmt_at_global_env(&stmt, runtime)?;
        }
    }
    Ok(latex_fragment(&math_blocks))
}

pub fn to_latex_from_file_after_builtins(file_path: &str) -> Result<String, RuntimeError> {
    let resolved_path = resolve_file_path(file_path)?;
    let mut runtime = Runtime::new_with_builtin_code();
    match discover_repository_for_file(&mut runtime, resolved_path.as_str())? {
        Some(target) => to_latex_project_target(&mut runtime, target),
        None => {
            let source = read_source(resolved_path.as_str())?;
            runtime.new_file_path_new_env_new_name_scope(resolved_path.as_str());
            to_latex(source.as_str(), &mut runtime)
        }
    }
}

pub fn to_latex_from_source_after_builtins(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_latex(normalized.as_str(), &mut runtime)
}

pub fn to_latex_from_repository_after_builtins(
    repository_path: &str,
) -> Result<String, RuntimeError> {
    let mut runtime = Runtime::new_with_builtin_code();
    discover_repository(&mut runtime, repository_path)?;
    let entry_module_id = runtime.current_module_id();
    to_latex_project_target(&mut runtime, RepositoryFileTarget::Module(entry_module_id))
}

fn to_latex_project_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
    match target {
        RepositoryFileTarget::Module(module_id) => {
            let (module_path, run_targets) = {
                let module = runtime
                    .module_manager
                    .module(module_id)
                    .expect("discovered module should exist");
                (module.main_file_path.clone(), module.run_targets.clone())
            };
            let pushed_frame = runtime.current_module_id() != module_id;
            if pushed_frame {
                runtime.push_module_execution_frame(module_id, module_path.as_str());
            }
            let output = (|| {
                let mut fragments = vec![];
                for run_target in run_targets {
                    let fragment = match run_target {
                        ImportTarget::File { module_id, file_id } => to_latex_project_target(
                            runtime,
                            RepositoryFileTarget::File { module_id, file_id },
                        ),
                        ImportTarget::Module(module_id) => to_latex_project_target(
                            runtime,
                            RepositoryFileTarget::Module(module_id),
                        ),
                    }?;
                    if !fragment.trim().is_empty() {
                        fragments.push(fragment);
                    }
                }
                Ok(fragments.join("\n\n"))
            })();
            if pushed_frame {
                runtime.pop_execution_frame();
            }
            output
        }
        RepositoryFileTarget::File { module_id, file_id } => {
            let source_path = runtime
                .module_manager
                .module(module_id)
                .and_then(|module| module.file(file_id))
                .expect("registered project file should exist")
                .source_path
                .clone();
            runtime.push_file_execution_frame(module_id, file_id, source_path.as_str());
            let output = read_source(source_path.as_str())
                .and_then(|source| to_latex(source.as_str(), runtime));
            runtime.pop_execution_frame();
            output
        }
    }
}

fn resolve_file_path(file_path: &str) -> Result<String, RuntimeError> {
    let path = Path::new(file_path);
    let absolute = if path.is_absolute() {
        PathBuf::from(path)
    } else {
        env::current_dir()
            .map_err(|error| {
                file_error(
                    file_path,
                    format!("failed to get current directory: {}", error),
                )
            })?
            .join(path)
    };
    let canonical = fs::canonicalize(&absolute)
        .map_err(|error| file_error(file_path, format!("could not read file: {}", error)))?;
    canonical
        .to_str()
        .map(str::to_string)
        .ok_or_else(|| file_error(file_path, "file path is not valid UTF-8".to_string()))
}

fn read_source(path: &str) -> Result<String, RuntimeError> {
    fs::read_to_string(path)
        .map(|source| source.replace('\r', ""))
        .map_err(|error| file_error(path, format!("could not read file: {}", error)))
}

fn file_error(path: &str, message: String) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (0, Rc::from(path)),
    ))
    .into()
}
