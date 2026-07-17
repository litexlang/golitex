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
    }
    Ok(latex_fragment(&math_blocks))
}

pub fn to_latex_from_file(file_path: &str) -> Result<String, RuntimeError> {
    let resolved_path = resolve_file_path(file_path)?;
    let mut runtime = Runtime::new();
    match discover_repository_for_file(&mut runtime, resolved_path.as_str())? {
        Some(target) => to_latex_project_run(&mut runtime, target),
        None => {
            let source = read_source(resolved_path.as_str())?;
            runtime.new_file_path_new_env_new_name_scope(resolved_path.as_str());
            to_latex(source.as_str(), &mut runtime)
        }
    }
}

pub fn to_latex_from_source(source_code: &str, entry_label: &str) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_latex(normalized.as_str(), &mut runtime)
}

pub fn to_latex_from_repository(repository_path: &str) -> Result<String, RuntimeError> {
    let mut runtime = Runtime::new();
    let target = discover_repository(&mut runtime, repository_path)?;
    to_latex_project_run(&mut runtime, target)
}

fn to_latex_project_run(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
    let root_module_id = runtime
        .module_manager
        .entry_module_id
        .expect("discovered project should have an entry module");
    if target == RepositoryFileTarget::Module(root_module_id) {
        return to_latex_project_target(runtime, target);
    }
    if !project_target_is_inside_module(runtime, target, root_module_id) {
        return Err(file_error(
            "litex.config",
            "selected target is not inside the entry module export tree".to_string(),
        ));
    }
    to_latex_project_prefix(runtime, root_module_id, target)
}

fn to_latex_project_prefix(
    runtime: &mut Runtime,
    module_id: ModuleId,
    selected_target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
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
            let target_matches = repository_target_matches(selected_target, run_target);
            let target_contains = matches!(
                run_target,
                ImportTarget::Module(child_module_id)
                    if project_target_is_inside_module(runtime, selected_target, child_module_id)
            );
            let fragment = if target_contains && !target_matches {
                let ImportTarget::Module(child_module_id) = run_target else {
                    unreachable!("only a module target can contain another target")
                };
                to_latex_project_prefix(runtime, child_module_id, selected_target)?
            } else {
                to_latex_project_target(runtime, repository_file_target(run_target))?
            };
            if !fragment.trim().is_empty() {
                fragments.push(fragment);
            }
            if target_matches || target_contains {
                return Ok(fragments.join("\n\n"));
            }
        }
        Err(file_error(
            module_path.as_str(),
            "selected target is missing from its recursive ordered [export] tree".to_string(),
        ))
    })();
    if pushed_frame {
        runtime.pop_execution_frame();
    }
    output
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

fn repository_target_matches(target: RepositoryFileTarget, import_target: ImportTarget) -> bool {
    match (target, import_target) {
        (RepositoryFileTarget::Module(target_module), ImportTarget::Module(module_id)) => {
            target_module == module_id
        }
        (
            RepositoryFileTarget::File {
                module_id: target_module,
                file_id: target_file,
            },
            ImportTarget::File { module_id, file_id },
        ) => target_module == module_id && target_file == file_id,
        _ => false,
    }
}

fn repository_file_target(target: ImportTarget) -> RepositoryFileTarget {
    match target {
        ImportTarget::Module(module_id) => RepositoryFileTarget::Module(module_id),
        ImportTarget::File { module_id, file_id } => {
            RepositoryFileTarget::File { module_id, file_id }
        }
    }
}

fn project_target_is_inside_module(
    runtime: &Runtime,
    target: RepositoryFileTarget,
    ancestor_module_id: ModuleId,
) -> bool {
    let mut module_id = Some(match target {
        RepositoryFileTarget::Module(module_id) => module_id,
        RepositoryFileTarget::File { module_id, .. } => module_id,
    });
    while let Some(current) = module_id {
        if current == ancestor_module_id {
            return true;
        }
        module_id = runtime
            .module_manager
            .module(current)
            .and_then(|module| module.parent_module_id);
    }
    false
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
