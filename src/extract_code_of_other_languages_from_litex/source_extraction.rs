use super::program::{extract_program_from_stmts, ExtractedProgram};
use crate::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

#[derive(Clone, Copy)]
pub(super) enum CodeExtractionTarget {
    Python,
    C,
}

pub(super) fn extract_code(
    source_code: &str,
    runtime: &mut Runtime,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;

    let mut stmts = vec![];
    for mut block in blocks {
        let stmt = runtime.parse_statement(&mut block)?;
        runtime.execute_statement(&stmt)?;
        stmts.push(stmt);
    }

    let program = extract_program_from_stmts(&stmts, runtime)?;
    render_program(&program, target)
}

pub(super) fn extract_code_from_source(
    source_code: &str,
    _source_label: &str,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::CodeExtraction);
    extract_code(normalized.as_str(), &mut runtime, target)
}

pub(super) fn extract_code_from_file(
    file_path: &str,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let resolved_path = resolve_file_path(file_path)?;
    let source = read_source(resolved_path.as_str())?;
    let selected_source = select_marked_source(source.as_str(), resolved_path.as_str())?;
    let mut runtime = Runtime::default();
    runtime.start_real_file(resolved_path.as_str());
    extract_code(selected_source.as_str(), &mut runtime, target)
}

pub(super) fn extract_code_from_repository(
    repository_path: &str,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let mut runtime = Runtime::default();
    let selected_target = discover_repository(&mut runtime, repository_path)?;
    extract_project_run(&mut runtime, selected_target, target)
}

fn extract_project_run(
    runtime: &mut Runtime,
    selected_target: RepositoryFileTarget,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let root_module_id = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .map(|module| module.id)
        .expect("discovered project should have a root module");
    if selected_target == RepositoryFileTarget::Module(root_module_id) {
        return extract_project_target(runtime, selected_target, target);
    }
    if !project_target_is_inside_module(runtime, selected_target, root_module_id) {
        return Err(file_error(
            "litex.config",
            "selected target is not inside the root module export tree".to_string(),
        ));
    }
    extract_project_prefix(runtime, root_module_id, selected_target, target)
}

fn extract_project_prefix(
    runtime: &mut Runtime,
    module_id: ModuleId,
    selected_target: RepositoryFileTarget,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    let (module_path, config_imports, run_targets) = {
        let module = runtime
            .module_manager
            .module(module_id)
            .expect("discovered module should exist");
        (
            module.main_source_label(),
            module.config_imports.clone(),
            module.run_targets.clone(),
        )
    };
    let output = (|| {
        let mut fragments = vec![];
        for config_import in config_imports {
            let fragment = extract_project_target(
                runtime,
                RepositoryFileTarget::Module(config_import.module_id),
                target,
            )?;
            push_fragment(&mut fragments, fragment, target);
        }
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
                extract_project_prefix(runtime, child_module_id, selected_target, target)?
            } else {
                extract_project_target(runtime, repository_file_target(run_target), target)?
            };
            push_fragment(&mut fragments, fragment, target);
            if target_matches || target_contains {
                return Ok(fragments.join("\n"));
            }
        }
        Err(file_error(
            module_path.as_str(),
            "selected target is missing from its recursive ordered [export] tree".to_string(),
        ))
    })();
    if output.is_ok() {
        runtime
            .module_manager
            .module_mut(module_id)
            .expect("discovered module should exist")
            .status = ModuleStatus::Loaded;
    }
    output
}

fn extract_project_target(
    runtime: &mut Runtime,
    selected_target: RepositoryFileTarget,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    match selected_target {
        RepositoryFileTarget::Module(module_id) => {
            let (config_imports, run_targets) = {
                let module = runtime
                    .module_manager
                    .module(module_id)
                    .expect("discovered module should exist");
                (module.config_imports.clone(), module.run_targets.clone())
            };
            let output = (|| {
                let mut fragments = vec![];
                for config_import in config_imports {
                    let fragment = extract_project_target(
                        runtime,
                        RepositoryFileTarget::Module(config_import.module_id),
                        target,
                    )?;
                    push_fragment(&mut fragments, fragment, target);
                }
                for run_target in run_targets {
                    let fragment = extract_project_target(
                        runtime,
                        repository_file_target(run_target),
                        target,
                    )?;
                    push_fragment(&mut fragments, fragment, target);
                }
                Ok(fragments.join("\n"))
            })();
            if output.is_ok() {
                runtime
                    .module_manager
                    .module_mut(module_id)
                    .expect("discovered module should exist")
                    .status = ModuleStatus::Loaded;
            }
            output
        }
        RepositoryFileTarget::File {
            module_id,
            source_id,
        } => {
            let (source_path, status) = {
                let source = runtime
                    .module_manager
                    .module(module_id)
                    .and_then(|module| module.source(source_id))
                    .expect("registered project file should exist");
                let source_path = source
                    .real_file_path()
                    .expect("a repository file target must have a real path")
                    .to_string();
                (source_path, source.load_status)
            };
            if status == SourceLoadStatus::Loaded {
                return Ok(String::new());
            }
            if status == SourceLoadStatus::Loading {
                return Err(file_error(
                    source_path.as_str(),
                    format!("cyclic project entry while extracting {}", target.name()),
                ));
            }
            runtime
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.source_mut(source_id))
                .expect("registered project file should exist")
                .load_status = SourceLoadStatus::Loading;
            let previous_source = runtime.source_activation();
            runtime.activate_source_for_execution(module_id, source_id);
            let output = read_source(source_path.as_str())
                .and_then(|source| extract_code(source.as_str(), runtime, target));
            runtime.restore_source_activation(previous_source);
            runtime
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.source_mut(source_id))
                .expect("registered project file should exist")
                .load_status = if output.is_ok() {
                SourceLoadStatus::Loaded
            } else {
                SourceLoadStatus::Unloaded
            };
            output
        }
    }
}

fn render_program(
    program: &ExtractedProgram,
    target: CodeExtractionTarget,
) -> Result<String, RuntimeError> {
    match target {
        CodeExtractionTarget::Python => super::python::rendering::render_program(program),
        CodeExtractionTarget::C => super::c::rendering::render_program(program),
    }
}

fn push_fragment(fragments: &mut Vec<String>, fragment: String, target: CodeExtractionTarget) {
    if !fragment.trim().is_empty() && fragment.trim() != target.empty_output() {
        fragments.push(fragment);
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
                source_id: target_source,
            },
            ImportTarget::File {
                module_id,
                source_id,
            },
        ) => target_module == module_id && target_source == source_id,
        _ => false,
    }
}

fn repository_file_target(target: ImportTarget) -> RepositoryFileTarget {
    match target {
        ImportTarget::Module(module_id) => RepositoryFileTarget::Module(module_id),
        ImportTarget::File {
            module_id,
            source_id,
        } => RepositoryFileTarget::File {
            module_id,
            source_id,
        },
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

fn select_marked_source(source: &str, path: &str) -> Result<String, RuntimeError> {
    const START_MARKER: &str = "# [-extract]";
    const END_MARKER: &str = "# [end of -extract]";

    let mut selected = String::with_capacity(source.len());
    let mut open_marker_line = None;
    let mut found_block = false;

    for (line_index, line_with_ending) in source.split_inclusive('\n').enumerate() {
        let line = line_with_ending
            .strip_suffix('\n')
            .unwrap_or(line_with_ending);
        let trimmed = line.trim();
        let has_line_ending = line_with_ending.ends_with('\n');

        if trimmed == START_MARKER {
            if open_marker_line.is_some() {
                return Err(marker_error(
                    path,
                    line_index,
                    format!(
                        "nested `{}` marker; close the current block with `{}` first",
                        START_MARKER, END_MARKER
                    ),
                ));
            }
            open_marker_line = Some(line_index);
            found_block = true;
        } else if trimmed == END_MARKER {
            if open_marker_line.is_none() {
                return Err(marker_error(
                    path,
                    line_index,
                    format!("`{}` has no matching `{}` marker", END_MARKER, START_MARKER),
                ));
            }
            open_marker_line = None;
        } else if open_marker_line.is_some() {
            selected.push_str(line);
        }

        if has_line_ending {
            selected.push('\n');
        }
    }

    if let Some(line_index) = open_marker_line {
        return Err(marker_error(
            path,
            line_index,
            format!("`{}` has no matching `{}` marker", START_MARKER, END_MARKER),
        ));
    }
    if !found_block {
        return Err(marker_error(
            path,
            0,
            format!(
                "file extraction requires at least one `{}` block closed by `{}`",
                START_MARKER, END_MARKER
            ),
        ));
    }

    Ok(selected)
}

fn marker_error(path: &str, line: usize, message: String) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (line, Rc::from(path)),
    ))
    .into()
}

fn file_error(path: &str, message: String) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (0, Rc::from(path)),
    ))
    .into()
}

impl CodeExtractionTarget {
    fn name(self) -> &'static str {
        match self {
            Self::Python => "Python",
            Self::C => "C",
        }
    }

    fn empty_output(self) -> &'static str {
        match self {
            Self::Python => "# No Python-extractable Litex definitions.",
            Self::C => "/* No C-extractable Litex definitions. */",
        }
    }
}
