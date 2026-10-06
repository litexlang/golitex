//! Select source, verify with `exec_stmt`, build IR, render Python/C.

use super::program::ProgramExtractor;
use crate::launch_command::{
    CodeExtractionTarget, ExtractInput, LaunchCommand, OutputLanguage,
};
use crate::module_manager::ExportFileAndItsExecEnv;
use crate::run_module::{
    load_config, resolve_std_root, run_import_module, RunImportModuleOutcome,
};
use crate::runtime::{
    CodeSource, RealOrVirtualPath, Runtime, RuntimeError, RuntimeParseError, RuntimeResult,
};
use crate::tokenize::Tokenizer;
use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

pub(super) fn extract_code(
    source_code: &str,
    runtime: &mut Runtime,
    target: CodeExtractionTarget,
) -> RuntimeResult<String> {
    let mut extractor = ProgramExtractor::new();
    verify_and_extract_into(runtime, source_code, &mut extractor)?;
    render_program(&extractor.into_program(), target)
}

pub fn extract_code_from_source(
    source_code: &str,
    target: CodeExtractionTarget,
) -> RuntimeResult<String> {
    let normalized = source_code.replace('\r', "");
    let command = LaunchCommand::ExtractExecutableCode {
        target,
        input: ExtractInput::Code(normalized.clone()),
        language: OutputLanguage::English,
    };
    let mut runtime = Runtime::new(command);
    extract_code(normalized.as_str(), &mut runtime, target)
}

pub fn extract_code_from_file(
    file_path: &str,
    target: CodeExtractionTarget,
) -> RuntimeResult<String> {
    let resolved_path = resolve_file_path(file_path)?;
    let source = read_source(resolved_path.as_path())?;
    let selected_source = select_marked_source(source.as_str(), resolved_path.as_path())?;
    let command = LaunchCommand::ExtractExecutableCode {
        target,
        input: ExtractInput::File(resolved_path.clone()),
        language: OutputLanguage::English,
    };
    let mut runtime = Runtime::new(command);
    // Drop placeholder; reopen on the real file path with selected source as Eval-like buffer.
    runtime.abort_file();
    runtime.set_code_source(CodeSource::StandaloneFile);
    runtime.begin_file(RealOrVirtualPath::Real(resolved_path.clone()));
    extract_code(selected_source.as_str(), &mut runtime, target)
}

pub fn extract_code_from_repository(
    repository_path: &str,
    target: CodeExtractionTarget,
) -> RuntimeResult<String> {
    let root = PathBuf::from(repository_path);
    if root.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-r requires a repository path".to_string(),
        ));
    }
    if !root.is_dir() {
        return Err(RuntimeError::Io {
            path: root,
            message: "repository path is not a directory".to_string(),
        });
    }

    let std_root = resolve_std_root(Some(&root));
    let root_config = load_config(&root, &std_root)?;

    let command = LaunchCommand::ExtractExecutableCode {
        target,
        input: ExtractInput::Repository(root.clone()),
        language: OutputLanguage::English,
    };
    let mut runtime = Runtime::new(command);
    runtime.abort_file();
    runtime
        .global_module_manager
        .set_root_config(root_config.clone());

    let mut done = HashSet::new();
    let mut running = HashSet::new();
    let mut file_results = Vec::new();
    let mut extractor = ProgramExtractor::new();

    for import in &root_config.imports {
        match run_import_module(
            &mut runtime,
            &import.path,
            &import.alias,
            &std_root,
            &mut done,
            &mut running,
            &mut file_results,
        )? {
            RunImportModuleOutcome::Done => {}
            RunImportModuleOutcome::SessionError(_) => {
                return Err(RuntimeError::Unsupported(
                    "code extraction stopped: repository import failed".to_string(),
                ));
            }
        }
    }

    for (export_file_id, export) in root_config.exports.iter().enumerate() {
        extract_export_file_into(
            &mut runtime,
            &export.name,
            &export.path,
            export_file_id,
            &mut extractor,
        )?;
        let _ = export_file_id;
    }

    render_program(&extractor.into_program(), target)
}

fn extract_export_file_into(
    runtime: &mut Runtime,
    export_name: &str,
    export_path: &Path,
    export_file_id: usize,
    extractor: &mut ProgramExtractor,
) -> RuntimeResult<()> {
    if !export_path.is_file() {
        return Err(RuntimeError::Io {
            path: export_path.to_path_buf(),
            message: "export `.lit` file not found".to_string(),
        });
    }
    let source = read_source(export_path)?;
    runtime
        .global_module_manager
        .set_current_mod_id(None)
        .map_err(RuntimeError::InternalBug)?;
    runtime.set_code_source(CodeSource::RootExport { export_file_id });
    runtime.begin_file(RealOrVirtualPath::Real(export_path.to_path_buf()));

    let outcome = verify_and_extract_into(runtime, &source, extractor);
    if outcome.is_err() {
        runtime.abort_file();
        let _ = runtime.global_module_manager.set_current_mod_id(None);
        return outcome;
    }

    let (_file, exec_env) = runtime.finish_file();
    let recorded = ExportFileAndItsExecEnv::new(
        export_name.to_string(),
        export_path.to_path_buf(),
        exec_env,
    );
    let _ = export_file_id;
    runtime.global_module_manager.record_root_export(recorded);
    let _ = runtime.global_module_manager.set_current_mod_id(None);
    Ok(())
}

fn verify_and_extract_into(
    runtime: &mut Runtime,
    source_code: &str,
    extractor: &mut ProgramExtractor,
) -> RuntimeResult<()> {
    let token_blocks = Tokenizer::new().tokenize(source_code, runtime.current_file.clone())?;
    let stmts = runtime.parse(&token_blocks)?;
    for stmt in &stmts {
        match runtime.exec_stmt(stmt) {
            Ok(outcome) => {
                if outcome.is_failed() {
                    return Err(RuntimeError::Unsupported(
                        "code extraction requires every statement to succeed; soft-failed statement"
                            .to_string(),
                    ));
                }
            }
            Err(error) => return Err(error),
        }
        extractor.extract_stmt(stmt)?;
    }
    Ok(())
}

fn render_program(
    program: &super::program::ExtractedProgram,
    target: CodeExtractionTarget,
) -> RuntimeResult<String> {
    match target {
        CodeExtractionTarget::Python => super::python::rendering::render_program(program),
        CodeExtractionTarget::C => super::c::rendering::render_program(program),
    }
}

fn resolve_file_path(file_path: &str) -> RuntimeResult<PathBuf> {
    let path = Path::new(file_path);
    let absolute = if path.is_absolute() {
        PathBuf::from(path)
    } else {
        env::current_dir()
            .map_err(|error| RuntimeError::Io {
                path: PathBuf::from(file_path),
                message: format!("failed to get current directory: {}", error),
            })?
            .join(path)
    };
    fs::canonicalize(&absolute).map_err(|error| RuntimeError::Io {
        path: PathBuf::from(file_path),
        message: format!("could not read file: {}", error),
    })
}

fn read_source(path: &Path) -> RuntimeResult<String> {
    fs::read_to_string(path)
        .map(|source| source.replace('\r', ""))
        .map_err(|error| RuntimeError::Io {
            path: path.to_path_buf(),
            message: format!("could not read file: {}", error),
        })
}

fn select_marked_source(source: &str, path: &Path) -> RuntimeResult<String> {
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

    let _ = found_block;
    Ok(selected)
}

fn marker_error(path: &Path, line: usize, message: String) -> RuntimeError {
    RuntimeError::ParseError(RuntimeParseError::new(
        message,
        line,
        RealOrVirtualPath::Real(path.to_path_buf()),
    ))
}
