use super::run_command_outcome::{RunFileResult, RunRepoResult};
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};
use std::fs;
use std::path::{Path, PathBuf};

pub fn run_repo(path: PathBuf) -> RuntimeResult<RunRepoResult> {
    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-r requires a repository path".to_string(),
        ));
    }
    let mut runtime = Runtime::new();
    let mut files = Vec::new();
    run_module_dir(&mut runtime, &path, &mut files)?;
    let all_stmts_succeeded = files.iter().all(|file| !file.process_failed());
    Ok(RunRepoResult::new(path, all_stmts_succeeded, files, None))
}

fn run_module_dir(
    runtime: &mut Runtime,
    module_dir: &Path,
    files: &mut Vec<RunFileResult>,
) -> RuntimeResult<()> {
    let config_path = module_dir.join("litex.config");
    let source = fs::read_to_string(&config_path).map_err(|error| RuntimeError::Io {
        path: config_path.clone(),
        message: error.to_string(),
    })?;

    let mut std_imports = Vec::new();
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut current: Option<&str> = None;

    for (index, raw_line) in source.lines().enumerate() {
        let line = index + 1;
        let text = raw_line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }

        if text.starts_with('[') && text.ends_with(']') {
            current = Some(text);
            continue;
        }

        match current {
            Some("[hierarchy]") | Some("[module]") => {}
            Some("[import std]") => {
                if text.contains('=') || text.split_whitespace().count() != 1 {
                    return Err(config_err(
                        &config_path,
                        line,
                        "[import std] expects one name",
                    ));
                }
                std_imports.push(text.to_string());
            }
            Some("[import]") => {
                imports.push(parse_name_eq_path(text, &config_path, line, "[import]")?);
            }
            Some("[export]") => {
                exports.push(parse_name_eq_path(text, &config_path, line, "[export]")?);
            }
            Some(table) => {
                return Err(config_err(
                    &config_path,
                    line,
                    &format!("unsupported litex.config table `{table}`"),
                ))
            }
            None => {
                return Err(config_err(
                    &config_path,
                    line,
                    "declare a table before config values",
                ))
            }
        }
    }

    if exports.is_empty() {
        return Err(config_err(
            &config_path,
            0,
            "litex.config must contain a non-empty [export] table",
        ));
    }

    for name in std_imports {
        return Err(RuntimeError::Unsupported(format!(
            "import std `{name}` is not wired yet"
        )));
    }

    for (_name, rel) in imports {
        run_module_dir(runtime, &module_dir.join(&rel), files)?;
    }

    for (_name, rel) in exports {
        let export_path = module_dir.join(&rel);
        if export_path.is_dir() || export_path.join("litex.config").is_file() {
            run_module_dir(runtime, &export_path, files)?;
            continue;
        }

        let file_source = fs::read_to_string(&export_path).map_err(|error| RuntimeError::Io {
            path: export_path.clone(),
            message: error.to_string(),
        })?;
        runtime.begin_file(RealOrVirtualPath::Real(export_path.clone()), false);
        let code_result = match runtime.run_litex_code(&file_source) {
            Ok(result) => result,
            Err(error) => {
                runtime.abort_file();
                return Err(error);
            }
        };

        if code_result.all_stmts_succeeded {
            let (file, exec_env) = runtime.finish_file();
            runtime.publish_completed_export_file(file, exec_env);
            files.push(RunFileResult::from_code_result(export_path, code_result));
        } else {
            runtime.abort_file();
            files.push(RunFileResult::from_code_result(export_path, code_result));
            return Ok(());
        }
    }

    Ok(())
}

fn parse_name_eq_path(
    text: &str,
    config_path: &Path,
    line: usize,
    table: &str,
) -> RuntimeResult<(String, PathBuf)> {
    let Some((raw_key, raw_value)) = text.split_once('=') else {
        return Err(config_err(
            config_path,
            line,
            &format!("{table} expects `name = \"path\"`"),
        ));
    };
    let name = raw_key.trim().to_string();
    let value = raw_value.trim();
    if value.len() < 2 || !value.starts_with('"') || !value.ends_with('"') {
        return Err(config_err(
            config_path,
            line,
            "path must be a double-quoted string",
        ));
    }
    Ok((name, PathBuf::from(&value[1..value.len() - 1])))
}

fn config_err(config_path: &Path, line: usize, message: &str) -> RuntimeError {
    RuntimeError::InvalidArguments(format!("{}:{}: {}", config_path.display(), line, message))
}
