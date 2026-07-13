use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct ProjectConfig {
    pub run_paths: Vec<ProjectRunPath>,
    pub exports: Vec<ProjectExport>,
}

#[derive(Clone)]
pub struct ProjectRunPath {
    pub path: String,
    pub line: usize,
}

#[derive(Clone)]
pub struct ProjectExport {
    pub name: String,
    pub path: String,
    pub line: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConfigTable {
    Run,
    Export,
}

pub fn parse_project_config(
    source: &str,
    config_path: &str,
) -> Result<ProjectConfig, RuntimeError> {
    let mut current_table = None;
    let mut run_paths = vec![];
    let mut exports = vec![];
    let mut export_names = HashSet::new();

    for (index, raw_line) in source.lines().enumerate() {
        let line = index + 1;
        let text = raw_line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }

        if text.starts_with('[') || text.ends_with(']') {
            current_table = match text {
                "[run]" => Some(ConfigTable::Run),
                "[export]" => Some(ConfigTable::Export),
                _ => {
                    return Err(config_error(
                        config_path,
                        line,
                        "litex.config only supports [run] and [export] tables; replace [entrance] with [run]",
                    ))
                }
            };
            continue;
        }

        match current_table {
            Some(ConfigTable::Run) => {
                if text.contains('=') {
                    return Err(config_error(
                        config_path,
                        line,
                        "[run] entries are bare relative paths, for example `./chapter01.lit`",
                    ));
                }
                let path = parse_run_path(text, config_path, line)?;
                run_paths.push(ProjectRunPath { path, line });
            }
            Some(ConfigTable::Export) => {
                let Some((key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[export] expects `name = \"path\"`",
                    ));
                };
                let key = key.trim();
                let value = parse_quoted_path(raw_value.trim(), config_path, line)?;
                is_valid_litex_name(key)
                    .map_err(|message| config_error(config_path, line, message.as_str()))?;
                if !export_names.insert(key.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate export name `{}`", key).as_str(),
                    ));
                }
                exports.push(ProjectExport {
                    name: key.to_string(),
                    path: value,
                    line,
                });
            }
            None => {
                return Err(config_error(
                    config_path,
                    line,
                    "declare [run] or [export] before configuration values",
                ))
            }
        }
    }

    if run_paths.is_empty() {
        return Err(config_error(
            config_path,
            0,
            "litex.config must contain a non-empty [run] table",
        ));
    }
    Ok(ProjectConfig { run_paths, exports })
}

fn parse_run_path(value: &str, config_path: &str, line: usize) -> Result<String, RuntimeError> {
    let value = value.trim();
    if value.is_empty() {
        return Err(config_error(
            config_path,
            line,
            "[run] path must not be empty",
        ));
    }
    if value.starts_with('"') || value.ends_with('"') {
        return parse_quoted_path(value, config_path, line);
    }
    Ok(value.to_string())
}

fn parse_quoted_path(value: &str, config_path: &str, line: usize) -> Result<String, RuntimeError> {
    if value.len() < 2 || !value.starts_with('"') || !value.ends_with('"') {
        return Err(config_error(
            config_path,
            line,
            "configuration paths must be quoted strings",
        ));
    }
    let path = &value[1..value.len() - 1];
    if path.is_empty() {
        return Err(config_error(
            config_path,
            line,
            "configuration paths must not be empty",
        ));
    }
    Ok(path.to_string())
}

fn config_error(config_path: &str, line: usize, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (line, Rc::from(config_path)),
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_an_ordered_run_plan_with_bare_paths() {
        let config = parse_project_config(
            "[run]\n./chapter01.lit\n./Algebra\n\n[export]\nchapter1 = \"./chapter01.lit\"\nAlgebra = \"./Algebra\"\n",
            "litex.config",
        )
        .expect("parse run plan");
        assert_eq!(config.run_paths.len(), 2);
        assert_eq!(config.run_paths[0].path, "./chapter01.lit");
        assert_eq!(config.run_paths[1].path, "./Algebra");
    }

    #[test]
    fn rejects_entrance_with_a_migration_message() {
        let result = parse_project_config("[entrance]\nfile = \"./main.lit\"\n", "litex.config");
        let Err(error) = result else {
            panic!("entrance must be rejected");
        };
        assert!(format!("{error:?}").contains("replace [entrance] with [run]"));
    }

    #[test]
    fn rejects_key_value_entries_in_run() {
        let result = parse_project_config("[run]\nfile = \"./main.lit\"\n", "litex.config");
        let Err(error) = result else {
            panic!("run entries must be bare paths");
        };
        assert!(format!("{error:?}").contains("bare relative paths"));
    }
}
