use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct ProjectConfig {
    pub exports: Vec<ProjectExport>,
}

#[derive(Clone)]
pub struct ProjectExport {
    pub name: String,
    pub path: String,
    pub line: usize,
    pub trusted: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConfigTable {
    Export,
}

pub fn parse_project_config(
    source: &str,
    config_path: &str,
) -> Result<ProjectConfig, RuntimeError> {
    let mut current_table = None;
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
                "[export]" => Some(ConfigTable::Export),
                "[run]" => return Err(config_error(
                    config_path,
                    line,
                    "[run] has been removed; list ordered `name = \"path\"` entries in [export]",
                )),
                _ => {
                    return Err(config_error(
                        config_path,
                        line,
                        "litex.config only supports the [export] table",
                    ))
                }
            };
            continue;
        }

        match current_table {
            Some(ConfigTable::Export) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[export] expects `name = \"path\"` or `trust name = \"path\"`",
                    ));
                };
                let raw_key = raw_key.trim();
                let (trusted, key) = if let Some(name) = raw_key.strip_prefix("trust ") {
                    (true, name.trim())
                } else {
                    (false, raw_key)
                };
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
                    trusted,
                });
            }
            None => {
                return Err(config_error(
                    config_path,
                    line,
                    "declare [export] before configuration values",
                ))
            }
        }
    }

    if exports.is_empty() {
        return Err(config_error(
            config_path,
            0,
            "litex.config must contain a non-empty [export] table",
        ));
    }
    Ok(ProjectConfig { exports })
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
    fn parses_an_ordered_export_plan_with_trusted_entries() {
        let config = parse_project_config(
            "[export]\nchapter1 = \"./chapter01.lit\"\ntrust Algebra = \"./Algebra\"\n",
            "litex.config",
        )
        .expect("parse ordered export plan");
        assert_eq!(config.exports.len(), 2);
        assert_eq!(config.exports[0].name, "chapter1");
        assert!(!config.exports[0].trusted);
        assert_eq!(config.exports[1].name, "Algebra");
        assert!(config.exports[1].trusted);
    }

    #[test]
    fn rejects_run_with_a_migration_message() {
        let result = parse_project_config("[run]\n./main.lit\n", "litex.config");
        let Err(error) = result else {
            panic!("run must be rejected");
        };
        assert!(format!("{error:?}").contains("[run] has been removed"));
    }
}
