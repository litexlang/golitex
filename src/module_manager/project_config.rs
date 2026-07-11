use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct ProjectConfig {
    pub entrance_path: String,
    pub entrance_line: usize,
    pub exports: Vec<ProjectExport>,
}

#[derive(Clone)]
pub struct ProjectExport {
    pub name: String,
    pub path: String,
    pub line: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConfigTable {
    Entrance,
    Export,
}

pub fn parse_project_config(
    source: &str,
    config_path: &str,
) -> Result<ProjectConfig, RuntimeError> {
    let mut current_table = None;
    let mut entrance_path = None;
    let mut entrance_line = 0;
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
                "[entrance]" => Some(ConfigTable::Entrance),
                "[export]" => Some(ConfigTable::Export),
                _ => {
                    return Err(config_error(
                        config_path,
                        line,
                        "litex.config only supports [entrance] and [export] tables",
                    ))
                }
            };
            continue;
        }

        let Some((key, raw_value)) = text.split_once('=') else {
            return Err(config_error(
                config_path,
                line,
                "expected `name = \"path\"` in litex.config",
            ));
        };
        let key = key.trim();
        let value = parse_quoted_path(raw_value.trim(), config_path, line)?;
        match current_table {
            Some(ConfigTable::Entrance) => {
                if key != "file" {
                    return Err(config_error(
                        config_path,
                        line,
                        "[entrance] only accepts `file = \"path/to/entry.lit\"`",
                    ));
                }
                if entrance_path.is_some() {
                    return Err(config_error(
                        config_path,
                        line,
                        "[entrance] may declare `file` only once",
                    ));
                }
                entrance_path = Some(value);
                entrance_line = line;
            }
            Some(ConfigTable::Export) => {
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
                    "declare [entrance] or [export] before configuration values",
                ))
            }
        }
    }

    let Some(entrance_path) = entrance_path else {
        return Err(config_error(
            config_path,
            0,
            "litex.config must contain [entrance] with `file = \"...\"`",
        ));
    };
    Ok(ProjectConfig {
        entrance_path,
        entrance_line,
        exports,
    })
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
