use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct ProjectConfig {
    pub hierarchy: ProjectHierarchy,
    pub hierarchy_line: usize,
    pub module_flatten: bool,
    pub module_flatten_line: Option<usize>,
    pub imports: Vec<ProjectImport>,
    pub std_imports: Vec<ProjectStdImport>,
    pub exports: Vec<ProjectExport>,
    pub allow_bare_exports: Vec<ProjectBareName>,
    pub allow_bare_std_imports: Vec<ProjectBareName>,
    pub allow_bare_imports: Vec<ProjectBareName>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectHierarchy {
    Module,
    Submodule,
}

#[derive(Clone)]
pub struct ProjectImport {
    pub name: String,
    pub path: String,
    pub line: usize,
}

#[derive(Clone)]
pub struct ProjectStdImport {
    pub name: String,
    pub line: usize,
}

#[derive(Clone)]
pub struct ProjectExport {
    pub name: String,
    pub path: String,
    pub line: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectBareName {
    pub name: String,
    pub line: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConfigTable {
    Hierarchy,
    Module,
    Import,
    ImportStd,
    Export,
    AllowBareExport,
    AllowBareImportStd,
    AllowBareImport,
}

pub fn parse_project_config(
    source: &str,
    config_path: &str,
) -> Result<ProjectConfig, RuntimeError> {
    let mut current_table = None;
    let mut hierarchy = None;
    let mut module_flatten = false;
    let mut module_flatten_line = None;
    let mut imports = vec![];
    let mut std_imports = vec![];
    let mut exports = vec![];
    let mut allow_bare_exports = vec![];
    let mut allow_bare_std_imports = vec![];
    let mut allow_bare_imports = vec![];
    let mut import_names = HashSet::new();
    let mut std_import_names = HashSet::new();
    let mut export_names = HashSet::new();
    let mut allow_bare_export_names = HashSet::new();
    let mut allow_bare_std_import_names = HashSet::new();
    let mut allow_bare_import_names = HashSet::new();

    for (index, raw_line) in source.lines().enumerate() {
        let line = index + 1;
        let text = raw_line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }

        if text.starts_with('[') && text.ends_with(']') {
            current_table = match text {
                "[hierarchy]" => Some(ConfigTable::Hierarchy),
                "[module]" => Some(ConfigTable::Module),
                "[import]" => Some(ConfigTable::Import),
                "[import std]" => Some(ConfigTable::ImportStd),
                "[export]" => Some(ConfigTable::Export),
                "[allow bare export]" => Some(ConfigTable::AllowBareExport),
                "[allow bare import std]" => Some(ConfigTable::AllowBareImportStd),
                "[allow bare import]" => Some(ConfigTable::AllowBareImport),
                _ => {
                    return Err(config_error(
                        config_path,
                        line,
                        "litex.config only supports the [hierarchy], [module], [import], [import std], [export], [allow bare export], [allow bare import std], and [allow bare import] tables",
                    ))
                }
            };
            continue;
        }

        match current_table {
            Some(ConfigTable::Hierarchy) => {
                if hierarchy.is_some() {
                    return Err(config_error(
                        config_path,
                        line,
                        "[hierarchy] must contain exactly one declaration",
                    ));
                }
                let value = match text {
                    "module" => ProjectHierarchy::Module,
                    "submodule" => ProjectHierarchy::Submodule,
                    _ => {
                        return Err(config_error(
                            config_path,
                            line,
                            "[hierarchy] expects exactly `module` or `submodule`",
                        ))
                    }
                };
                hierarchy = Some((value, line));
            }
            Some(ConfigTable::Module) => {
                let Some((key, value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] expects `flatten = true` or `flatten = false`",
                    ));
                };
                if key.trim() != "flatten" {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] only supports `flatten`",
                    ));
                }
                if module_flatten_line.is_some() {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] may declare `flatten` only once",
                    ));
                }
                module_flatten = match value.trim() {
                    "true" => true,
                    "false" => false,
                    _ => {
                        return Err(config_error(
                            config_path,
                            line,
                            "[module] flatten must be `true` or `false`",
                        ))
                    }
                };
                module_flatten_line = Some(line);
            }
            Some(ConfigTable::Import) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[import] expects `name = \"path\"`",
                    ));
                };
                let raw_key = raw_key.trim();
                let value = parse_quoted_path(raw_value.trim(), config_path, line)?;
                is_valid_litex_name(raw_key)
                    .map_err(|message| config_error(config_path, line, message.as_str()))?;
                if !import_names.insert(raw_key.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate import name `{}`", raw_key).as_str(),
                    ));
                }
                imports.push(ProjectImport {
                    name: raw_key.to_string(),
                    path: value,
                    line,
                });
            }
            Some(ConfigTable::ImportStd) => {
                if text.contains('=') || text.split_whitespace().count() != 1 {
                    return Err(config_error(
                        config_path,
                        line,
                        "[import std] expects exactly one standard package name",
                    ));
                }
                is_valid_litex_name(text)
                    .map_err(|message| config_error(config_path, line, message.as_str()))?;
                if !std_import_names.insert(text.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate standard import name `{}`", text).as_str(),
                    ));
                }
                std_imports.push(ProjectStdImport {
                    name: text.to_string(),
                    line,
                });
            }
            Some(ConfigTable::Export) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[export] expects `name = \"path\"`",
                    ));
                };
                let raw_key = raw_key.trim();
                let value = parse_quoted_path(raw_value.trim(), config_path, line)?;
                is_valid_litex_name(raw_key)
                    .map_err(|message| config_error(config_path, line, message.as_str()))?;
                if !export_names.insert(raw_key.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate export name `{}`", raw_key).as_str(),
                    ));
                }
                exports.push(ProjectExport {
                    name: raw_key.to_string(),
                    path: value,
                    line,
                });
            }
            Some(ConfigTable::AllowBareExport) => parse_bare_name(
                text,
                "[allow bare export]",
                config_path,
                line,
                &mut allow_bare_export_names,
                &mut allow_bare_exports,
            )?,
            Some(ConfigTable::AllowBareImportStd) => parse_bare_name(
                text,
                "[allow bare import std]",
                config_path,
                line,
                &mut allow_bare_std_import_names,
                &mut allow_bare_std_imports,
            )?,
            Some(ConfigTable::AllowBareImport) => parse_bare_name(
                text,
                "[allow bare import]",
                config_path,
                line,
                &mut allow_bare_import_names,
                &mut allow_bare_imports,
            )?,
            None => {
                return Err(config_error(
                    config_path,
                    line,
                    "declare a supported litex.config table before configuration values",
                ))
            }
        }
    }

    let Some((hierarchy, hierarchy_line)) = hierarchy else {
        return Err(config_error(
            config_path,
            0,
            "litex.config must declare `module` or `submodule` under [hierarchy]",
        ));
    };

    if exports.is_empty() {
        return Err(config_error(
            config_path,
            0,
            "litex.config must contain a non-empty [export] table",
        ));
    }
    if module_flatten {
        let flatten_line = module_flatten_line.expect("flatten line should be recorded");
        if hierarchy != ProjectHierarchy::Module {
            return Err(config_error(
                config_path,
                flatten_line,
                "[module] flatten is only available for [hierarchy] module",
            ));
        }
        if exports.len() != 1 {
            return Err(config_error(
                config_path,
                flatten_line,
                "[module] flatten requires exactly one [export] entry",
            ));
        }
        if !exports[0].path.ends_with(".lit") {
            return Err(config_error(
                config_path,
                flatten_line,
                "[module] flatten requires its one [export] entry to be a .lit file",
            ));
        }
    }
    if hierarchy == ProjectHierarchy::Submodule && (!imports.is_empty() || !std_imports.is_empty())
    {
        let line = imports
            .first()
            .map(|import| import.line)
            .or_else(|| std_imports.first().map(|import| import.line))
            .unwrap_or(hierarchy_line);
        return Err(config_error(
            config_path,
            line,
            "only a [hierarchy] module may declare [import] or [import std]",
        ));
    }
    for import in imports.iter() {
        if std_import_names.contains(&import.name) {
            return Err(config_error(
                config_path,
                import.line,
                format!(
                    "[import] name `{}` conflicts with an [import std] package name",
                    import.name
                )
                .as_str(),
            ));
        }
    }
    for import in imports.iter() {
        if export_names.contains(&import.name) {
            return Err(config_error(
                config_path,
                import.line,
                format!("`{}` cannot be both an import and an export", import.name).as_str(),
            ));
        }
    }
    for import in std_imports.iter() {
        if export_names.contains(&import.name) {
            return Err(config_error(
                config_path,
                import.line,
                format!(
                    "`{}` cannot be both a standard import and an export",
                    import.name
                )
                .as_str(),
            ));
        }
    }
    validate_allowed_bare_names(
        &allow_bare_exports,
        &export_names,
        "[allow bare export]",
        "[export]",
        config_path,
    )?;
    validate_allowed_bare_names(
        &allow_bare_std_imports,
        &std_import_names,
        "[allow bare import std]",
        "[import std]",
        config_path,
    )?;
    validate_allowed_bare_names(
        &allow_bare_imports,
        &import_names,
        "[allow bare import]",
        "[import]",
        config_path,
    )?;
    for allowed in allow_bare_exports.iter() {
        let export = exports
            .iter()
            .find(|export| export.name == allowed.name)
            .expect("allowed export was checked present");
        if export.path.ends_with(".lit") {
            return Err(config_error(
                config_path,
                allowed.line,
                format!(
                    "[allow bare export] `{}` must name an exported folder/submodule, not a .lit file",
                    allowed.name
                )
                .as_str(),
            ));
        }
    }

    Ok(ProjectConfig {
        hierarchy,
        hierarchy_line,
        module_flatten,
        module_flatten_line,
        imports,
        std_imports,
        exports,
        allow_bare_exports,
        allow_bare_std_imports,
        allow_bare_imports,
    })
}

fn parse_bare_name(
    text: &str,
    table: &str,
    config_path: &str,
    line: usize,
    names: &mut HashSet<String>,
    entries: &mut Vec<ProjectBareName>,
) -> Result<(), RuntimeError> {
    if text.contains('=') || text.split_whitespace().count() != 1 {
        return Err(config_error(
            config_path,
            line,
            format!("{} expects exactly one module name per line", table).as_str(),
        ));
    }
    is_valid_litex_name(text)
        .map_err(|message| config_error(config_path, line, message.as_str()))?;
    if !names.insert(text.to_string()) {
        return Err(config_error(
            config_path,
            line,
            format!("duplicate module name `{}` in {}", text, table).as_str(),
        ));
    }
    entries.push(ProjectBareName {
        name: text.to_string(),
        line,
    });
    Ok(())
}

fn validate_allowed_bare_names(
    entries: &[ProjectBareName],
    declared_names: &HashSet<String>,
    allow_table: &str,
    source_table: &str,
    config_path: &str,
) -> Result<(), RuntimeError> {
    for entry in entries {
        if !declared_names.contains(&entry.name) {
            return Err(config_error(
                config_path,
                entry.line,
                format!(
                    "{} name `{}` must be declared in {}",
                    allow_table, entry.name, source_table
                )
                .as_str(),
            ));
        }
    }
    Ok(())
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
#[path = "../../tests/unit/module_system/project_config/tests.rs"]
mod tests;
