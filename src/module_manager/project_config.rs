use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct ProjectConfig {
    pub module_flatten: bool,
    pub module_flatten_line: Option<usize>,
    pub imports: Vec<ProjectImport>,
    pub std_imports: Vec<ProjectStdImport>,
    pub exports: Vec<ProjectExport>,
    pub requirements: Vec<ProjectRequirement>,
}

#[derive(Clone)]
pub struct ProjectImport {
    pub name: String,
    pub path: String,
    pub line: usize,
    pub trusted: bool,
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
    pub trusted: bool,
}

#[derive(Clone)]
pub struct ProjectRequirement {
    pub name: String,
    pub dependencies: Vec<String>,
    pub line: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConfigTable {
    Module,
    Import,
    ImportStd,
    Export,
    Requires,
}

pub fn parse_project_config(
    source: &str,
    config_path: &str,
) -> Result<ProjectConfig, RuntimeError> {
    let mut current_table = None;
    let mut module_flatten = false;
    let mut module_flatten_line = None;
    let mut module_flatten_declared = false;
    let mut imports = vec![];
    let mut std_imports = vec![];
    let mut exports = vec![];
    let mut requirements = vec![];
    let mut import_names = HashSet::new();
    let mut std_import_names = HashSet::new();
    let mut export_names = HashSet::new();
    let mut requirement_names = HashSet::new();

    for (index, raw_line) in source.lines().enumerate() {
        let line = index + 1;
        let text = raw_line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }

        if text.starts_with('[') && text.ends_with(']') {
            current_table = match text {
                "[module]" => Some(ConfigTable::Module),
                "[import]" => Some(ConfigTable::Import),
                "[import std]" => Some(ConfigTable::ImportStd),
                "[export]" => Some(ConfigTable::Export),
                "[requires]" => Some(ConfigTable::Requires),
                "[run]" => return Err(config_error(
                    config_path,
                    line,
                    "[run] has been removed; list ordered `name = \"path\"` entries in [export]",
                )),
                _ => {
                    return Err(config_error(
                        config_path,
                        line,
                        "litex.config only supports the [module], [import], [import std], [export], and [requires] tables",
                    ))
                }
            };
            continue;
        }

        match current_table {
            Some(ConfigTable::Module) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] expects `flatten = true` or `flatten = false`",
                    ));
                };
                if raw_key.trim() != "flatten" {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] only supports `flatten`",
                    ));
                }
                if module_flatten_declared {
                    return Err(config_error(
                        config_path,
                        line,
                        "[module] declares `flatten` more than once",
                    ));
                }
                module_flatten_declared = true;
                match raw_value.trim() {
                    "true" => {
                        module_flatten = true;
                        module_flatten_line = Some(line);
                    }
                    "false" => {}
                    _ => {
                        return Err(config_error(
                            config_path,
                            line,
                            "[module] `flatten` must be true or false",
                        ))
                    }
                }
            }
            Some(ConfigTable::Import) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[import] expects `name = \"path\"` or `trust name = \"path\"`",
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
                if !import_names.insert(key.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate import name `{}`", key).as_str(),
                    ));
                }
                imports.push(ProjectImport {
                    name: key.to_string(),
                    path: value,
                    line,
                    trusted,
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
            Some(ConfigTable::Requires) => {
                let Some((raw_key, raw_value)) = text.split_once('=') else {
                    return Err(config_error(
                        config_path,
                        line,
                        "[requires] expects `name = [\"dependency\", ...]`",
                    ));
                };
                let key = raw_key.trim();
                is_valid_litex_name(key)
                    .map_err(|message| config_error(config_path, line, message.as_str()))?;
                if !requirement_names.insert(key.to_string()) {
                    return Err(config_error(
                        config_path,
                        line,
                        format!("duplicate [requires] entry for `{}`", key).as_str(),
                    ));
                }
                requirements.push(ProjectRequirement {
                    name: key.to_string(),
                    dependencies: parse_name_list(raw_value.trim(), config_path, line)?,
                    line,
                });
            }
            None => return Err(config_error(
                config_path,
                line,
                "declare [module], [import], [import std], [export], or [requires] before configuration values",
            )),
        }
    }

    if exports.is_empty() {
        return Err(config_error(
            config_path,
            0,
            "litex.config must contain a non-empty [export] table",
        ));
    }
    if module_flatten && exports.len() != 1 {
        return Err(config_error(
            config_path,
            module_flatten_line.unwrap_or(0),
            "[module] flatten = true requires exactly one [export] entry",
        ));
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

    for requirement in requirements.iter() {
        let Some(target_index) = exports
            .iter()
            .position(|export| export.name == requirement.name)
        else {
            return Err(config_error(
                config_path,
                requirement.line,
                format!(
                    "[requires] target `{}` is not declared in [export]",
                    requirement.name
                )
                .as_str(),
            ));
        };
        let mut dependency_names = HashSet::new();
        for dependency in requirement.dependencies.iter() {
            let Some(dependency_index) =
                exports.iter().position(|export| export.name == *dependency)
            else {
                return Err(config_error(
                    config_path,
                    requirement.line,
                    format!(
                        "[requires] dependency `{}` for `{}` is not declared in [export]",
                        dependency, requirement.name
                    )
                    .as_str(),
                ));
            };
            if dependency_index >= target_index {
                return Err(config_error(
                    config_path,
                    requirement.line,
                    format!(
                        "[requires] dependency `{}` for `{}` must appear earlier in [export]",
                        dependency, requirement.name
                    )
                    .as_str(),
                ));
            }
            if !dependency_names.insert(dependency) {
                return Err(config_error(
                    config_path,
                    requirement.line,
                    format!(
                        "[requires] dependency `{}` is listed more than once for `{}`",
                        dependency, requirement.name
                    )
                    .as_str(),
                ));
            }
        }
    }

    Ok(ProjectConfig {
        module_flatten,
        module_flatten_line,
        imports,
        std_imports,
        exports,
        requirements,
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

fn parse_name_list(
    value: &str,
    config_path: &str,
    line: usize,
) -> Result<Vec<String>, RuntimeError> {
    if !value.starts_with('[') || !value.ends_with(']') {
        return Err(config_error(
            config_path,
            line,
            "[requires] values must be lists of quoted export names",
        ));
    }
    let body = value[1..value.len() - 1].trim();
    if body.is_empty() {
        return Ok(vec![]);
    }
    let mut names = vec![];
    for raw_name in body.split(',') {
        let name = parse_quoted_path(raw_name.trim(), config_path, line)?;
        is_valid_litex_name(name.as_str())
            .map_err(|message| config_error(config_path, line, message.as_str()))?;
        names.push(name);
    }
    Ok(names)
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
    fn parses_imports_and_file_requirements() {
        let config = parse_project_config(
            "[import]\nAlgebra = \"../algebra\"\n\n[export]\nchap3 = \"./chap3.lit\"\nchap7 = \"./chap7.lit\"\n\n[requires]\nchap7 = [\"chap3\"]\n",
            "litex.config",
        )
        .expect("parse dependency configuration");
        assert_eq!(config.imports.len(), 1);
        assert_eq!(config.imports[0].name, "Algebra");
        assert_eq!(config.requirements.len(), 1);
        assert_eq!(config.requirements[0].dependencies, vec!["chap3"]);
    }

    #[test]
    fn parses_standard_imports_separately_from_path_imports() {
        let config = parse_project_config(
            "[import std]\nbasics\nnumber_theory # standard package\n\n[import]\nAlgebra = \"../algebra\"\n\n[export]\nmain = \"./main.lit\"\n",
            "litex.config",
        )
        .expect("parse standard and path imports");
        assert_eq!(config.std_imports.len(), 2);
        assert_eq!(config.std_imports[0].name, "basics");
        assert_eq!(config.std_imports[0].line, 2);
        assert_eq!(config.std_imports[1].name, "number_theory");
        assert_eq!(config.std_imports[1].line, 3);
        assert_eq!(config.imports.len(), 1);
        assert_eq!(config.imports[0].name, "Algebra");
    }

    #[test]
    fn standard_imports_require_one_unique_package_name_per_line() {
        for (source, expected) in [
            (
                "[import std]\nbasics = \"./basics\"\n\n[export]\nmain = \"./main.lit\"\n",
                "expects exactly one standard package name",
            ),
            (
                "[import std]\ntrust basics\n\n[export]\nmain = \"./main.lit\"\n",
                "expects exactly one standard package name",
            ),
            (
                "[import std]\nbasics number_theory\n\n[export]\nmain = \"./main.lit\"\n",
                "expects exactly one standard package name",
            ),
            (
                "[import std]\n1basics\n\n[export]\nmain = \"./main.lit\"\n",
                "name first character cannot be a number or symbol",
            ),
            (
                "[import std]\nbasics\nbasics\n\n[export]\nmain = \"./main.lit\"\n",
                "duplicate standard import name `basics`",
            ),
        ] {
            let Err(error) = parse_project_config(source, "litex.config") else {
                panic!("invalid standard imports must be rejected");
            };
            assert!(format!("{error:?}").contains(expected), "{error:?}");
        }
    }

    #[test]
    fn parses_module_flatten() {
        let config = parse_project_config(
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./implementation.lit\"\n",
            "litex.config",
        )
        .expect("parse flattened module configuration");
        assert!(config.module_flatten);
        assert_eq!(config.module_flatten_line, Some(2));
    }

    #[test]
    fn module_flatten_configuration_is_strict() {
        for (source, expected) in [
            (
                "[module]\nroot = true\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "only supports `flatten`",
            ),
            (
                "[module]\nflatten = true\nflatten = false\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "more than once",
            ),
            (
                "[module]\nflatten = maybe\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "must be true or false",
            ),
            (
                "[module]\nflatten = true\n\n[export]\na = \"./a.lit\"\nb = \"./b.lit\"\n",
                "requires exactly one [export] entry",
            ),
        ] {
            let Err(error) = parse_project_config(source, "litex.config") else {
                panic!("invalid module flatten configuration must be rejected");
            };
            assert!(format!("{error:?}").contains(expected), "{error:?}");
        }
    }

    #[test]
    fn requires_must_point_to_earlier_exports() {
        let result = parse_project_config(
            "[export]\nchap3 = \"./chap3.lit\"\nchap7 = \"./chap7.lit\"\n\n[requires]\nchap3 = [\"chap7\"]\n",
            "litex.config",
        );
        let Err(error) = result else {
            panic!("later dependencies must be rejected");
        };
        assert!(format!("{error:?}").contains("must appear earlier"));
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
