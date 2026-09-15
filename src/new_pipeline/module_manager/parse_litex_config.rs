//! Parse new_pipeline `litex.config` into `LitexConfig` (data only).

use super::litex_config::{LitexConfig, LitexConfigExport, LitexConfigImport};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Parse a `litex.config` source. Paths are resolved against `config_dir`.
/// `[import std] Alias = StdName` (or bare `N`) resolves to `std_root/StdName`.
pub fn parse_litex_config(
    source: &str,
    config_dir: &Path,
    std_root: &Path,
) -> Result<LitexConfig, String> {
    let mut current: Option<Table> = None;
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut import_aliases = HashSet::new();
    let mut export_names = HashSet::new();

    for (index, raw_line) in source.lines().enumerate() {
        let line = index + 1;
        let text = raw_line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }

        if text.starts_with('[') && text.ends_with(']') {
            current = Some(match text {
                "[import]" => Table::Import,
                "[import std]" => Table::ImportStd,
                "[export]" => Table::Export,
                "[hierarchy]" | "[module]" => {
                    return Err(err(
                        line,
                        "new_pipeline litex.config does not use [hierarchy] or [module]",
                    ));
                }
                _ => {
                    return Err(err(
                        line,
                        "litex.config only supports [import], [import std], and [export]",
                    ));
                }
            });
            continue;
        }

        match current {
            Some(Table::Import) => {
                let (alias, rel) = parse_alias_eq_quoted_path(text, line)?;
                check_alias(&alias, line)?;
                if !import_aliases.insert(alias.clone()) {
                    return Err(err(line, &format!("duplicate import alias `{alias}`")));
                }
                imports.push(LitexConfigImport::new(
                    alias,
                    normalize_join(config_dir, &rel),
                ));
            }
            Some(Table::ImportStd) => {
                let (alias, std_name) = parse_import_std_row(text, line)?;
                check_alias(&alias, line)?;
                check_alias(&std_name, line)?;
                if !import_aliases.insert(alias.clone()) {
                    return Err(err(line, &format!("duplicate import alias `{alias}`")));
                }
                imports.push(LitexConfigImport::new(
                    alias,
                    normalize_join(std_root, &std_name),
                ));
            }
            Some(Table::Export) => {
                let (name, rel) = parse_alias_eq_quoted_path(text, line)?;
                check_alias(&name, line)?;
                if !export_names.insert(name.clone()) {
                    return Err(err(line, &format!("duplicate export name `{name}`")));
                }
                if !rel.ends_with(".lit") {
                    return Err(err(line, "[export] path must end with `.lit`"));
                }
                exports.push(LitexConfigExport::new(
                    name,
                    normalize_join(config_dir, &rel),
                ));
            }
            None => {
                return Err(err(
                    line,
                    "declare [import], [import std], or [export] before values",
                ));
            }
        }
    }

    if exports.is_empty() {
        return Err("litex.config must contain a non-empty [export] table".to_string());
    }

    Ok(LitexConfig { imports, exports })
}

#[derive(Clone, Copy)]
enum Table {
    Import,
    ImportStd,
    Export,
}

fn parse_import_std_row(text: &str, line: usize) -> Result<(String, String), String> {
    if let Some((left, right)) = text.split_once('=') {
        let alias = left.trim().to_string();
        let std_name = right.trim().to_string();
        if std_name.is_empty() || std_name.contains('"') {
            return Err(err(
                line,
                "[import std] expects `Alias = StdName` or a bare `StdName`",
            ));
        }
        Ok((alias, std_name))
    } else {
        let name = text.trim().to_string();
        if name.split_whitespace().count() != 1 {
            return Err(err(
                line,
                "[import std] expects `Alias = StdName` or a bare `StdName`",
            ));
        }
        Ok((name.clone(), name))
    }
}

fn parse_alias_eq_quoted_path(text: &str, line: usize) -> Result<(String, String), String> {
    let Some((left, right)) = text.split_once('=') else {
        return Err(err(line, "expected `name = \"path\"`"));
    };
    let alias = left.trim().to_string();
    let path = parse_quoted_path(right.trim(), line)?;
    Ok((alias, path))
}

fn parse_quoted_path(value: &str, line: usize) -> Result<String, String> {
    if value.len() < 2 || !value.starts_with('"') || !value.ends_with('"') {
        return Err(err(line, "paths must be quoted strings"));
    }
    let path = &value[1..value.len() - 1];
    if path.is_empty() {
        return Err(err(line, "paths must not be empty"));
    }
    Ok(path.to_string())
}

fn check_alias(name: &str, line: usize) -> Result<(), String> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(err(line, "empty name"));
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return Err(err(
            line,
            &format!("invalid name `{name}`: must start with a letter or `_`"),
        ));
    }
    if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return Err(err(
            line,
            &format!("invalid name `{name}`: use letters, digits, `_` only"),
        ));
    }
    Ok(())
}

fn normalize_join(base: &Path, rel: &str) -> PathBuf {
    let joined = base.join(rel);
    let mut out = PathBuf::new();
    for comp in joined.components() {
        match comp {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            other => out.push(other.as_os_str()),
        }
    }
    out
}

fn err(line: usize, message: &str) -> String {
    format!("litex.config:{line}: {message}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn parses_import_std_and_export() {
        let source = r#"
[import]
Algebra = "../Algebra"

[import std]
basics
myB = basics

[export]
chap1 = "./chapter01.lit"
"#;
        let cfg = parse_litex_config(source, Path::new("/proj/root"), Path::new("/std")).unwrap();
        assert_eq!(cfg.imports.len(), 3);
        assert_eq!(cfg.imports[0].alias, "Algebra");
        assert_eq!(cfg.imports[1].alias, "basics");
        assert_eq!(cfg.imports[1].path, PathBuf::from("/std/basics"));
        assert_eq!(cfg.imports[2].alias, "myB");
        assert_eq!(cfg.imports[2].path, PathBuf::from("/std/basics"));
        assert_eq!(cfg.exports.len(), 1);
        assert_eq!(cfg.exports[0].name, "chap1");
    }

    #[test]
    fn rejects_hierarchy() {
        let result = parse_litex_config(
            "[hierarchy]\nmodule\n[export]\na = \"./a.lit\"\n",
            Path::new("/proj"),
            Path::new("/std"),
        );
        assert!(result.is_err());
        assert!(result.err().unwrap().contains("hierarchy"));
    }

    #[test]
    fn allows_export_alias_same_as_import() {
        let source = r#"
[import]
chap1 = "../Other"

[export]
chap1 = "./chapter01.lit"
"#;
        parse_litex_config(source, Path::new("/proj"), Path::new("/std")).unwrap();
    }
}
