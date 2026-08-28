//! Project config loading, enclosing roots, parent checks, and directory validation.

use super::*;

pub(super) fn require_project_config(
    directory: &Path,
    source_path: &str,
    line: usize,
) -> Result<PathBuf, RuntimeError> {
    let config_path = directory.join(LITEX_CONFIG);
    require_file(
        &config_path,
        format!(
            "project directory `{}` does not contain {}",
            directory.to_string_lossy(),
            LITEX_CONFIG
        ),
        source_path,
        line,
    )?;
    Ok(config_path)
}

pub(super) fn read_project_config(config_path: &Path) -> Result<ProjectConfig, RuntimeError> {
    let config_path_string = path_string(config_path, &config_path.to_string_lossy(), 0)?;
    let content = fs::read_to_string(config_path).map_err(|error| {
        repository_error(
            format!(
                "failed to read {}: {}",
                config_path.to_string_lossy(),
                error
            ),
            config_path_string.as_str(),
            0,
        )
    })?;
    parse_project_config(content.as_str(), config_path_string.as_str())
}

pub(super) fn enclosing_module_root(
    requested_root: &Path,
    requested_config_path: &Path,
    requested_config: &ProjectConfig,
    source_path: &str,
) -> Result<PathBuf, RuntimeError> {
    let mut current_root = requested_root.to_path_buf();
    let mut current_config_path = requested_config_path.to_path_buf();
    let mut current_config = requested_config.clone();
    loop {
        if current_config.hierarchy == ProjectHierarchy::Module {
            reject_module_with_configured_parent(
                &current_root,
                &current_config_path,
                &current_config,
            )?;
            return Ok(current_root);
        }
        let parent = current_root.parent().ok_or_else(|| {
            repository_error(
                "submodule hierarchy reached the filesystem root without finding a module"
                    .to_string(),
                source_path,
                current_config.hierarchy_line,
            )
        })?;
        let parent_config_path = require_project_config(
            parent,
            &current_config_path.to_string_lossy(),
            current_config.hierarchy_line,
        )?;
        let parent_config = read_project_config(&parent_config_path)?;
        let current_name = current_root
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| {
                repository_error(
                    "submodule folder name is not valid UTF-8".to_string(),
                    &current_config_path.to_string_lossy(),
                    current_config.hierarchy_line,
                )
            })?;
        let exported_by_parent = parent_config.exports.iter().any(|export| {
            direct_child_name(
                export.path.as_str(),
                &parent_config_path.to_string_lossy(),
                export.line,
                "[export]",
            )
            .is_ok_and(|name| name == current_name)
        });
        if !exported_by_parent {
            return Err(repository_error(
                format!(
                    "submodule folder `{}` is not directly exported by its parent litex.config",
                    current_root.to_string_lossy()
                ),
                &current_config_path.to_string_lossy(),
                current_config.hierarchy_line,
            ));
        }
        current_root = parent.to_path_buf();
        current_config_path = parent_config_path;
        current_config = parent_config;
    }
}

pub(super) fn reject_module_with_configured_parent(
    module_root: &Path,
    config_path: &Path,
    config: &ProjectConfig,
) -> Result<(), RuntimeError> {
    if module_root
        .parent()
        .is_some_and(|parent| parent.join(LITEX_CONFIG).is_file())
    {
        return Err(repository_error(
            "a [hierarchy] module cannot have a configured parent folder".to_string(),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    Ok(())
}

pub(super) fn validate_config_directory_contents(
    config_path: &Path,
    config: &ProjectConfig,
) -> Result<(), RuntimeError> {
    let root = config_path.parent().ok_or_else(|| {
        repository_error(
            "litex.config has no containing folder".to_string(),
            &config_path.to_string_lossy(),
            0,
        )
    })?;
    let mut exported_children = HashMap::new();
    for export in config.exports.iter() {
        let child_name = direct_child_name(
            export.path.as_str(),
            &config_path.to_string_lossy(),
            export.line,
            "[export]",
        )?;
        if let Some(previous_line) = exported_children.insert(child_name.clone(), export.line) {
            return Err(repository_error(
                format!(
                    "[export] path `{}` is declared more than once (first declared on line {})",
                    child_name, previous_line
                ),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
    }
    let entries = fs::read_dir(root).map_err(|error| {
        repository_error(
            format!(
                "failed to inspect configured folder `{}`: {}",
                root.to_string_lossy(),
                error
            ),
            &config_path.to_string_lossy(),
            0,
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            repository_error(
                format!("failed to inspect configured folder entry: {}", error),
                &config_path.to_string_lossy(),
                0,
            )
        })?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let path = entry.path();
        if name == LITEX_CONFIG {
            continue;
        }
        // Local work records are outside the ordered, publishable module tree.
        if name == LOCAL_DRAFTS {
            continue;
        }
        if name == LITEX_TODO {
            let source = fs::read_to_string(&path).map_err(|error| {
                repository_error(
                    format!("failed to read todo.lit: {}", error),
                    &path.to_string_lossy(),
                    0,
                )
            })?;
            let source_without_documentation =
                Tokenizer::new().strip_triple_quote_comment_blocks(&source);
            if let Some(line) = source_without_documentation
                .lines()
                .position(|line| !line.trim().is_empty() && !line.trim().starts_with('#'))
            {
                return Err(repository_error(
                    "todo.lit must be comment-only".to_string(),
                    &path.to_string_lossy(),
                    line + 1,
                ));
            }
            continue;
        }
        let is_litex_source =
            path.extension().and_then(|extension| extension.to_str()) == Some("lit");
        if !path.is_dir() && !is_litex_source {
            continue;
        }
        if !exported_children.contains_key(&name) {
            return Err(repository_error(
                format!(
                    "configured folder contains unexported Litex module path `{}`; every direct child directory or .lit file must appear in [export]",
                    name
                ),
                &config_path.to_string_lossy(),
                0,
            ));
        }
    }
    Ok(())
}
