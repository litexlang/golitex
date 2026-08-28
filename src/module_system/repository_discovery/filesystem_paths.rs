//! Canonical paths, required files, child names, and repository errors.

use super::*;

pub(super) fn canonical_directory(
    path: &str,
    source_path: &str,
    line: usize,
) -> Result<PathBuf, RuntimeError> {
    let canonical = fs::canonicalize(path).map_err(|error| {
        repository_error(
            format!("module directory `{}` does not exist: {}", path, error),
            source_path,
            line,
        )
    })?;
    if !canonical.is_dir() {
        return Err(repository_error(
            format!("module path `{}` is not a directory", path),
            source_path,
            line,
        ));
    }
    Ok(canonical)
}

pub(super) fn canonical_file(
    path: &Path,
    source_path: &str,
    line: usize,
) -> Result<PathBuf, RuntimeError> {
    let canonical = fs::canonicalize(path).map_err(|error| {
        repository_error(
            format!(
                "source file `{}` does not exist: {}",
                path.to_string_lossy(),
                error
            ),
            source_path,
            line,
        )
    })?;
    if !canonical.is_file() {
        return Err(repository_error(
            format!(
                "configured source path `{}` is not a file",
                path.to_string_lossy()
            ),
            source_path,
            line,
        ));
    }
    Ok(canonical)
}

pub(super) fn require_file(
    path: &Path,
    message: String,
    source_path: &str,
    line: usize,
) -> Result<(), RuntimeError> {
    if path.is_file() {
        Ok(())
    } else {
        Err(repository_error(message, source_path, line))
    }
}

pub(super) fn path_string(
    path: &Path,
    source_path: &str,
    line: usize,
) -> Result<String, RuntimeError> {
    path.to_str().map(str::to_string).ok_or_else(|| {
        repository_error(
            "repository path is not valid UTF-8".to_string(),
            source_path,
            line,
        )
    })
}

pub(super) fn direct_child_name(
    configured_path: &str,
    source_path: &str,
    line: usize,
    table: &str,
) -> Result<String, RuntimeError> {
    let mut child_name = None;
    for component in Path::new(configured_path).components() {
        match component {
            Component::CurDir => {}
            Component::Normal(name) if child_name.is_none() => {
                child_name = name.to_str().map(str::to_string);
            }
            _ => {
                return Err(repository_error(
                    format!("{} paths must name exactly one direct child", table),
                    source_path,
                    line,
                ))
            }
        }
    }
    child_name.ok_or_else(|| {
        repository_error(
            format!("{} paths must name exactly one direct child", table),
            source_path,
            line,
        )
    })
}

pub(super) fn join_module_name(parent: &str, child: &str) -> String {
    if parent.is_empty() {
        child.to_string()
    } else {
        format!("{}{}{}", parent, MOD_SIGN, child)
    }
}

pub(super) fn repository_error(message: String, source_path: &str, line: usize) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (line, Rc::from(source_path)),
    ))
    .into()
}
