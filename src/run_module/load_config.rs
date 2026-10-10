//! Load a module directory's `litex.config` (find + read + parse).

use crate::module_manager::{parse_litex_config, LitexConfig};
use crate::runtime::{RuntimeError, RuntimeResult};
use std::fs;
use std::path::{Path, PathBuf};

pub const LITEX_CONFIG_FILE_NAME: &str = "litex.config";

/// Resolve standard-library root for `[import std]` path sugar.
/// Does not require the directory to exist (only used when ImportStd rows appear).
pub fn resolve_std_root(repo_hint: Option<&Path>) -> PathBuf {
    if let Ok(path) = std::env::var("LITEX_STD_PATH") {
        return PathBuf::from(path);
    }
    let cwd_std = PathBuf::from("std");
    if cwd_std.is_dir() {
        return cwd_std;
    }
    if let Some(repo) = repo_hint {
        let repo_std = repo.join("std");
        if repo_std.is_dir() {
            return repo_std;
        }
    }
    // Installed archives, Homebrew/Scoop, MSI and Debian packages keep std
    // alongside the real executable or under its installation prefix.
    if let Ok(executable) = std::env::current_exe() {
        let executable = executable.canonicalize().unwrap_or(executable);
        if let Some(bin) = executable.parent() {
            let mut candidates = vec![bin.join("std")];
            if let Some(prefix) = bin.parent() {
                candidates.push(prefix.join("std"));
                candidates.push(prefix.join("share/litex/std"));
                if let Some(parent) = prefix.parent() {
                    candidates.push(parent.join("share/litex/std"));
                }
            }
            for candidate in candidates {
                if candidate.is_dir() {
                    return candidate;
                }
            }
        }
    }
    if let Some(repo) = repo_hint {
        return repo.join("std");
    }
    cwd_std
}

/// `module_dir/litex.config` must exist.
pub fn litex_config_path(module_dir: &Path) -> PathBuf {
    module_dir.join(LITEX_CONFIG_FILE_NAME)
}

/// Find, read, and parse `litex.config` for `module_dir`.
pub fn load_config(module_dir: &Path, std_root: &Path) -> RuntimeResult<LitexConfig> {
    let path = litex_config_path(module_dir);
    if !path.is_file() {
        return Err(RuntimeError::Io {
            path: path.clone(),
            message: format!(
                "missing `{}` in module directory `{}`",
                LITEX_CONFIG_FILE_NAME,
                module_dir.display()
            ),
        });
    }
    let source = fs::read_to_string(&path).map_err(|error| RuntimeError::Io {
        path: path.clone(),
        message: error.to_string(),
    })?;
    parse_litex_config(&source, module_dir, std_root).map_err(RuntimeError::InvalidArguments)
}

/// Like `load_config`, but missing `litex.config` → empty config (isolated `-f`).
pub fn load_config_or_empty(module_dir: &Path, std_root: &Path) -> RuntimeResult<LitexConfig> {
    let path = litex_config_path(module_dir);
    if !path.is_file() {
        return Ok(LitexConfig::new());
    }
    load_config(module_dir, std_root)
}

/// Normalize a module directory path for done/running sets.
pub fn normalize_module_dir(path: &Path) -> PathBuf {
    match path.canonicalize() {
        Ok(canonical) => canonical,
        Err(_) => path.to_path_buf(),
    }
}
