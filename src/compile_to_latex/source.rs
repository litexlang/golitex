use super::compile::to_latex_from_ast;
use super::helper::escape_text;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::module_manager::{GlobalModuleManager, LitexConfig};
use crate::run_module::{load_config, resolve_std_root};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};
use crate::tokenize::Tokenizer;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

/// Parse a complete source batch in the caller's existing parse scope.
pub fn to_latex(source: &str, runtime: &mut Runtime) -> RuntimeResult<String> {
    let blocks = Tokenizer::new().tokenize(source, runtime.current_file.clone())?;
    let stmts = runtime.parse(&blocks)?;
    to_latex_from_ast(
        &stmts,
        &runtime.global_module_manager,
        runtime.launch_command.output_language(),
    )
}

pub fn to_latex_from_source(source: &str, language: OutputLanguage) -> RuntimeResult<String> {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: source.into(),
        session: false,
        strict: false,
        language,
    });
    let cwd = std::env::current_dir().map_err(|error| io_error(Path::new("."), error))?;
    if cwd.join("litex.config").is_file() {
        prepare_modules(&mut runtime, &cwd)?;
    }
    to_latex(source, &mut runtime)
}

pub fn to_latex_from_file(path: &str, language: OutputLanguage) -> RuntimeResult<String> {
    let file = fs::canonicalize(path).map_err(|error| io_error(Path::new(path), error))?;
    let mut root = file.parent();
    while let Some(dir) = root {
        if dir.join("litex.config").is_file() {
            let mut runtime = Runtime::new(LaunchCommand::File {
                path: file.clone(),
                session: false,
                strict: false,
                language,
            });
            let config = prepare_modules(&mut runtime, dir)?;
            let selected = config
                .exports
                .iter()
                .position(|row| fs::canonicalize(&row.path).ok().as_ref() == Some(&file));
            if let Some(index) = selected {
                return render_exports(&mut runtime, &config, Some(index));
            }
            // An unregistered file still has the enclosing module's name metadata.
            let source = read_source(&file)?;
            return to_latex(&source, &mut runtime);
        }
        root = dir.parent();
    }
    let mut runtime = Runtime::new(LaunchCommand::File {
        path: file.clone(),
        session: false,
        strict: false,
        language,
    });
    to_latex(&read_source(&file)?, &mut runtime)
}

pub fn to_latex_from_repository(path: &str, language: OutputLanguage) -> RuntimeResult<String> {
    let root = fs::canonicalize(path).map_err(|error| io_error(Path::new(path), error))?;
    let mut runtime = Runtime::new(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: false,
        language,
    });
    let config = prepare_modules(&mut runtime, &root)?;
    render_exports(&mut runtime, &config, None)
}

fn prepare_modules(runtime: &mut Runtime, root: &Path) -> RuntimeResult<LitexConfig> {
    let std_root = resolve_std_root(Some(root));
    let config = load_config(root, &std_root)?;
    runtime
        .global_module_manager
        .set_root_config(config.clone());
    let mut active = HashSet::new();
    active.insert(fs::canonicalize(root).map_err(|error| io_error(root, error))?);
    let mut done = HashSet::new();
    mount_imports(
        &mut runtime.global_module_manager,
        &config,
        &std_root,
        &mut active,
        &mut done,
    )?;
    Ok(config)
}

// Only manifests are mounted. Imported Litex statements are never run.
fn mount_imports(
    modules: &mut GlobalModuleManager,
    config: &LitexConfig,
    std_root: &Path,
    active: &mut HashSet<PathBuf>,
    done: &mut HashSet<PathBuf>,
) -> RuntimeResult<()> {
    for import in &config.imports {
        let path = fs::canonicalize(&import.path).map_err(|error| io_error(&import.path, error))?;
        if active.contains(&path) {
            return Err(RuntimeError::Unsupported(format!(
                "LaTeX: import cycle at {}",
                path.display()
            )));
        }
        if done.contains(&path) {
            continue;
        }
        let imported = load_config(&path, std_root)?;
        let mut label = import.alias.clone();
        let mut suffix = 1;
        while modules
            .imports()
            .iter()
            .any(|m| m.name == label && m.path != path)
        {
            label = format!("{}_{}", import.alias, suffix);
            suffix += 1;
        }
        modules
            .mount_module(label, path.clone(), imported.clone())
            .map_err(RuntimeError::Unsupported)?;
        active.insert(path.clone());
        mount_imports(modules, &imported, std_root, active, done)?;
        active.remove(&path);
        done.insert(path);
    }
    Ok(())
}

fn render_exports(
    runtime: &mut Runtime,
    config: &LitexConfig,
    through: Option<usize>,
) -> RuntimeResult<String> {
    let mut fragments = Vec::new();
    for (index, export) in config.exports.iter().enumerate() {
        runtime.abort_file();
        runtime.set_code_source(CodeSource::RootExport {
            export_file_id: index,
        });
        runtime.begin_file(RealOrVirtualPath::Real(export.path.clone()));
        let fragment = to_latex(&read_source(&export.path)?, runtime)?;
        fragments.push(format!(
            "\\section*{{{}}}\n{}",
            escape_text(&export.name),
            fragment
        ));
        if through == Some(index) {
            break;
        }
    }
    Ok(fragments.join("\n"))
}
fn read_source(path: &Path) -> RuntimeResult<String> {
    fs::read_to_string(path).map_err(|error| io_error(path, error))
}
fn io_error(path: &Path, error: std::io::Error) -> RuntimeError {
    RuntimeError::Io {
        path: path.into(),
        message: error.to_string(),
    }
}
