use crate::prelude::*;
use std::fs;
use std::path::Path;

pub fn run_compile_to_lean(
    command: LaunchCommand,
) -> RuntimeResult<crate::run::CompileToLeanResult> {
    let source = compile_source(command).map_err(RuntimeError::Unsupported)?;
    Ok(crate::run::CompileToLeanResult::new(source))
}

fn compile_source(command: LaunchCommand) -> Result<String, String> {
    let LaunchCommand::CompileToLean { path, .. } = &command else {
        return Err("phase=launch: run_compile_to_lean expects CompileToLean".into());
    };
    let path = path.clone();
    if path
        .parent()
        .unwrap_or(Path::new("."))
        .join("litex.config")
        .exists()
    {
        return Err("phase=compile: module proof closure is not supported yet; use a standalone source file".into());
    }
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("phase=verify: cannot read {}: {error}", path.display()))?;
    let namespace = artifact_namespace(&path);
    let mut runtime = Runtime::new(command);
    let result = runtime
        .run_litex_code(&source)
        .map_err(|error| format!("phase=verify: {error}"))?;
    if !result.success {
        let failure = result
            .statement_results
            .iter()
            .position(|result| result.is_failed());
        return Err(match failure {
            Some(index) => format!(
                "phase=verify: statement {} failed Litex verification",
                index + 1
            ),
            None => format!(
                "phase=verify: {}",
                result
                    .session_error
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "source run failed".into())
            ),
        });
    }
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(&result, &runtime);
    compiler
        .compile(&namespace)
        .map_err(|error| format!("phase=compile: {error}"))
}

fn artifact_namespace(path: &Path) -> String {
    let cwd = std::env::current_dir().ok();
    let relative = cwd
        .as_ref()
        .and_then(|cwd| path.strip_prefix(cwd).ok())
        .unwrap_or(path);
    let label = relative
        .components()
        .filter(|component| !matches!(component, std::path::Component::CurDir))
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/");
    let mut safe = String::from("file_");
    for byte in label.bytes() {
        if byte.is_ascii_alphanumeric() {
            safe.push(char::from(byte));
        } else {
            safe.push_str(&format!("_x{byte:02x}_"));
        }
    }
    safe
}

#[cfg(test)]
#[path = "../../tests/unit/run/lean_command/tests.rs"]
mod tests;
