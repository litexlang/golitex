use crate::prelude::*;
use std::fs;
use std::path::Path;

pub fn parse_lean_command(args: &[String]) -> RuntimeResult<Option<LaunchCommand>> {
    let mut ordinary = Vec::new();
    let mut lean = false;
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "-lean" {
            if lean {
                return Err(RuntimeError::InvalidArguments("`-lean` may appear only once".into()));
            }
            lean = true;
            index += 1;
            continue;
        }
        ordinary.push(arg.clone());
        index += 1;
        let operand = matches!(arg.as_str(), "-e" | "-f" | "-r" | "-lang" | "--lang")
            || (matches!(arg.as_str(), "-extractpython" | "-extractc")
                && !matches!(args.get(index).map(String::as_str), Some("-f" | "-r")));
        if operand && index < args.len() {
            ordinary.push(args[index].clone());
            index += 1;
        }
    }
    if !lean {
        return Ok(None);
    }
    let command = parse_launch_command(&ordinary)?;
    match &command {
        LaunchCommand::File { session: false, .. } => Ok(Some(command)),
        _ => Err(RuntimeError::InvalidArguments(
            "`-lean` currently requires standalone -f and does not take -session or other output modes".into(),
        )),
    }
}

pub fn run_compile_to_lean(command: LaunchCommand) -> Result<String, String> {
    let LaunchCommand::File { path, session: false, .. } = &command else {
        return Err("phase=launch: `-lean` requires standalone -f".into());
    };
    let path = path.clone();
    if path.parent().unwrap_or(Path::new(".")).join("litex.config").exists() {
        return Err("phase=compile: module proof closure is not supported yet; use a standalone source file".into());
    }
    let source = fs::read_to_string(&path)
        .map_err(|error| format!("phase=verify: cannot read {}: {error}", path.display()))?;
    let namespace = artifact_namespace(&path);
    let mut runtime = Runtime::new(command);
    let result = runtime.run_litex_code(&source)
        .map_err(|error| format!("phase=verify: {error}"))?;
    if !result.success {
        let failure = result.statement_results.iter().position(|result| result.is_failed());
        return Err(match failure {
            Some(index) => format!("phase=verify: statement {} failed Litex verification", index + 1),
            None => format!("phase=verify: {}", result.session_error.as_ref()
                .map(ToString::to_string).unwrap_or_else(|| "source run failed".into())),
        });
    }
    crate::compile_to_lean::compile_run(&result, &runtime, &namespace)
        .map_err(|error| format!("phase=compile: {error}"))
}

fn artifact_namespace(path: &Path) -> String {
    let cwd = std::env::current_dir().ok();
    let relative = cwd.as_ref().and_then(|cwd| path.strip_prefix(cwd).ok()).unwrap_or(path);
    let label = relative.components()
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
