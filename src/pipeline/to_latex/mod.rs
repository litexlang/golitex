use crate::parse::TokenBlock;
use crate::prelude::*;

// Parse-only path: one Litex surface string per top-level stmt (`Stmt::to_string`).
// True LaTeX emission can replace the formatting later without changing the CLI shape.
pub fn to_latex(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let blocks =
        TokenBlock::parse_blocks(source_code, runtime.module_manager.current_file_path_rc())?;
    let mut lines: Vec<String> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        lines.push(stmt.to_string());
    }
    Ok(lines.join("\n\n"))
}

pub fn to_latex_from_source_after_builtins(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    let (_, builtin_error) = super::run_source_code(builtin_code().as_str(), &mut runtime);
    if let Some(e) = builtin_error {
        return Err(e);
    }
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_latex(normalized.as_str(), &mut runtime)
}
