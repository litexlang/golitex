use crate::prelude::*;
use std::fs;
use std::rc::Rc;

fn latex_fragment(math_blocks: &[String]) -> String {
    let mut blocks = Vec::new();
    if math_blocks.is_empty() {
        blocks.push("% No statements parsed.".to_string());
    } else {
        for block in math_blocks.iter() {
            let t = block.trim();
            if t.is_empty() {
                continue;
            }
            blocks.push(format!("\\[\n{}\n\\]", t));
        }
        if blocks.is_empty() {
            blocks.push("% No non-empty LaTeX blocks.".to_string());
        }
    }
    blocks.join("\n\n")
}

// Parse-only path: one blank-separated block per top-level stmt via `Stmt::to_latex_string`.
// Returns a LaTeX fragment; callers can embed it in their own document wrapper if needed.
pub fn to_latex(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut math_blocks: Vec<String> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        math_blocks.push(stmt.to_latex_string());
    }
    Ok(latex_fragment(&math_blocks))
}

pub fn to_latex_from_source_after_builtins(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_latex(normalized.as_str(), &mut runtime)
}

pub fn to_latex_from_repository_after_builtins(
    repository_path: &str,
) -> Result<String, RuntimeError> {
    let mut runtime = Runtime::new_with_builtin_code();
    let main_file_path = discover_repository(&mut runtime, repository_path)?;
    let source_code = fs::read_to_string(&main_file_path).map_err(|error| {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                format!("failed to read repository main.lit: {}", error),
                (0, Rc::from(main_file_path.as_str())),
            ),
        ))
    })?;
    to_latex(source_code.replace('\r', "").as_str(), &mut runtime)
}
