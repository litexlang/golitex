use crate::prelude::*;

fn standalone_latex_document(math_blocks: &[String]) -> String {
    let mut body = String::new();
    if math_blocks.is_empty() {
        body.push_str("% No statements parsed.\n");
    } else {
        for (i, block) in math_blocks.iter().enumerate() {
            let t = block.trim();
            if t.is_empty() {
                continue;
            }
            body.push_str(&format!(
                "\\paragraph{{Stmt {}}}\n\\[\n{}\n\\]\n\n",
                i + 1,
                t
            ));
        }
        if body.trim().is_empty() {
            body.push_str("% No non-empty LaTeX blocks.\n");
        }
    }
    format!(
        r"\documentclass{{article}}
\usepackage{{amsmath}}
\usepackage{{amssymb}}
\begin{{document}}
{}
\end{{document}}
",
        body
    )
}

// Parse-only path: one blank-separated block per top-level stmt via `Stmt::to_latex_string`.
// Returns a full LaTeX file (preamble + each stmt in display math) ready for pdflatex/lualatex.
pub fn to_latex(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let blocks =
        tokenizer.parse_blocks(source_code, runtime.module_manager.current_file_path_rc())?;
    let mut math_blocks: Vec<String> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        math_blocks.push(stmt.to_latex_string());
    }
    Ok(standalone_latex_document(&math_blocks))
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
