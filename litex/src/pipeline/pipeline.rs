use std::fs;
use crate::runtime_context::RuntimeContext;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use crate::parse::TokenBlock;
use crate::parse::Parser;
use crate::execute::Executor;
use crate::stmt::Stmt;

pub fn run_source_code_in_file(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code(&source_code, entrance_file_path)
}

fn run_source_code(source_code: &str, entrance_file_path: &str) -> String {
    let mut module_manager = ModuleManager::new_empty_module_manager(entrance_file_path);
    let mut builtin_environment = Environment::new_empty_env();

    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(&mut module_manager, &mut builtin_environment);

    let blocks = match TokenBlock::parse_blocks(source_code, 0) {
        Ok(b) => b,
        Err(e) => return format!("parse block error: {}", e),
    };

    let parser = Parser::new();
    let mut executor = Executor::new(&mut runtime_context);
    let mut out = String::new();

    for block in blocks {
        let mut tb = block;
        let stmt: Stmt = match parser.parse_stmt(&mut tb) {
            Ok(s) => s,
            Err(e) => return format!("parse error: {}", e),
        };
        let result = match executor.stmt(&stmt) {
            Ok(r) => r,
            Err(e) => return format!("exec error {}: {}", e.line_file().unwrap_or((0, 0)).0, e),
        };
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(executor.runtime_context.display_result(&result).as_str());
    }

    out
}
