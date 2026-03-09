use std::collections::HashMap;
use crate::runtime_context::RuntimeContext;
use crate::module_manager::ModuleManager;
use crate::environment::Environment;
use crate::parse::TokenBlock;
use crate::parse::Parser;
use crate::execute::Executor;
use crate::stmt::Stmt;

pub fn run_source_code(source_code: &str) -> String {
    let mut module_manager = ModuleManager::new();
    let environment: Box<Environment> = Box::new(Environment::new(
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(),
    ));

    let builtin_environment: Box<Environment> = Box::new(Environment::new(
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(),
        HashMap::new(), HashMap::new(),
    ));

    let mut runtime_context = RuntimeContext::new(&mut module_manager, vec![environment], builtin_environment, HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new());

    let blocks = match TokenBlock::parse_blocks(source_code, 0) {
        Ok(b) => b,
        Err(e) => return format!("parse block error: {}", e),
    };

    let parser = Parser::new();
    let mut executor = Executor::new(&mut runtime_context);
    let mut out = String::new();

    for block in blocks {
        let mut tb = block;
        let stmt: Stmt = match parser.stmt(&mut tb) {
            Ok(s) => s,
            Err(e) => return format!("parse error: {}", e),
        };
        let result = match executor.stmt(&stmt) {
            Ok(r) => r,
            Err(e) => return format!("exec error: {}", e),
        };
        if !out.is_empty() {
            out.push('\n');
        }
        if let Some(line_file_index) = result.line_file() {
            out.push_str(format!("{}\n{}", executor.line_file_index_string(line_file_index.0, line_file_index.1), result).as_str());
        } else {
            out.push_str(format!("{}", result).as_str());
        }
    }

    out
}
