use crate::environment::Environment;
use crate::execute::Executor;
use crate::module_manager::ModuleManager;
use crate::parse::TokenBlock;
use crate::runtime_context::RuntimeContext;
use crate::stmt::Stmt;
use std::fs;

pub fn run_source_code_in_file(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code(&source_code, entrance_file_path)
}

fn run_source_code(source_code: &str, entrance_file_path: &str) -> String {
    let mut module_manager = ModuleManager::new_empty_module_manager(entrance_file_path);
    let mut builtin_environment = Environment::new_empty_env();

    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );

    let blocks = match TokenBlock::parse_blocks(source_code, 0) {
        Ok(b) => b,
        Err(e) => return format!("\n{}\n", runtime_context.display_error(&e.into())),
    };

    let mut out = String::new();
    let mut executor = Executor::new(&mut runtime_context);
    for mut block in blocks {
        let stmt: Stmt = {
            match executor.parse_stmt(&mut block) {
                Ok(s) => s,
                Err(e) => {
                    out.push_str(
                        format!("\n{}\n", executor.runtime_context.display_error(&e.into()))
                            .as_str(),
                    );
                    return out;
                }
            }
        };
        let result = match executor.exec_stmt(&stmt) {
            Ok(r) => r,
            Err(e) => {
                out.push_str(
                    format!("\n{}\n", executor.runtime_context.display_error(&e)).as_str(),
                );
                return out;
            }
        };
        out.push('\n');
        out.push_str(executor.runtime_context.display_result(&result).as_str());
        out.push('\n');
    }
    out
}
