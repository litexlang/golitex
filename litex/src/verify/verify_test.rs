use std::collections::HashMap;

use crate::atomic_fact::AtomicFact;
use crate::atomic_fact::EqualFact;
use crate::environment::Environment;
use crate::executor::Executor;
use crate::fact::Fact;
use crate::module_manager::ModuleManager;
use crate::obj::{Number, Obj};
use crate::parser::Parser;
use crate::runtime_context::RuntimeContext;
use crate::stmt::Stmt;
use crate::stmt_result::StmtResult;
use crate::token_block::TokenBlock;
use crate::tokenizer::tokenize_line;

#[test]
fn test_verify_atomic_fact() {
    let mut module_manager = ModuleManager::new();
    let environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let builtin_environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let mut runtime_context = RuntimeContext::new(
        &mut module_manager,
        vec![environment],
        builtin_environment,
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let mut executor = Executor::new(&mut runtime_context);

    // verify 1 = 1
    let one = Obj::Number(Number::new("1"));
    let fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(one.clone(), one, None)));
    let stmt = Stmt::Fact(fact);
    let result = executor.stmt(&stmt);

    match result {
        Ok(stmt_result) => {
            println!("{}", stmt_result);
        }
        Err(e) => {
            println!("ERROR:{}", e);
        }
    }
}

/// 从 string → parse → exec 整条链路测试：fact "1 + 1 = 2"
#[test]
fn test_exec_stmt_fact_one_plus_one_eq_two() {
    let s = "1 + 1 = 2";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 0));
    let parser = Parser::new();
    let stmt = parser.stmt(&mut tb).expect("parse fact \"1 + 1 = 2\" failed");
    assert!(matches!(stmt, Stmt::Fact(_)), "expected Stmt::Fact");

    let mut module_manager = ModuleManager::new();
    let environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let builtin_environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let mut runtime_context = RuntimeContext::new(
        &mut module_manager,
        vec![environment],
        builtin_environment,
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
        HashMap::new(),
    );
    let mut executor = Executor::new(&mut runtime_context);

    let result = executor.stmt(&stmt).expect("exec.stmt(fact) failed");
    match &result {
        StmtResult::StmtSuccess(_) => {println!("{}", result);}
        StmtResult::StmtUnknown(u) => panic!("fact 1+1=2 should be verified, got StmtUnknown: {}", u),
        StmtResult::StmtError(e) => panic!("fact 1+1=2 should be verified, got StmtError: {}", e),
    }
}
