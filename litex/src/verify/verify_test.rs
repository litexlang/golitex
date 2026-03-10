use std::collections::HashMap;

use crate::verify::VerifyState;
use crate::fact::AtomicFact;
use crate::fact::EqualFact;
use crate::environment::Environment;
use crate::execute::Executor;
use crate::fact::Fact;
use crate::module_manager::ModuleManager;
use crate::obj::{Number, Obj};
use crate::parse::Parser;
use crate::runtime_context::RuntimeContext;
use crate::stmt::Stmt;
use crate::result::StmtResult;
use crate::parse::TokenBlock;
use crate::parse::tokenize_line;

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
        StmtResult::NonFactualStmtSuccess(_) | StmtResult::FactVerifiedByFact(_) | StmtResult::FactVerifiedByBuiltinRules(_) => println!("{}", result),
        StmtResult::StmtUnknown(u) => panic!("fact 1+1=2 should be verified, got StmtUnknown: {}", u),
    }
}

#[test]
fn test_verify_state() {
    let mut verify_state = VerifyState::new(0, false);
    assert!(!verify_state.is_final_round());
    verify_state = verify_state.new_state_with_round_increased();
    assert!(!verify_state.is_final_round());
}