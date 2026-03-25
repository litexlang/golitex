use crate::environment::Environment;
use crate::execute::Runtime;
use crate::fact::AtomicFact;
use crate::fact::EqualFact;
use crate::fact::Fact;
use crate::module_manager::ModuleManager;
use crate::obj::{Number, Obj};
use crate::parse::tokenize_line;
use crate::parse::TokenBlock;
use crate::result::NonErrStmtExecResult;
use crate::runtime::RuntimeContext;
use crate::stmt::Stmt;
use crate::verify::VerifyState;

#[test]
fn test_verify_atomic_fact() {
    let mut module_manager = ModuleManager::new_empty_module_manager("examples/tmp.lit");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);

    // verify 1 = 1
    let one = Obj::Number(Number::new("1".to_string()));
    let fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        one.clone(),
        one,
        crate::common::defaults::DEFAULT_LINE_FILE.clone(),
    )));
    let stmt = Stmt::Fact(fact);
    let result = runtime.exec_stmt(&stmt);

    match result {
        Ok(stmt_result) => {
            println!("{}", stmt_result.body_string());
        }
        Err(e) => {
            println!("ERROR\n{}\n{}", e.display_label(), e.display_label());
        }
    }
}

/// 从 string → parse → exec 整条链路测试：fact "1 + 1 = 2"
#[test]
fn test_exec_stmt_fact_one_plus_one_eq_two() {
    let mut module_manager = ModuleManager::new_empty_module_manager("examples/tmp.lit");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);
    let s = "1 + 1 = 2";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 1));
    let stmt = runtime
        .parse_stmt(&mut tb)
        .expect("parse fact \"1 + 1 = 2\" failed");
    assert!(matches!(stmt, Stmt::Fact(_)), "expected Stmt::Fact");

    let result = runtime.exec_stmt(&stmt).expect("exec.stmt(fact) failed");
    match &result {
        NonErrStmtExecResult::NonFactualStmtSuccess(_)
        | NonErrStmtExecResult::FactVerifiedByFact(_)
        | NonErrStmtExecResult::FactVerifiedByBuiltinRules(_) => {
            println!("{}", result.body_string())
        }
        NonErrStmtExecResult::StmtUnknown(u) => {
            panic!("fact 1+1=2 should be verified, got StmtUnknown: {}", u)
        }
    }
}

#[test]
fn test_verify_state() {
    let mut verify_state = VerifyState::new(0, false);
    assert!(!verify_state.is_final_round());
    verify_state = verify_state.new_state_with_round_increased();
    assert!(!verify_state.is_final_round());
}
