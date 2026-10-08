use crate::ast::fact::{ExistShapedFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::VerifyExistShapedFactWellDefinedResult;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn normal_atomic_expand_bounded_wd_constructor() {
    let mut runtime = runtime();
    let run = runtime
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/infer/atomic/normal_atomic_expand_bounded_wd.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn normal_atomic_expand_bounded_wd_does_not_accept_invalid_calls_or_false_facts() {
    let mut runtime = runtime();
    assert!(
        runtime
            .run_litex_code("have terms finite_seq(R, 1)")
            .unwrap()
            .success
    );
    for code in ["terms(0) = terms(0)", "0 = 1"] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert!(runtime.run_litex_code("terms(1) $in R").unwrap().success);
    }
}

#[test]
fn normal_atomic_expand_bounded_wd_keeps_parameter_projection() {
    let mut runtime = runtime();
    let run = runtime
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/infer/atomic/normal_atomic_param_types_renamed_carrier.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn normal_atomic_expand_bounded_wd_does_not_raise_the_caller_ceiling() {
    let mut runtime = runtime();
    assert!(runtime.run_litex_code("have x R").unwrap().success);
    let tokens = Tokenizer::new()
        .tokenize(
            "exist terms finite_seq(R, 1) st {terms(1) = x}",
            runtime.current_file.clone(),
        )
        .unwrap();
    let Stmt::Fact(Fact::ExistFact(fact)) = runtime.parse(&tokens).unwrap().remove(0) else {
        panic!("existential tracer");
    };
    let result = runtime
        .verify_exist_shaped_fact_well_definedness(
            &ExistShapedFact::Exist(fact),
            VerifyState::new(VerifyStateLevel::Direct),
        )
        .unwrap();
    assert!(matches!(
        result,
        VerifyExistShapedFactWellDefinedResult::Failed(_)
    ));
}
