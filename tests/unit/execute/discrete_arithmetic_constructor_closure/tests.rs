use super::*;
use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::launch_command::{LaunchCommand, OutputLanguage};
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
fn discrete_constructor_tracer_checks_recursive_domains_and_codomain() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/atomic/by_builtin_rule/discrete_arithmetic_constructor_closure.lit"
    ));
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success, "maintained recursion tracer");
}

#[test]
fn discrete_constructor_truth_retains_stage_citation_and_no_temporary_store() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have f fn(t N) N\nhave n N\n")
            .unwrap()
            .success
    );
    let tokens = Tokenizer::new()
        .tokenize("f(n) + f(n) * 2 $in N", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact");
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
    ] {
        assert!(rt
            .verify_fact(&goal, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    let Fact::AtomicFact(atomic) = &goal else {
        panic!("atomic");
    };
    assert!(rt.lookup_known_atomic_fact(atomic).is_none());
    let result = rt.exec_stmt(&Stmt::Fact(goal)).unwrap();
    assert!(!result.is_failed());
    let json = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
    for text in [
        "DiscreteArithmeticConstructorClosure",
        "constructor_tree",
        "FnApplicationInCodomain",
        "cite_property_fact_id",
    ] {
        assert!(json.contains(text), "{text}: {json}");
    }
}

#[test]
fn discrete_constructor_rejects_natural_subtraction_wrong_carriers_and_domains() {
    for code in [
        "have fn f(t N) N = t\nf(0) - 1 $in N\n",
        "have fn f(t N) N = t\n-f(1) $in N\n",
        "have fn f(t R) R = t\nforall n R:\n    f(n) + 1 $in N\n",
        "have fn f(t C) C = t\nforall n C:\n    f(n) + 1 $in Z\n",
        "have fn partial(t Z: t > 0) Z = t\npartial(0) - 1 $in Z\n",
        "have fn f(t N) N = t\nf(1) / 2 $in Z\n",
        "have fn f(t N) N = t\nf(1) / 0 $in Z\n",
        "have fn bad(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: bad(n) + 1\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "{code}");
    }
}
