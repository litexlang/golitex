use super::*;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English })
}

#[test]
fn nonnegative_sum_retains_builtin_ceiling_and_premise_evidence() {
    // Fresh declarations provide a checked assumption, rather than trusting it.
    let mut rt = runtime();
    assert!(rt.run_litex_code("have n Z = 0\nn >= 0\n").unwrap().success);
    let tokens = Tokenizer::new().tokenize("n + 1 + 1 >= 0", rt.current_file.clone()).unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact"); };
    for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty] {
        assert!(rt.verify_fact(&goal, VerifyState::new(level)).unwrap().is_failed());
    }
    assert!(!rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed());
    let result = rt.exec_stmt(&Stmt::Fact(goal)).unwrap();
    assert!(!result.is_failed());
    let json = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
    for text in ["SumOfNonnegatives", "constructor_tree", "cite_fact_id"] {
        assert!(json.contains(text), "{text}: {json}");
    }
}

#[test]
fn nonnegative_sum_domain_tracer_and_negative_boundaries() {
    let code = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/atomic/by_builtin_rule/nonnegative_sum_domain.lit"));
    assert!(runtime().run_litex_code(code).unwrap().success);
    for code in [
        "forall n Z:\n    n >= 0\n    =>:\n        n + (-1) >= 0\n",
        "have fn f(t Z: t >= 0) N = t\nf(-1) <= f(-1)\n",
        "forall n C:\n    n + 1 >= 0\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "{code}");
    }
}
