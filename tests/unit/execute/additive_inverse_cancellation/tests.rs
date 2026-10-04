use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict,
        language: OutputLanguage::English,
    })
}

fn fact(rt: &mut Runtime, text: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(text, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    fact
}

#[test]
fn maintained_additive_inverse_tracer_preserves_complex_domain_and_orientations() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_builtin_rule/additive_inverse_from_sum.lit"
    ));
    assert!(runtime(true).run_litex_code(code).unwrap().success);
}

#[test]
fn cancellation_requires_the_matching_zero_sum() {
    for code in [
        "forall a, b C:\n    a + b = 1\n    =>:\n        a = -b\n",
        "forall a, b C:\n    a + b = 0\n    =>:\n        a = b\n",
        "forall a, b, c C:\n    a + b = 0\n    =>:\n        a = -c\n",
    ] {
        let run = runtime(true).run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}

#[test]
fn original_sum_citation_is_read_only_and_obeys_the_search_ceiling() {
    for (source, goal) in [("a + b = 0", "a = -b"), ("b + a = 0", "-b = a")] {
        // Unit assumptions only; the maintained tracer and textbook use no trust.
        let mut rt = runtime(false);
        assert!(
            rt.run_litex_code(&format!("have a, b C\ntrust {source}\n"))
                .unwrap()
                .success
        );
        let goal_fact = fact(&mut rt, goal);
        let sizes = |rt: &Runtime| {
            rt.execution_environments_stack
                .iter()
                .map(|e| {
                    (
                        e.facts.facts_by_id.len(),
                        e.well_defined_objects.object_to_wd_id.len(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = sizes(&rt);
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
            VerifyStateLevel::BuiltinRule,
        ] {
            let proof = rt.verify_fact(&goal_fact, VerifyState::new(level)).unwrap();
            assert_eq!(!proof.is_failed(), level == VerifyStateLevel::BuiltinRule);
            assert_eq!(before, sizes(&rt));
        }
        let run = rt.run_litex_code(goal).unwrap();
        assert!(run.success);
        let json =
            crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        for needle in ["SubtractionFromKnownAddition", "cite_fact_id", source] {
            assert!(json.contains(needle), "{json}");
        }
    }
}
