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
fn maintained_tracer_retains_all_four_weak_order_orientations() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_builtin_rule/two_sided_weak_order_orientations.lit"
    ));
    assert!(runtime(true).run_litex_code(code).unwrap().success);
}

#[test]
fn two_citations_are_read_only_and_do_not_raise_the_search_ceiling() {
    for (left, right) in [
        ("a <= b", "b <= a"),
        ("a >= b", "b >= a"),
        ("a <= b", "a >= b"),
        ("b >= a", "b <= a"),
    ] {
        // Trusted rows are unit assumptions only; the tracer has no trust.
        let mut rt = runtime(false);
        assert!(
            rt.run_litex_code(&format!("have a, b R\ntrust {left}\ntrust {right}\n"))
                .unwrap()
                .success
        );
        let goal = fact(&mut rt, "a = b");
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
            let proof = rt.verify_fact(&goal, VerifyState::new(level)).unwrap();
            assert_eq!(!proof.is_failed(), level == VerifyStateLevel::BuiltinRule);
            assert_eq!(before, sizes(&rt));
        }
        let run = rt.run_litex_code("a = b").unwrap();
        assert!(run.success);
        let json =
            crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        for needle in [
            "EqualityFromTwoSidedWeakOrder",
            "left_le_right_proof",
            "right_le_left_proof",
            "cite_fact_id",
            left,
            right,
        ] {
            assert!(json.contains(needle), "{json}");
        }
    }
}

#[test]
fn one_direction_is_not_antisymmetry() {
    for code in [
        "forall a, b R:\n    a >= b\n    =>:\n        a = b\n",
        "forall a, b R:\n    a <= b\n    b >= a\n    =>:\n        a = b\n",
        "forall a, b R:\n    a <= b\n    =>:\n        a = b\n",
        "forall a, b C:\n    a >= b\n    b >= a\n    =>:\n        a = b\n",
    ] {
        let run = runtime(true).run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}
