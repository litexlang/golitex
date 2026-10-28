use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    fact
}

// Trusted rows are unit-test assumptions only. The maintained tracer below
// proves the corresponding implications without trust.
fn with_bound(bound: &str) -> Runtime {
    let mut rt = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    assert!(
        rt.run_litex_code(&format!("have x R\ntrust {bound}\n"))
            .unwrap()
            .success
    );
    rt
}

#[test]
fn both_weak_goal_orientations_consume_all_stored_bound_orientations() {
    for (sources, targets) in [
        (
            ["x >= 2", "x > 2", "2 <= x", "2 < x"],
            ["x - 1 >= 0", "0 <= x - 1"],
        ),
        (
            ["x <= -2", "x < -2", "-2 >= x", "-2 > x"],
            ["x - 1 <= 0", "0 >= x - 1"],
        ),
    ] {
        for source in sources {
            for target in targets {
                let mut rt = with_bound(source);
                let goal = fact(&mut rt, target);
                let proof = rt
                    .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
                    .unwrap();
                assert!(!proof.is_failed(), "{source} => {target}");
                let run = rt.run_litex_code(target).unwrap();
                assert!(run.success);
                let json =
                    crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                        .stringify();
                assert!(json.contains("ClosedSubtractionBound"), "{json}");
            }
        }
    }
}

#[test]
fn exact_fraction_offset_equality_and_negative_offset_work() {
    for (source, target) in [
        ("x >= 2", "x - 2 >= 0"),
        ("x >= 2", "x - (1 / 3) >= 5 / 3"),
        ("x >= 2", "x - (-2) >= 4"),
        ("x <= 2", "x - (1 / 3) <= 5 / 3"),
    ] {
        let mut rt = with_bound(source);
        let goal = fact(&mut rt, target);
        assert!(
            !rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
                .unwrap()
                .is_failed(),
            "{source} => {target}"
        );
    }
}

#[test]
fn insufficient_opposite_unknown_and_nonreal_bounds_reject() {
    for (source, target) in [
        ("x >= 2", "x - 3 >= 0"),
        ("x >= 2", "x - 1 <= 0"),
        ("x <= 2", "x - 1 >= 0"),
        ("x <= 2", "x - 1 <= 0"),
        ("x > 2", "x - 3 >= 0"),
    ] {
        let mut rt = with_bound(source);
        let goal = fact(&mut rt, target);
        assert!(
            rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
                .unwrap()
                .is_failed(),
            "{source} incorrectly proves {target}"
        );
    }
    for code in [
        "forall x, c R:\n    x >= 2\n    =>:\n        x - c >= 0\n",
        "forall x C:\n    x - 1 >= 0\n",
        "forall x R:\n    x >= 2\n    =>:\n        x - (1 / 0) >= 0\n",
    ] {
        assert!(!runtime().run_litex_code(code).unwrap().success, "{code}");
    }
    // Bounded exact arithmetic overflows safely; it never wraps a threshold.
    let mut rt = with_bound("x >= 2");
    let goal = fact(
        &mut rt,
        "x - (-170141183460469231731687303715884105727) >= 2",
    );
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
}

#[test]
fn evidence_cites_source_and_search_preserves_memory_and_ceiling() {
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::BuiltinRule,
    ] {
        let mut rt = with_bound("x >= 2");
        let goal = fact(&mut rt, "x - 1 >= 0");
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
        let proof = rt.verify_fact(&goal, VerifyState::new(level)).unwrap();
        assert_eq!(!proof.is_failed(), level == VerifyStateLevel::BuiltinRule);
        assert_eq!(before, sizes(&rt));
        if !proof.is_failed() {
            let run = rt.run_litex_code("x - 1 >= 0").unwrap();
            assert!(run.success);
            let json = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            for needle in [
                "ClosedSubtractionBound",
                "cite_fact_id",
                "x >= 2",
                "\"translated_bound\":\"1\"",
                "\"target_bound\":\"0\"",
            ] {
                assert!(json.contains(needle), "{json}");
            }
        }
    }
}

#[test]
fn maintained_subtraction_bound_implications_pass() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/atomic/by_builtin_rule/closed_subtraction_bound.lit"
    ));
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn symbolic_endpoint_requires_identical_bound_and_correct_offset_sign() {
    for (source, target, expected) in [
        ("x <= b", "x - 1 <= b", true),
        ("b >= x", "b >= x - 1", true),
        ("x < b", "x - 0 <= b", true),
        ("x >= b", "x - (-1) >= b", true),
        ("b <= x", "b <= x - (-1)", true),
        ("x <= b", "x - (-1) <= b", false),
        ("x >= b", "x - 1 >= b", false),
        ("x <= b", "x - 1 <= c", false),
        ("x >= b", "x - 1 <= b", false),
        ("x <= b", "x - c <= b", false),
    ] {
        let mut rt = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: false,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(
            rt.run_litex_code(&format!("have x, b, c R\ntrust {source}\n"))
                .unwrap()
                .success
        );
        let goal = fact(&mut rt, target);
        let before: Vec<_> = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect();
        let result = rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap();
        let after: Vec<_> = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect();
        assert_eq!(before, after);
        assert_eq!(!result.is_failed(), expected, "{source} => {target}");
        if expected {
            let run = rt.run_litex_code(target).unwrap();
            let json = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(json.contains("ClosedSubtractionBound"), "{json}");
            assert!(json.contains("cite_fact_id") && json.contains("translated_bound"));
        }
    }
    assert!(
        !runtime()
            .run_litex_code("forall x, b R:\n    x - 1 <= b\n")
            .unwrap()
            .success
    );
    assert!(
        !runtime()
            .run_litex_code("forall x, b R:\n    x <= b\n    =>:\n        x - (1 / 0) <= b\n")
            .unwrap()
            .success
    );
}

#[test]
fn strict_subtraction_bound_preserves_source_strictness_and_direction() {
    for (source, target, expected) in [
        ("x <= b", "x - 1 < b", true),
        ("b >= x", "b > x - 1", true),
        ("x >= b", "x - (-1) > b", true),
        ("b <= x", "b < x - (-1)", true),
        ("x < b", "x - 0 < b", true),
        ("x > b", "x - 0 > b", true),
        ("x <= b", "x - 0 < b", false),
        ("x >= b", "x - 0 > b", false),
        ("x <= b", "x - (-1) < b", false),
        ("x >= b", "x - 1 > b", false),
        ("x <= b", "x - 1 < c", false),
        ("x <= 2", "x - 1 < 1", false),
        ("x < 2", "x - 1 < 1", true),
    ] {
        let mut rt = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: false,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(
            rt.run_litex_code(&format!("have x, b, c R\ntrust {source}\n"))
                .unwrap()
                .success
        );
        let goal = fact(&mut rt, target);
        let result = rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap();
        assert_eq!(!result.is_failed(), expected, "{source} => {target}");
        if expected {
            let run = rt.run_litex_code(target).unwrap();
            let json = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(json.contains("ClosedSubtractionStrictBound"), "{json}");
            assert!(json.contains("cite_fact_id") && json.contains("translated_bound"));
        }
    }
}

#[test]
fn symbolic_bound_output_and_compiler_boundaries_are_explicit() {
    for language in OutputLanguage::ALL {
        for source in [
            "forall x,b R:\n    x<=b\n    =>:\n        x-1<=b\n",
            "forall x,b R:\n    x<=b\n    =>:\n        x-1<b\n",
            "forall x,b R:\n    x>=b\n    =>:\n        x-(-1)>b\n",
        ] {
            let mut rt = Runtime::new_with_result_detail(
                LaunchCommand::Eval {
                    code: String::new(),
                    session: false,
                    strict: true,
                    language,
                },
                crate::result_detail::OutputDetail::Detailed,
            );
            let run = rt.run_litex_code(source).unwrap();
            assert!(run.success && run.session_error.is_none());
            let normal =
                crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify();
            assert!(!normal.contains("unsupported"));
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(detail.contains("ClosedSubtraction"));
            assert!(detail.contains("cite_fact_id") && detail.contains("translated_bound"));
            assert!(crate::compile_to_lean::compile_run(&run, rt, "symbolic_bound").is_err());
        }
    }
}
