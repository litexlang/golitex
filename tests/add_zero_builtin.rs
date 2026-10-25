use litex::ast::fact::{AtomicFact, Fact};
use litex::ast::stmt::Stmt;
use litex::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use litex::json_output::{project_run_detailed, project_stmt_normal};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::{CodeSource, Runtime};
use litex::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn add_zero_builtin_verifies_the_plane_identity_without_coordinate_seeds() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../examples/proof_nodes/equal/by_builtin_rule/add_zero_from_equalities.lit"
        ))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = project_run_detailed(&run, &rt, "eval", None).stringify();
    assert!(json.contains("AddZeroLeftFromEqualities"), "{json}");
    assert!(json.contains("AddZeroRightFromEqualities"), "{json}");
    assert!(json.contains("remaining_equal") && json.contains("zero_equal"));
    assert!(json.contains("TupleProjection"), "{json}");
}

#[test]
fn add_zero_builtin_keeps_both_premises_and_the_equality_orientation() {
    for (goal, rule, reversed) in [
        ("(0,0)(1)+x(1)=x(1)", "AddZeroLeftFromEqualities", false),
        ("x(1)+(0,0)(2)=x(1)", "AddZeroRightFromEqualities", false),
        ("x(1)=(0,0)(1)+x(1)", "AddZeroLeftFromEqualities", true),
        ("x(1)=x(1)+(0,0)(2)", "AddZeroRightFromEqualities", true),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code("have x R × R").unwrap().success);
        let run = rt.run_litex_code(goal).unwrap();
        assert!(run.success && run.session_error.is_none(), "{goal}");
        let json = project_run_detailed(&run, &rt, "eval", None).stringify();
        assert!(json.contains(rule), "{goal}: {json}");
        assert!(json.contains("remaining_equal") && json.contains("zero_equal"));
        assert!(json.contains("TupleProjection"), "{json}");
        assert!(json.contains(&format!("\"reversed\":{reversed}")), "{json}");
        let normal = project_stmt_normal(&run.statement_results[0], &rt).stringify();
        assert!(normal.contains(rule), "{normal}");
    }

    for goal in ["(0,0)(1)+x(1)=y", "y=x(1)+(0,0)(2)"] {
        let mut rt = runtime();
        assert!(
            rt.run_litex_code("have x R × R\nhave y R=x(1)")
                .unwrap()
                .success
        );
        let run = rt.run_litex_code(goal).unwrap();
        assert!(run.success && run.session_error.is_none(), "{goal}");
        let json = project_run_detailed(&run, &rt, "eval", None).stringify();
        assert!(
            json.contains("FromEqualities") && json.contains("remaining_equal"),
            "{json}"
        );
        assert!(json.contains("cite_fact_id"), "{json}");
    }
}

#[test]
fn add_zero_builtin_uses_the_existing_premise_ceiling() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have x R × R").unwrap().success);
    let blocks = Tokenizer::new()
        .tokenize("(0,0)(1)+x(1)=x(1)", CodeSource::Eval)
        .unwrap();
    let mut statements = rt.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = statements.remove(0) else {
        panic!("equality target");
    };
    assert!(rt
        .verify_equal_fact(
            &fact,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
        )
        .unwrap()
        .is_failed());
    assert!(!rt
        .verify_equal_fact(&fact, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    // Verification alone must not publish the tested result.
    assert!(rt
        .verify_equal_fact(
            &fact,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
        )
        .unwrap()
        .is_failed());
}

#[test]
fn add_zero_builtin_rejects_bad_premises_and_domains_without_publishing() {
    let mut rt = runtime();
    assert!(rt.run_litex_code(
        "have x R × R\nhave a,y R\nhave fn guarded(t R: t>0) R=t\nhave fn plane_add(u,v R × R) R × R=(u(1)+v(1),u(2)+v(2))"
    ).unwrap().success);
    for goal in [
        "a+x(1)=x(1)",
        "(1,0)(1)+x(1)=x(1)",
        "x(1)+(1,0)(1)=x(1)",
        "(0,0)(1)+x(1)=y",
        "(0,0)(1)+x(1)=x(1)+1",
        "((0,0)(1)+x(1),(1,0)(1)+x(2))=(x(1),x(2))",
        "plane_add((1,0),x)=x",
        "(0,0)(0)+x(1)=x(1)",
        "(0,0)(3)+x(1)=x(1)",
        "(0,0)(1/2)+x(1)=x(1)",
        "(0,0)(1)+x(1)/0=x(1)/0",
        "(0,0)(1)+guarded(a)=guarded(a)",
    ] {
        for _ in 0..2 {
            let run = rt.run_litex_code(goal).unwrap();
            assert!(!run.success && run.session_error.is_none(), "{goal}");
            assert_eq!(rt.execution_environments_stack.len(), 1);
        }
        assert!(rt.run_litex_code("(0,0)(2)+x(2)=x(2)").unwrap().success);
    }
}

#[test]
fn add_zero_builtin_respects_binder_scope_and_complex_addition() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("forall a,b R:\n    a=0\n    =>:\n        a+b=b\nhave a,b R")
            .unwrap()
            .success
    );
    let run = rt.run_litex_code("a+b=b").unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert!(rt.run_litex_code("have z C\n(0,0)(1)+z=z").unwrap().success);
}

#[test]
fn add_zero_builtin_lean_replays_the_recorded_equalities() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have a R=0\nhave b R\na+b=b").unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = project_run_detailed(&run, &rt, "eval", None).stringify();
    assert!(json.contains("AddZeroLeftFromEqualities"), "{json}");
    let lean = litex::compile_to_lean::compile_run(&run, rt, "AddZeroFromEqualities").unwrap();
    assert!(lean.contains("Litex.zeroAdd"), "{lean}");
}

#[test]
fn add_zero_literal_coordinate_carriers_need_no_strategy_or_storage() {
    let mut rt = runtime();
    for source in ["(0,0)(1) $in C", "(0,3/2)(2) $in Q", "(i,0)(1) $in C"] {
        let blocks = Tokenizer::new().tokenize(source, CodeSource::Eval).unwrap();
        let mut statements = rt.parse(&blocks).unwrap();
        let Stmt::Fact(fact) = statements.remove(0) else {
            panic!("membership");
        };
        assert!(
            !rt.verify_fact(
                &fact,
                VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
            )
            .unwrap()
            .is_failed(),
            "{source}"
        );
        assert!(
            rt.verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
                .unwrap()
                .is_failed(),
            "verification alone must not publish {source}"
        );
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}");
        let json = project_run_detailed(&run, &rt, "eval", None).stringify();
        assert!(
            json.contains("LiteralTupleNumericCoordinate") && json.contains("component_membership"),
            "{json}"
        );
    }
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!(
        "../examples/proof_nodes/atomic/by_known_special_property/literal_tuple_numeric_coordinate.lit"
    )).unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = project_run_detailed(&run, &rt, "eval", None).stringify();
    assert!(
        json.contains("tuple_equal") && json.contains("cite_fact_id"),
        "{json}"
    );
    for source in [
        "(i,0)(1) $in R",
        "(0,3/2)(2) $in Z",
        "(0,0)(1) $in R+",
        "(0,0)(0) $in C",
        "(0,0)(3) $in C",
        "(0,0)(1/2) $in C",
        "(0,1/0)(1) $in C",
        "(0,{0})(2) $in C",
    ] {
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{source}");
        assert!(rt.run_litex_code("(0,0)(2) $in C").unwrap().success);
    }
}
