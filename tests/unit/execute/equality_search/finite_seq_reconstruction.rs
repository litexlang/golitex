use super::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;

#[test]
fn finite_seq_reconstruction_accepts_bodyless_claims() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_builtin_rule/finite_seq_reconstruction.lit"
    ));
    assert!(runtime().run_litex_code(source).unwrap().success);
}

#[test]
fn finite_seq_reconstruction_cites_membership_without_writes() {
    for goal in ["x=(x(1),x(2))", "(x(1),x(2))=x"] {
        let mut rt = runtime();
        exec_ok(&mut rt, "have x finite_seq(R,2)");
        let fact = equal(&mut rt, goal);
        assert!(!rt
            .verify_equal_fact_well_definedness(&fact, VerifyState::top_level())
            .unwrap()
            .is_failed());
        assert!(
            rt.search_equal_fact_proof(
                &fact,
                VerifyState::new(
                    crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty
                )
            )
            .unwrap()
            .is_none(),
            "builtin rule must respect the caller's ceiling"
        );
        let before = store_sizes(&rt);
        let proof = rt
            .search_equal_fact_builtin_rule(&fact, VerifyState::top_level())
            .unwrap()
            .unwrap();
        let EqualitySearchProofByBuiltinRule::FiniteSeqReconstruction(p) = proof else {
            panic!("wrong rule")
        };
        assert!(rt.fact_by_id_in_stack(p.membership.fact_id).is_some());
        assert_eq!(p.reversed, goal.starts_with('('));
        assert_eq!(before, store_sizes(&rt));
        let result = exec_ok(&mut rt, goal);
        let json = project_stmt_detailed(&result, &rt).stringify();
        assert!(json.contains("FiniteSeqReconstruction"), "{json}");
        assert!(json.contains(&p.membership.fact_id.to_string()), "{json}");
        let normal = project_stmt_normal(&result, &rt).stringify();
        assert!(normal.contains("FiniteSeqReconstruction"), "{normal}");
        assert!(normal.contains("x $in finite_seq(R, 2)"), "{normal}");
        let rule = EqualitySearchProofByBuiltinRule::FiniteSeqReconstruction(p);
        for language in [
            OutputLanguage::English,
            OutputLanguage::Chinese,
            OutputLanguage::ChineseTraditional,
            OutputLanguage::French,
            OutputLanguage::Russian,
            OutputLanguage::Spanish,
            OutputLanguage::Arabic,
            OutputLanguage::Japanese,
            OutputLanguage::Korean,
            OutputLanguage::Vietnamese,
        ] {
            let text = rule.rule_name_and_message(language);
            assert_eq!(text.rule_name, "FiniteSeqReconstruction");
            assert!(!text.message.is_empty());
        }
    }
}

#[test]
fn finite_seq_reconstruction_rejects_incomplete_or_wrong_coordinates() {
    for (setup, goal) in [
        ("have x finite_seq(R,3)", "x=(x(1),x(2))"),
        ("have x finite_seq(R,2)", "x=(x(2),x(1))"),
        ("have x finite_seq(R,2)", "x=(x(1),x(1))"),
        ("have x finite_seq(R,2)", "x=(x(1),x(2),x(1))"),
        ("have x,y finite_seq(R,2)", "x=(y(1),y(2))"),
        ("have x seq(R)", "x=(x(1),x(2))"),
        ("have x fn(k N+: k<=3) R", "x=(x(1),x(2))"),
        ("have x finite_seq(R,2)", "x=(x(0),x(2))"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        assert!(exec(&mut rt, goal).is_failed(), "{setup}: {goal}");
    }
}

#[test]
fn finite_seq_reconstruction_does_not_leak_claim_binders() {
    let mut rt = runtime();
    exec_ok(
        &mut rt,
        "claim:\n    ? forall x finite_seq(R,2):\n        x=(x(1),x(2))",
    );
    exec_ok(&mut rt, "have x seq(R)");
    assert!(exec(&mut rt, "x=(x(1),x(2))").is_failed());
    exec_ok(&mut rt, "have y finite_seq(R,2)");
    assert!(exec(&mut rt, "claim:\n    ? y=(y(2),y(1))").is_failed());
    exec_ok(&mut rt, "y=(y(1),y(2))");
}
