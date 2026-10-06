use crate::ast::fact::Fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchedProof,
    VerifyAtomicExceptEqualityFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualFactSearchedProof, EqualitySearchProofByBuiltinRule, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::{
    verify_trig_interval_bound::TrigIntervalBoundSide,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language,
    })
}

#[test]
fn actual_inverse_children_keep_written_bounds_and_citations_in_ten_languages() {
    for language in OutputLanguage::ALL {
        for lower in ["(-pi)/2", "-(pi/2)", "0-pi/2", "(-1)*(pi/2)"] {
            let code = format!(
                "forall y R:\n    {lower}<=y\n    y<=pi/2\n    =>:\n        arcsin(sin(y))=y\n"
            );
            let mut rt = runtime(language);
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.success && run.session_error.is_none(), "{code}");
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &run.statement_results[0]
            else {
                panic!("fact");
            };
            let VerifyFactResult::ForallFact(f) = &stmt.verify_result else {
                panic!("forall");
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) =
                f.as_ref()
            else {
                panic!("local introduction");
            };
            let VerifyFactResult::Equality(eq) = &f.proved_then_facts[0].verify_result else {
                panic!("equality");
            };
            let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
                panic!("success");
            };
            let EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(p),
            ) = &eq.searched_proof
            else {
                panic!("right inverse");
            };
            assert_eq!(p.proof_of_requirement_facts.len(), 2);
            for child in &p.proof_of_requirement_facts {
                let VerifyFactResult::AtomicExceptEquality(child) = child else {
                    panic!("bound");
                };
                let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_ref() else {
                    panic!("checked bound");
                };
                assert!(matches!(
                    child.searched_proof,
                    AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
                ));
            }
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(detail.contains("ArcsinSinRightInverse"));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}

#[test]
fn inverse_sine_order_and_partial_tangent_wd_share_only_fixed_bound_spellings() {
    for lower in ["(-pi)/2", "-(pi/2)", "0-pi/2", "(-1)*(pi/2)"] {
        for code in [
            format!("forall x R:\n    x>{lower}\n    pi/2>x\n    =>:\n        cos(x)!=0\n"),
            format!("forall a,b R:\n    a>={lower}\n    pi/2>=b\n    a<b\n    =>:\n        sin(a)<sin(b)\n"),
            format!("forall y R:\n    y>{lower}\n    pi/2>y\n    =>:\n        arctan(tan(y))=y\n"),
            format!("forall y R:\n    y>={lower}\n    pi/2>=y\n    =>:\n        arcsin(sin(y))=y\n"),
        ] {
            let run = runtime(OutputLanguage::English).run_litex_code(&code).unwrap();
            assert!(run.success && run.session_error.is_none(), "{code}");
        }
    }
}

#[test]
fn false_intervals_strictness_poles_missing_guards_and_free_angles_still_reject() {
    for code in [
        "forall y R:\n    -pi<=y\n    y<=pi\n    =>:\n        arcsin(sin(y))=y\n",
        "forall y R:\n    y<=-(pi/2)\n    y<=pi/2\n    =>:\n        arcsin(sin(y))=y\n",
        "forall y R:\n    -(pi/2)<=y\n    =>:\n        arcsin(sin(y))=y\n",
        "forall y R:\n    -(pi/2)<=y\n    y<=pi/2\n    =>:\n        cos(y)!=0\n",
        "forall y R:\n    -(pi/2)<=y\n    y<=pi/2\n    =>:\n        arctan(tan(y))=y\n",
        "forall a,b R:\n    -(pi/2)<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<sin(b)\n",
        "forall a,b R:\n    -(pi/2)<=a\n    b<=pi/2\n    a<b\n    =>:\n        sin(b)<sin(a)\n",
        "forall a,b R:\n    -(pi/2)<=a\n    a<=pi/2\n    =>:\n        arcsin(sin(b))=b\n",
        "cos(pi/2)!=0\n",
    ] {
        let run = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}

#[test]
fn fixed_bound_lookup_preserves_direct_ceiling_and_does_not_publish() {
    let mut rt = runtime(OutputLanguage::English);
    let prefix = "witness exist t R st {-(pi/2)<=t,t<=pi/2} from arcsin(0)\nobtain y from exist t R st {-(pi/2)<=t,t<=pi/2}\n";
    let run = rt.run_litex_code(prefix).unwrap();
    assert!(run.success && run.session_error.is_none());
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("(-pi)/2<=y", crate::runtime::RealOrVirtualPath::Eval)
        .unwrap();
    let mut parsed = rt.parse(&blocks).unwrap();
    let canonical: Fact = match parsed.remove(0) {
        crate::ast::stmt::Stmt::Fact(fact) => fact,
        _ => panic!("canonical bound"),
    };
    let direct = VerifyState::new(VerifyStateLevel::Direct);
    assert!(rt.verify_fact(&canonical, direct).unwrap().is_failed());
    let proof = rt
        .verify_trig_interval_bound(&canonical, TrigIntervalBoundSide::Lower, direct)
        .unwrap()
        .expect("same-ceiling written bound");
    let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
        panic!("bound");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("checked bound");
    };
    assert!(proof.fact.readable_string().contains("-(pi / 2)"));
    assert!(matches!(
        proof.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
    ));
    assert!(rt.verify_fact(&canonical, direct).unwrap().is_failed());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn persistent_consumers_and_success_failure_source_reuse_remain_checkable() {
    for source in [
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/arcsin_principal_bound_spellings.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/cos_nonzero_principal_bound_spellings.lit"),
    ] {
        assert!(!source.contains("trust"));
        assert!(runtime(OutputLanguage::English).run_litex_code(source).unwrap().success);
    }
    let good = "forall y R:\n    -(pi/2)<=y\n    y<=pi/2\n    =>:\n        arcsin(sin(y))=y\n";
    let bad = good.replace("=y", "=y+1");
    let mut rt = runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert!(rt.run_litex_code(good).unwrap().success);
    let run = rt.run_litex_code(good).unwrap();
    assert!(run.success);
    assert!(
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
            .stringify()
            .contains("by_known_forall_fact")
    );
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
