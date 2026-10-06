use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{AtomicExceptEqualityFactSearchProofByBuiltinRule, less::LessFactSearchProofByBuiltinRule, less_equal::LessEqualFactSearchProofByBuiltinRule};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecStmtResult, ExecFactStmtResult};
use crate::launch_command::{LaunchCommand,OutputLanguage};
use crate::runtime::Runtime;
use crate::ast::stmt::Stmt;
use crate::tokenize::Tokenizer;
fn runtime(lang: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: lang,
    })
}
fn premise(
    p: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> (&AtomicExceptEqualityFactKnownProof, &'static str) {
    match p {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::LessFromPosDifference(p),
        ) => (&p.premise_proof, "LessFromPosDifference"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::PosDifferenceFromLess(p),
        ) => (&p.premise_proof, "PosDifferenceFromLess"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::LessFromNegativeDifference(p),
        ) => (&p.premise_proof, "LessFromNegativeDifference"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::NegativeDifferenceFromLess(p),
        ) => (&p.premise_proof, "NegativeDifferenceFromLess"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonnegDifference(p),
        ) => (&p.premise_proof, "LessEqualFromNonnegDifference"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::NonnegDifferenceFromLessEqual(p),
        ) => (&p.premise_proof, "NonnegDifferenceFromLessEqual"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonpositiveDifference(p),
        ) => (&p.premise_proof, "LessEqualFromNonpositiveDifference"),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::NonpositiveDifferenceFromLessEqual(p),
        ) => (&p.premise_proof, "NonpositiveDifferenceFromLessEqual"),
        _ => panic!("difference leaf"),
    }
}
#[test]
fn eight_real_leaves_keep_selected_comparison_source_and_ten_languages() {
    for lang in OutputLanguage::ALL {
        for (condition, goal, name) in [
            ("b-a>0", "a<b", "LessFromPosDifference"),
            ("a>b", "0<a-b", "PosDifferenceFromLess"),
            ("0>a-b", "a<b", "LessFromNegativeDifference"),
            ("b>a", "a-b<0", "NegativeDifferenceFromLess"),
            ("b-a>0", "a<=b", "LessEqualFromNonnegDifference"),
            ("a>b", "0<=a-b", "NonnegDifferenceFromLessEqual"),
            ("0>a-b", "a<=b", "LessEqualFromNonpositiveDifference"),
            ("b>a", "a-b<=0", "NonpositiveDifferenceFromLessEqual"),
        ] {
            let code = format!("forall a,b R:\n    {condition}\n    =>:\n        {goal}\n");
            let mut rt = runtime(lang);
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.success && run.session_error.is_none(), "{code}");
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &run.statement_results[0]
            else {
                panic!("fact")
            };
            let VerifyFactResult::ForallFact(f) = &s.verify_result else {
                panic!("forall")
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) =
                f.as_ref()
            else {
                panic!("local")
            };
            let VerifyFactResult::AtomicExceptEquality(a) = &f.proved_then_facts[0].verify_result
            else {
                panic!("atomic")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(a) = a.as_ref() else {
                panic!("success")
            };
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &a.searched_proof
            else {
                panic!("builtin")
            };
            let (p, actual) = premise(rule);
            assert_eq!(actual, name);
            let id = f.assumed_dom_facts[0].store_and_infer.primary_fact_id();
            assert_eq!(p.cite_fact_id(), Some(id));
            let source = f.local_env.facts.facts_by_id.get(&id).unwrap();
            assert_eq!(p.fact.readable_string(), source.readable_string());
            let text = rule.rule_name_and_message(lang);
            assert!(!text.rule_name.is_empty() && !text.message.is_empty());
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                .stringify();
            assert!(detail.contains(name) && detail.contains("premise_proof"));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}
#[test]
fn difference_orientations_and_negative_spellings_verify() {
    for code in [
        "forall a,b R:\n    b-a>0\n    =>:\n        a<b\n",
        "forall a,b R:\n    0<b-a\n    =>:\n        a<b\n",
        "forall a,b R:\n    a-b<0\n    =>:\n        a<b\n",
        "forall a,b R:\n    0>a-b\n    =>:\n        a<b\n",
        "forall a,b R:\n    a-b>0\n    =>:\n        a>b\n",
        "forall a,b R:\n    0<a-b\n    =>:\n        a>b\n",
        "forall a,b R:\n    b-a<0\n    =>:\n        a>b\n",
        "forall a,b R:\n    0>b-a\n    =>:\n        a>b\n",
        "forall a,b R:\n    b-a>=0\n    =>:\n        a<=b\n",
        "forall a,b R:\n    0<=b-a\n    =>:\n        a<=b\n",
        "forall a,b R:\n    b-a>0\n    =>:\n        a<=b\n",
        "forall a,b R:\n    0<b-a\n    =>:\n        a<=b\n",
        "forall a,b R:\n    a-b<=0\n    =>:\n        a<=b\n",
        "forall a,b R:\n    0>=a-b\n    =>:\n        a<=b\n",
        "forall a,b R:\n    a-b<0\n    =>:\n        a<=b\n",
        "forall a,b R:\n    0>a-b\n    =>:\n        a<=b\n",
        "forall a,b R:\n    a-b>=0\n    =>:\n        a>=b\n",
        "forall a,b R:\n    0<=a-b\n    =>:\n        a>=b\n",
        "forall a,b R:\n    a-b>0\n    =>:\n        a>=b\n",
        "forall a,b R:\n    0<a-b\n    =>:\n        a>=b\n",
        "forall a,b R:\n    b-a<=0\n    =>:\n        a>=b\n",
        "forall a,b R:\n    0>=b-a\n    =>:\n        a>=b\n",
        "forall a,b R:\n    b-a<0\n    =>:\n        a>=b\n",
        "forall a,b R:\n    0>b-a\n    =>:\n        a>=b\n",
        "forall a,b R:\n    a<b\n    =>:\n        a-b<0\n",
        "forall a,b R:\n    b>a\n    =>:\n        a-b<0\n",
        "forall a,b R:\n    a<b\n    =>:\n        0>a-b\n",
        "forall a,b R:\n    b>a\n    =>:\n        0>a-b\n",
        "forall a,b R:\n    a>b\n    =>:\n        a-b>0\n",
        "forall a,b R:\n    b<a\n    =>:\n        a-b>0\n",
        "forall a,b R:\n    a>b\n    =>:\n        0<a-b\n",
        "forall a,b R:\n    b<a\n    =>:\n        0<a-b\n",
        "forall a,b R:\n    a<=b\n    =>:\n        a-b<=0\n",
        "forall a,b R:\n    b>=a\n    =>:\n        a-b<=0\n",
        "forall a,b R:\n    a<b\n    =>:\n        a-b<=0\n",
        "forall a,b R:\n    b>a\n    =>:\n        a-b<=0\n",
        "forall a,b R:\n    a<=b\n    =>:\n        0>=a-b\n",
        "forall a,b R:\n    b>=a\n    =>:\n        0>=a-b\n",
        "forall a,b R:\n    a<b\n    =>:\n        0>=a-b\n",
        "forall a,b R:\n    b>a\n    =>:\n        0>=a-b\n",
        "forall a,b R:\n    a>=b\n    =>:\n        a-b>=0\n",
        "forall a,b R:\n    b<=a\n    =>:\n        a-b>=0\n",
        "forall a,b R:\n    a>b\n    =>:\n        a-b>=0\n",
        "forall a,b R:\n    b<a\n    =>:\n        a-b>=0\n",
        "forall a,b R:\n    a>=b\n    =>:\n        0<=a-b\n",
        "forall a,b R:\n    b<=a\n    =>:\n        0<=a-b\n",
        "forall a,b R:\n    a>b\n    =>:\n        0<=a-b\n",
        "forall a,b R:\n    b<a\n    =>:\n        0<=a-b\n",
        "forall u R:\n    -u>0\n    =>:\n        u<0\n",
        "forall u R:\n    0<-u\n    =>:\n        u<0\n",
        "forall u R:\n    -u>=0\n    =>:\n        u<=0\n",
        "forall u R:\n    0<=-u\n    =>:\n        u<=0\n",
        "forall u R:\n    -u<0\n    =>:\n        u>0\n",
        "forall u R:\n    0>-u\n    =>:\n        u>0\n",
        "forall u R:\n    -u<=0\n    =>:\n        u>=0\n",
        "forall u R:\n    0>=-u\n    =>:\n        u>=0\n",
        "forall u R:\n    0-u>0\n    =>:\n        u<0\n",
        "forall u R:\n    0<0-u\n    =>:\n        u<0\n",
        "forall u R:\n    0-u>=0\n    =>:\n        u<=0\n",
        "forall u R:\n    0<=0-u\n    =>:\n        u<=0\n",
        "forall u R:\n    0-u<0\n    =>:\n        u>0\n",
        "forall u R:\n    0>0-u\n    =>:\n        u>0\n",
        "forall u R:\n    0-u<=0\n    =>:\n        u>=0\n",
        "forall u R:\n    0>=0-u\n    =>:\n        u>=0\n",
        "forall u R:\n    (-1)*u>0\n    =>:\n        u<0\n",
        "forall u R:\n    0<(-1)*u\n    =>:\n        u<0\n",
        "forall u R:\n    (-1)*u>=0\n    =>:\n        u<=0\n",
        "forall u R:\n    0<=(-1)*u\n    =>:\n        u<=0\n",
        "forall u R:\n    (-1)*u<0\n    =>:\n        u>0\n",
        "forall u R:\n    0>(-1)*u\n    =>:\n        u>0\n",
        "forall u R:\n    (-1)*u<=0\n    =>:\n        u>=0\n",
        "forall u R:\n    0>=(-1)*u\n    =>:\n        u>=0\n",
        "forall u R:\n    u*(-1)>0\n    =>:\n        u<0\n",
        "forall u R:\n    0<u*(-1)\n    =>:\n        u<0\n",
        "forall u R:\n    u*(-1)>=0\n    =>:\n        u<=0\n",
        "forall u R:\n    0<=u*(-1)\n    =>:\n        u<=0\n",
        "forall u R:\n    u*(-1)<0\n    =>:\n        u>0\n",
        "forall u R:\n    0>u*(-1)\n    =>:\n        u>0\n",
        "forall u R:\n    u*(-1)<=0\n    =>:\n        u>=0\n",
        "forall u R:\n    0>=u*(-1)\n    =>:\n        u>=0\n",
    ] {
        let r = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(r.success && r.session_error.is_none(), "{code}");
    }
}
#[test]
fn weak_wrong_direction_argument_and_domain_controls_reject() {
    for code in [
        "forall a,b R:\n    a-b<0\n    =>:\n        a>b\n",
        "forall a,b R:\n    a-b<=0\n    =>:\n        a<b\n",
        "forall a,b R:\n    a<b\n    =>:\n        0<a-b\n",
        "forall a,b R:\n    a<=b\n    =>:\n        a-b<0\n",
        "forall u R:\n    -u>=0\n    =>:\n        u<0\n",
        "forall u R:\n    -u>0\n    =>:\n        u>0\n",
        "forall u R:\n    0-u>=0\n    =>:\n        u<0\n",
        "forall u R:\n    0-u>0\n    =>:\n        u>0\n",
        "forall u R:\n    (-1)*u>=0\n    =>:\n        u<0\n",
        "forall u R:\n    (-1)*u>0\n    =>:\n        u>0\n",
        "forall u R:\n    u*(-1)>=0\n    =>:\n        u<0\n",
        "forall u R:\n    u*(-1)>0\n    =>:\n        u>0\n",
        "forall a,b R:\n    a-b<=0\n    =>:\n        a<b\n",
        "forall a,b,c R:\n    a-b<0\n    =>:\n        a<c\n",
        "forall a,b C:\n    =>:\n        a-b<0\n",
        "forall u R:\n    -u>=0\n    =>:\n        u<0\n",
    ] {
        let r = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(!r.success && r.session_error.is_none(), "{code}");
    }
}
#[test]
fn maintained_acceptance_files_execute() {
    for code in [
        include_str!(
            "../../../../examples/proof_nodes/atomic/by_builtin_rule/signed_difference_order.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/atomic/by_builtin_rule/negated_sign_order.lit"
        ),
    ] {
        assert!(
            runtime(OutputLanguage::English)
                .run_litex_code(code)
                .unwrap()
                .success
        );
    }
}
#[test]
fn fixed_known_only_bridge_respects_direct_ceiling_and_scope_reuse() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code("have a R\nhave b R").unwrap().success);
    let tokens = Tokenizer::new()
        .tokenize("a<b", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    for level in [VerifyStateLevel::Direct, VerifyStateLevel::BuiltinRule] {
        assert!(rt
            .verify_fact(&goal, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(!rt.run_litex_code("a-b<0").unwrap().success);
    let good = "forall x,y R:\n    x-y<0\n    =>:\n        x<y\n";
    let bad = good.replace("        x<y", "        x>y");
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    let saved = rt.run_litex_code(good).unwrap();
    assert!(saved.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &saved.statement_results[0] else {
        panic!("saved")
    };
    let id = s.store_and_infer_result.primary_fact_id();
    let reuse = rt.run_litex_code(good).unwrap();
    assert!(reuse.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &reuse.statement_results[0] else {
        panic!("reuse")
    };
    let VerifyFactResult::ForallFact(f) = &s.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) = f.as_ref()
    else {
        panic!("known")
    };
    assert_eq!(p.cite_fact_id, id);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
}
