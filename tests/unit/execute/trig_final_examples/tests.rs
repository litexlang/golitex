use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{AtomicExceptEqualityFactSearchProofByBuiltinRule, less::LessFactSearchProofByBuiltinRule, not_equal::NotEqualFactSearchProofByBuiltinRule};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{EqualFactSearchedProof, EqualitySearchProofByBuiltinRule, VerifyEqualityResult};
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: true, strict: true, language })
}

#[test]
fn nonzero_two_edge_interval_bounds_keep_actual_three_source_ids() {
    for language in OutputLanguage::ALL {
        for (function, lower, upper) in [("cos", "-pi/2", "pi/2"), ("sin", "0", "pi")] {
            let code = format!("forall a,b R:\n    {lower}<a\n    b<{upper}\n    a<=b\n    =>:\n        {function}(a)!=0\n        {function}(b)!=0\n");
            let mut rt = runtime(language);
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.success && run.session_error.is_none(), "{code}");
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &run.statement_results[0] else { panic!("fact"); };
            let VerifyFactResult::ForallFact(f) = &stmt.verify_result else { panic!("forall"); };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) = f.as_ref() else { panic!("local introduction"); };
            let ids: Vec<_> = f.assumed_dom_facts.iter().map(|x| x.store_and_infer.primary_fact_id()).collect();
            for (index, then) in f.proved_then_facts.iter().enumerate() {
                let VerifyFactResult::AtomicExceptEquality(a) = &then.verify_result else { panic!("nonzero"); };
                let VerifyAtomicExceptEqualityFactResult::Success(a) = a.as_ref() else { panic!("success"); };
                let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(rule)) = &a.searched_proof else { panic!("nonzero leaf"); };
                let (lo, hi) = match rule {
                    NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnOpenHalfPi(p) => (&p.lower_bound_proof, &p.upper_bound_proof),
                    NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnOpenPi(p) => (&p.lower_bound_proof, &p.upper_bound_proof),
                    _ => panic!("principal nonzero leaf"),
                };
                let (direct, chain, expected) = if index == 0 { (lo, hi, [ids[2], ids[1]]) } else { (hi, lo, [ids[0], ids[2]]) };
                assert_eq!(direct.cite_fact_id(), Some(if index == 0 { ids[0] } else { ids[1] }));
                let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::LessTransitivity(p))) = chain.searched_proof.as_ref() else { panic!("actual two-edge proof"); };
                assert_eq!([p.left_to_mid_cite_fact_id, p.mid_to_right_cite_fact_id], expected);
                assert!(p.left_to_mid_strict || p.mid_to_right_strict);
            }
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
            assert!(detail.contains("LessTransitivity"));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}

#[test]
fn inverse_consumes_actual_stronger_bound_and_both_source_ids() {
    let code = "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        arctan(tan(x))=x\n";
    let mut rt = runtime(OutputLanguage::English);
    let run = rt.run_litex_code(code).unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &run.statement_results[0] else { panic!("fact"); };
    let VerifyFactResult::ForallFact(f) = &stmt.verify_result else { panic!("forall"); };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) = f.as_ref() else { panic!("forall proof"); };
    let VerifyFactResult::Equality(e) = &f.proved_then_facts[0].verify_result else { panic!("equality"); };
    let VerifyEqualityResult::Success(e) = e.as_ref() else { panic!("success"); };
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(p)) = &e.searched_proof else { panic!("inverse leaf"); };
    assert_eq!(p.proof_of_requirement_facts.len(), 2);
    for (i, child) in p.proof_of_requirement_facts.iter().enumerate() {
        let VerifyFactResult::AtomicExceptEquality(a) = child else { panic!("actual bound"); };
        let VerifyAtomicExceptEqualityFactResult::Success(a) = a.as_ref() else { panic!("bound success"); };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &a.searched_proof else { panic!("actual given"); };
        assert_eq!(p.cite_fact_id, f.assumed_dom_facts[i].store_and_infer.primary_fact_id());
        if i == 0 { assert_eq!(a.fact.readable_string(), "0 < x"); }
    }
    crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
}

#[test]
fn fixed_fraction_difference_passes_and_wrong_domains_shapes_still_reject() {
    let prefix = "forall a,b,c,d R:\n    b!=0\n    d!=0\n    =>:\n        ";
    for equality in ["a/b-c/d=(a*d-c*b)/(b*d)", "(d*a-b*c)/(d*b)=a/b-c/d"] {
        assert!(runtime(OutputLanguage::English).run_litex_code(&format!("{prefix}{equality}\n")).unwrap().success);
    }
    for code in [
        "forall a,b,c,d R:\n    b!=0\n    d!=0\n    =>:\n        a/b-c/d=(a*d+c*b)/(b*d)\n",
        "forall a,b,c,d R:\n    b!=0\n    d!=0\n    =>:\n        a/b-c/d=(a*b-c*d)/(b*d)\n",
        "forall a,b,c,d R:\n    b!=0\n    d!=0\n    =>:\n        a/b-c/d=(a*d-c*b)/(b+d)\n",
        "forall a,b,c,d R:\n    b!=0\n    =>:\n        a/b-c/d=(a*d-c*b)/(b*d)\n",
        "1/0-1/2=(1*2-1*0)/(0*2)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<pi/2\n    a<=b\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<=pi/2\n    a<=b\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    0<=a\n    b<pi\n    a<=b\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<=pi\n    a<=b\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    =>:\n        tan(a)<tan(b)\n",
        "forall x R:\n    0<x\n    x<pi\n    =>:\n        arctan(tan(x))=x\n",
    ] {
        let run = runtime(OutputLanguage::English).run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}

#[test]
fn changed_interval_keeps_direct_ceiling_and_failed_scope_reuse() {
    let code = "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    =>:\n        tan(a)<tan(b)\n";
    let bad = code.replace("tan(a)<tan(b)", "tan(b)<tan(a)");
    let mut rt = runtime(OutputLanguage::English);
    let tokens = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact"); };
    let before = rt.execution_environments_stack[0].facts.facts_by_id.len();
    assert!(rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct)).unwrap().is_failed());
    assert!(!rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed());
    assert_eq!(rt.execution_environments_stack[0].facts.facts_by_id.len(), before);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert!(rt.run_litex_code(code).unwrap().success);
    let reused = rt.run_litex_code(code).unwrap();
    assert!(reused.success);
    let detail = crate::json_output::project_stmt_detailed(&reused.statement_results[0], &rt).stringify();
    assert!(detail.contains("by_known_forall_fact"));
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn maintained_wd_inverse_and_explicit_author_tracers_execute() {
    for source in [
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/trig_interval_partial_wd.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/arctan_first_quadrant_composition.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/trig_interval_quotient_authors.lit"),
    ] {
        assert!(!source.contains("trust"));
        let run = runtime(OutputLanguage::English).run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none());
    }
}
