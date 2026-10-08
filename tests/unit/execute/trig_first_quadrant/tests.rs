use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    AtomicExceptEqualityFactSearchProofByBuiltinRule, greater::GreaterFactSearchProofByBuiltinRule,
    less::LessFactSearchProofByBuiltinRule, not_equal::NotEqualFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::knowledge_base::JsonValue;
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

fn actual_bounds(
    rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> (
    &AtomicExceptEqualityFactKnownProof,
    &AtomicExceptEqualityFactKnownProof,
    &'static str,
) {
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "CosNonzeroOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "SinNonzeroOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::TanPositiveOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "TanPositiveOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CotPositiveOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "CotPositiveOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::TanGreaterZeroOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "TanGreaterZeroOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::CotGreaterZeroOnFirstQuadrant(p),
        ) => (
            &p.lower_bound_proof,
            &p.upper_bound_proof,
            "CotGreaterZeroOnFirstQuadrant",
        ),
        _ => panic!("dedicated first-quadrant evidence"),
    }
}

fn contains(value: &JsonValue, text: &str) -> bool {
    match value {
        JsonValue::String(s) => s == text,
        JsonValue::Object(fields) => fields
            .keys_in_order()
            .into_iter()
            .any(|k| contains(fields.get(&k).unwrap(), text)),
        JsonValue::Array(items) => items.iter().any(|v| contains(v, text)),
        _ => false,
    }
}

#[test]
fn six_actual_typed_leaves_keep_written_bounds_ids_and_ten_languages() {
    for language in OutputLanguage::ALL {
        for lower in ["0<x", "x>0"] {
            for upper in ["x<pi/2", "pi/2>x"] {
                for (goal, expected) in [
                    ("cos(x)!=0", "CosNonzeroOnFirstQuadrant"),
                    ("sin(x)!=0", "SinNonzeroOnFirstQuadrant"),
                    ("0<tan(x)", "TanPositiveOnFirstQuadrant"),
                    ("0<cot(x)", "CotPositiveOnFirstQuadrant"),
                    ("tan(x)>0", "TanGreaterZeroOnFirstQuadrant"),
                    ("cot(x)>0", "CotGreaterZeroOnFirstQuadrant"),
                ] {
                    let code =
                        format!("forall x R:\n    {lower}\n    {upper}\n    =>:\n        {goal}\n");
                    let mut rt = runtime(language);
                    let run = rt.run_litex_code(&code).unwrap();
                    assert!(run.success && run.session_error.is_none(), "{code}");
                    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) =
                        &run.statement_results[0]
                    else {
                        panic!("fact success");
                    };
                    let VerifyFactResult::ForallFact(f) = &stmt.verify_result else {
                        panic!("forall");
                    };
                    let VerifyForallFactResult::Success(
                        VerifyForallFactProof::ByLocalIntroduction(f),
                    ) = f.as_ref()
                    else {
                        panic!("local introduction");
                    };
                    let VerifyFactResult::AtomicExceptEquality(a) =
                        &f.proved_then_facts[0].verify_result
                    else {
                        panic!("atomic");
                    };
                    let VerifyAtomicExceptEqualityFactResult::Success(a) = a.as_ref() else {
                        panic!("atomic success");
                    };
                    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) =
                        &a.searched_proof
                    else {
                        panic!("native rule");
                    };
                    let (actual_lower, actual_upper, name) = actual_bounds(rule);
                    assert_eq!(name, expected);
                    assert_eq!(
                        actual_lower.cite_fact_id(),
                        Some(f.assumed_dom_facts[0].store_and_infer.primary_fact_id())
                    );
                    assert_eq!(
                        actual_upper.cite_fact_id(),
                        Some(f.assumed_dom_facts[1].store_and_infer.primary_fact_id())
                    );
                    assert_eq!(
                        actual_lower.fact.readable_string().contains('>'),
                        lower.contains('>')
                    );
                    assert_eq!(
                        actual_upper.fact.readable_string().contains('>'),
                        upper.contains('>')
                    );
                    let text = rule.rule_name_and_message(language);
                    assert!(!text.rule_name.is_empty() && text.message.contains(goal));
                    let detail =
                        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
                    assert!(contains(&detail, expected));
                    crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
                }
            }
        }
    }
}

#[test]
fn unguarded_partial_operators_use_actual_nonzero_evidence_in_wd() {
    for source in [
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/trig_first_quadrant.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/trig_first_quadrant_quotient_wd.lit"),
    ] {
        assert!(!source.contains("trust"));
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none());
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        assert!(contains(&detail, "CosNonzeroOnFirstQuadrant"));
        assert!(contains(&detail, "SinNonzeroOnFirstQuadrant"));
    }
    for goal in ["0!=cos(x)", "0!=sin(x)", "tan(x)*cot(x)=1"] {
        let code = format!("forall x R:\n    0<x\n    x<pi/2\n    =>:\n        {goal}\n");
        assert!(
            runtime(OutputLanguage::English)
                .run_litex_code(&code)
                .unwrap()
                .success,
            "{code}"
        );
    }
    // The deeper square denominator needs its base nonzero fact published first.
    // This is a proved consequence, not an added premise or a wider search budget.
    let square = "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        cos(x)!=0\n        1+tan(x)^2=1/cos(x)^2\n";
    assert!(
        runtime(OutputLanguage::English)
            .run_litex_code(square)
            .unwrap()
            .success
    );
}

#[test]
fn weak_missing_wrong_intervals_poles_wrong_signs_and_free_arguments_reject() {
    for bounds in [
        "0<=x\n    x<=pi/2",
        "0<x",
        "x<pi/2",
        "x<0\n    x<pi/2",
        "0<x\n    x<pi",
    ] {
        for goal in ["0<tan(x)", "0<cot(x)"] {
            let code = format!("forall x R:\n    {bounds}\n    =>:\n        {goal}\n");
            let run = runtime(OutputLanguage::English)
                .run_litex_code(&code)
                .unwrap();
            assert!(!run.success && run.session_error.is_none(), "{code}");
        }
    }
    for code in [
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        cot(x)<0\n",
        "forall x,y R:\n    0<x\n    x<pi/2\n    =>:\n        0<tan(y)\n",
        "forall x,y R:\n    0<x\n    y<pi/2\n    =>:\n        cos(x)!=0\n",
        "forall x C:\n    0<x\n    x<pi/2\n    =>:\n        0<tan(x)\n",
        "0<tan(0)\n",
        "0<cot(pi/2)\n",
        "tan(pi/2)=0\n",
        "cot(0)=0\n",
    ] {
        let run = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}

#[test]
fn raw_bound_lookup_preserves_direct_ceiling_and_publishes_no_nonzero_fact() {
    let mut rt = runtime(OutputLanguage::English);
    let prefix =
        "witness exist t R st {0<t,t<pi/2} from pi/4\nobtain x from exist t R st {0<t,t<pi/2}\n";
    let run = rt.run_litex_code(prefix).unwrap();
    assert!(run.success && run.session_error.is_none());
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("cos(x)!=0", crate::runtime::RealOrVirtualPath::Eval)
        .unwrap();
    let mut parsed = rt.parse(&blocks).unwrap();
    let Stmt::Fact(fact) = parsed.remove(0) else {
        panic!("fact");
    };
    let Fact::AtomicFact(crate::ast::fact::AtomicFact::NotEqualFact(nz)) = &fact else {
        panic!("nonzero");
    };
    let crate::ast::obj::Obj::TrigOperator(crate::ast::obj::TrigOperator::Cos(value)) = &nz.left
    else {
        panic!("cosine");
    };
    let direct = VerifyState::new(VerifyStateLevel::Direct);
    assert!(rt.verify_fact(&fact, direct).unwrap().is_failed());
    let (lower, upper) = rt
        .first_quadrant_bounds_for_arg(&value.arg)
        .expect("two actual known bounds");
    assert!(lower.cite_fact_id().is_some() && upper.cite_fact_id().is_some());
    assert!(rt.verify_fact(&fact, direct).unwrap().is_failed());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn failure_then_success_then_actual_forall_reuse_then_failure_keeps_scope() {
    let good = "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        0<tan(x)\n";
    let bad = good.replace("0<tan(x)", "tan(x)<0");
    let mut rt = runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    let first = rt.run_litex_code(good).unwrap();
    assert!(first.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(first)) = &first.statement_results[0]
    else {
        panic!("fact");
    };
    let source_id = first.store_and_infer_result.primary_fact_id();
    let reuse = rt.run_litex_code(good).unwrap();
    assert!(reuse.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(reuse)) = &reuse.statement_results[0]
    else {
        panic!("fact");
    };
    let VerifyFactResult::ForallFact(f) = &reuse.verify_result else {
        panic!("forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) = f.as_ref()
    else {
        panic!("actual reuse");
    };
    assert_eq!(p.cite_fact_id, source_id);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
