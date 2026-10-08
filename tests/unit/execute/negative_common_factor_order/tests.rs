use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{AtomicExceptEqualityFactSearchProofByBuiltinRule,less::LessFactSearchProofByBuiltinRule,greater::GreaterFactSearchProofByBuiltinRule,less_equal::LessEqualFactSearchProofByBuiltinRule,greater_equal::GreaterEqualFactSearchProofByBuiltinRule};
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult,VerifyState,VerifyStateLevel};
use crate::execute::{ExecStmtResult,ExecFactStmtResult};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand,OutputLanguage};
use crate::runtime::Runtime;
fn runtime(lang: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: lang,
    })
}
fn children(
    p: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> (&VerifyFactResult, &VerifyFactResult, &'static str) {
    match p {
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictLess(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftNegativeReversesStrictLess"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictLess(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightNegativeReversesStrictLess"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictLess(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftRightNegativeReversesStrictLess"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictLess(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightLeftNegativeReversesStrictLess"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictGreater(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftNegativeReversesStrictGreater"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictGreater(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightNegativeReversesStrictGreater"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictGreater(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftRightNegativeReversesStrictGreater"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(GreaterFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictGreater(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightLeftNegativeReversesStrictGreater"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakLessEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftNonpositiveReversesWeakLessEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakLessEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightNonpositiveReversesWeakLessEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakLessEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftRightNonpositiveReversesWeakLessEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakLessEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightLeftNonpositiveReversesWeakLessEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakGreaterEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftNonpositiveReversesWeakGreaterEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakGreaterEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightNonpositiveReversesWeakGreaterEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakGreaterEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulLeftRightNonpositiveReversesWeakGreaterEqual"),
    AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakGreaterEqual(p))=>(&p.factor_sign_proof,&p.reversed_order_proof,"MulRightLeftNonpositiveReversesWeakGreaterEqual"),
    _=>panic!("owned negative factor leaf")}
}
fn contains(v: &JsonValue, s: &str) -> bool {
    match v {
        JsonValue::String(x) => x == s,
        JsonValue::Array(a) => a.iter().any(|x| contains(x, s)),
        JsonValue::Object(o) => o
            .keys_in_order()
            .iter()
            .any(|k| contains(o.get(k).unwrap(), s)),
        _ => false,
    }
}
fn top_cite(p: &VerifyFactResult) -> crate::runtime::FactId {
    let VerifyFactResult::AtomicExceptEquality(a) = p else {
        panic!("comparison")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(a) = a.as_ref() else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &a.searched_proof else {
        panic!("actual known source")
    };
    p.cite_fact_id
}
#[test]
fn sixteen_actual_rigid_leaves_keep_two_source_ids_and_ten_languages() {
    for lang in OutputLanguage::ALL {
        for (code, name) in [
            (
                "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<c*b\n",
                "MulLeftNegativeReversesStrictLess",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<b*c\n",
                "MulRightNegativeReversesStrictLess",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<b*c\n",
                "MulLeftRightNegativeReversesStrictLess",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<c*b\n",
                "MulRightLeftNegativeReversesStrictLess",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>c*b\n",
                "MulLeftNegativeReversesStrictGreater",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>b*c\n",
                "MulRightNegativeReversesStrictGreater",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>b*c\n",
                "MulLeftRightNegativeReversesStrictGreater",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>c*b\n",
                "MulRightLeftNegativeReversesStrictGreater",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<=c*b\n",
                "MulLeftNonpositiveReversesWeakLessEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<=b*c\n",
                "MulRightNonpositiveReversesWeakLessEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<=b*c\n",
                "MulLeftRightNonpositiveReversesWeakLessEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<=c*b\n",
                "MulRightLeftNonpositiveReversesWeakLessEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>=c*b\n",
                "MulLeftNonpositiveReversesWeakGreaterEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>=b*c\n",
                "MulRightNonpositiveReversesWeakGreaterEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>=b*c\n",
                "MulLeftRightNonpositiveReversesWeakGreaterEqual",
            ),
            (
                "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>=c*b\n",
                "MulRightLeftNonpositiveReversesWeakGreaterEqual",
            ),
        ] {
            let mut rt = runtime(lang);
            let run = rt.run_litex_code(code).unwrap();
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
            let (sign, order, actual) = children(rule);
            assert_eq!(actual, name);
            assert_eq!(
                top_cite(sign),
                f.assumed_dom_facts[0].store_and_infer.primary_fact_id()
            );
            assert_eq!(
                top_cite(order),
                f.assumed_dom_facts[1].store_and_infer.primary_fact_id()
            );
            let text = rule.rule_name_and_message(lang);
            assert!(!text.rule_name.is_empty() && text.message.contains("=>"));
            let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
            assert!(contains(&detail, name));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}
#[test]
fn all_sign_order_orientations_and_stronger_weak_premises_are_checked() {
    for code in [
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a>=b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>c\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>c\n    a>=b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a>=b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b<a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a>b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a>=b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b<a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a>b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a>=b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>c\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>c\n    a>=b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a>=b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b<a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a>b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a>=b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b<a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a>b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a>=b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>c\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>c\n    a>=b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a>=b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b<a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a>b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a>=b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b<a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a>b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a>=b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a>b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>c\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>c\n    a>=b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>c\n    b<a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>c\n    a>b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a>=b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b<a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a>b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a>=b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b<a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a>b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b>=a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>c\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>c\n    b>=a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b>=a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a<b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b>a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b>=a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a<b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b>a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b>=a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>c\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>c\n    b>=a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b>=a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a<b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b>a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b>=a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a<b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b>a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b>=a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>c\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>c\n    b>=a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b>=a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    a<b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<=0\n    b>a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b>=a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    a<b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0>=c\n    b>a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b>=a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b>a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>c\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>c\n    b>=a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>c\n    a<b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>c\n    b>a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b>=a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    a<b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<=0\n    b>a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b>=a\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    a<b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0>=c\n    b>a\n    =>:\n        a*c>=c*b\n",
    ] {
        let run = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}");
    }
}
#[test]
fn wrong_missing_weak_for_strict_zero_and_domain_controls_reject() {
    for code in [
        "forall a,b,c R:\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    0<c\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c=0\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    b<a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    0<c\n    b<a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    c=0\n    b<a\n    =>:\n        a*c<b*c\n",
        "forall a,b,c R:\n    b<a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    0<c\n    b<a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    c=0\n    b<a\n    =>:\n        c*a<b*c\n",
        "forall a,b,c R:\n    b<a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    0<c\n    b<a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    c=0\n    b<a\n    =>:\n        a*c<c*b\n",
        "forall a,b,c R:\n    a<b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    0<c\n    a<b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    c=0\n    a<b\n    =>:\n        c*a>c*b\n",
        "forall a,b,c R:\n    a<b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    0<c\n    a<b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    c=0\n    a<b\n    =>:\n        a*c>b*c\n",
        "forall a,b,c R:\n    a<b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    0<c\n    a<b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    c=0\n    a<b\n    =>:\n        c*a>b*c\n",
        "forall a,b,c R:\n    a<b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    0<c\n    a<b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c<0\n    a<=b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    c=0\n    a<b\n    =>:\n        a*c>c*b\n",
        "forall a,b,c R:\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    0<c\n    b<=a\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a<=c*b\n",
        "forall a,b,c R:\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    0<c\n    b<=a\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c<=b*c\n",
        "forall a,b,c R:\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    0<c\n    b<=a\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        c*a<=b*c\n",
        "forall a,b,c R:\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    0<c\n    b<=a\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    c<0\n    a<b\n    =>:\n        a*c<=c*b\n",
        "forall a,b,c R:\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    0<c\n    a<=b\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a>=c*b\n",
        "forall a,b,c R:\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    0<c\n    a<=b\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c>=b*c\n",
        "forall a,b,c R:\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    0<c\n    a<=b\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a>=b*c\n",
        "forall a,b,c R:\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    0<c\n    a<=b\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<0\n    =>:\n        a*c>=c*b\n",
        "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        a*c>=c*b\n",
        "forall a,b C,c R:\n    c<0\n    =>:\n        c*a<c*b\n",
        "forall a,b,c,d R:\n    c<0\n    b<a\n    =>:\n        c*a<d*b\n",
    ] {
        let run = runtime(OutputLanguage::English)
            .run_litex_code(code)
            .unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}
#[test]
fn literal_factor_and_both_maintained_tracers_execute_without_extra_assumptions() {
    for code in [
    "forall a,b R:\n    b<a\n    =>:\n        (-1)*a<(-1)*b\n",
    "forall a,b R:\n    b<a\n    =>:\n        a*(-1)<b*(-1)\n",
    "forall a,b R:\n    a<b\n    =>:\n        (-1)*a>(-1)*b\n",
    "forall a,b R:\n    a<b\n    =>:\n        a*(-1)>b*(-1)\n",
    "forall a,b R:\n    b<a\n    =>:\n        (-1)*a<=(-1)*b\n",
    "forall a,b R:\n    b<a\n    =>:\n        a*(-1)<=b*(-1)\n",
    "forall a,b R:\n    a<b\n    =>:\n        (-1)*a>=(-1)*b\n",
    "forall a,b R:\n    a<b\n    =>:\n        a*(-1)>=b*(-1)\n",
include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/negative_common_factor_order.lit"),include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/nonpositive_common_factor_weak_order.lit"),
 ] {let run=runtime(OutputLanguage::English).run_litex_code(code).unwrap();assert!(run.success&&run.session_error.is_none(),"{code}");}
}
#[test]
fn success_failure_reuse_retains_actual_whole_forall_source() {
    let good = "forall a,b,c R:\n    c<0\n    b<a\n    =>:\n        c*a<c*b\n";
    let bad = good.replace("c*a<c*b", "c*a>c*b");
    let mut rt = runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    let first = rt.run_litex_code(good).unwrap();
    assert!(first.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &first.statement_results[0] else {
        panic!("fact")
    };
    let source = s.store_and_infer_result.primary_fact_id();
    let reuse = rt.run_litex_code(good).unwrap();
    assert!(reuse.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &reuse.statement_results[0] else {
        panic!("fact")
    };
    let VerifyFactResult::ForallFact(f) = &s.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) = f.as_ref()
    else {
        panic!("source replay")
    };
    assert_eq!(p.cite_fact_id, source);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
