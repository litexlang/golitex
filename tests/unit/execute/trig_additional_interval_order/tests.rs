use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{AtomicExceptEqualityFactSearchProofByBuiltinRule,less::LessFactSearchProofByBuiltinRule,less_equal::LessEqualFactSearchProofByBuiltinRule};
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof,VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult,VerifyState,VerifyStateLevel};
use crate::execute::{ExecStmtResult,ExecFactStmtResult};
use crate::launch_command::{LaunchCommand,OutputLanguage};
use crate::runtime::{Runtime,FactId};
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
fn children(
    p: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> (Vec<&VerifyFactResult>, &'static str) {
    match p {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CosPositiveOnOpenHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "CosPositiveOnOpenHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::SinNegativeOnOpenNegativePi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "SinNegativeOnOpenNegativePi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::TanNegativeOnOpenNegativeHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "TanNegativeOnOpenNegativeHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CotNegativeOnOpenUpperHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "CotNegativeOnOpenUpperHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::SinPositiveOnFirstQuadrant(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "SinPositiveOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CosPositiveOnFirstQuadrant(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound],
            "CosPositiveOnFirstQuadrant",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CosStrictDecreasingOnClosedPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "CosStrictDecreasingOnClosedPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::TanStrictIncreasingOnOpenHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "TanStrictIncreasingOnOpenHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::CotStrictDecreasingOnOpenPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "CotStrictDecreasingOnOpenPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::SinWeakIncreasingOnClosedHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "SinWeakIncreasingOnClosedHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::CosWeakDecreasingOnClosedPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "CosWeakDecreasingOnClosedPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::TanWeakIncreasingOnOpenHalfPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "TanWeakIncreasingOnOpenHalfPi",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::CotWeakDecreasingOnOpenPi(p),
        ) => (
            vec![&p.lower_bound, &p.upper_bound, &p.argument_order],
            "CotWeakDecreasingOnOpenPi",
        ),
        _ => panic!("additional interval leaf"),
    }
}
fn known_cite(p: &VerifyFactResult) -> FactId {
    let VerifyFactResult::AtomicExceptEquality(p) = p else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &p.searched_proof else {
        panic!("actual known child")
    };
    p.cite_fact_id
}
#[test]
fn thirteen_actual_leaves_preserve_two_or_three_source_ids_and_ten_languages() {
    for lang in OutputLanguage::ALL {
        for (code,name,count) in [
        ("forall x R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        0<cos(x)\n","CosPositiveOnOpenHalfPi",2),
        ("forall x R:\n    -pi<x\n    x<0\n    =>:\n        sin(x)<0\n","SinNegativeOnOpenNegativePi",2),
        ("forall x R:\n    -pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n","TanNegativeOnOpenNegativeHalfPi",2),
        ("forall x R:\n    pi/2<x\n    x<pi\n    sin(x)!=0\n    =>:\n        cot(x)<0\n","CotNegativeOnOpenUpperHalfPi",2),
        ("forall x R:\n    0<x\n    x<pi/2\n    =>:\n        0<sin(x)\n","SinPositiveOnFirstQuadrant",2),
        ("forall x R:\n    0<x\n    x<pi/2\n    =>:\n        0<cos(x)\n","CosPositiveOnFirstQuadrant",2),
        ("forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(b)<cos(a)\n","CosStrictDecreasingOnClosedPi",3),
        ("forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n","TanStrictIncreasingOnOpenHalfPi",3),
        ("forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n","CotStrictDecreasingOnOpenPi",3),
        ("forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n","SinWeakIncreasingOnClosedHalfPi",3),
        ("forall a,b R:\n    0<=a\n    b<=pi\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n","CosWeakDecreasingOnClosedPi",3),
        ("forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n","TanWeakIncreasingOnOpenHalfPi",3),
        ("forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n","CotWeakDecreasingOnOpenPi",3),
    ] {
        let mut rt=runtime(lang);let run=rt.run_litex_code(code).unwrap();assert!(run.success&&run.session_error.is_none(),"{code}");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p))=&run.statement_results[0]else{panic!("fact")};let VerifyFactResult::ForallFact(f)=&p.verify_result else{panic!("forall")};let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f))=f.as_ref()else{panic!("local")};let VerifyFactResult::AtomicExceptEquality(p)=&f.proved_then_facts[0].verify_result else{panic!("atomic")};let VerifyAtomicExceptEqualityFactResult::Success(p)=p.as_ref()else{panic!("success")};let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule)=&p.searched_proof else{panic!("builtin")};let (children,actual)=children(rule);assert_eq!(actual,name);assert_eq!(children.len(),count);
        for(i,child)in children.iter().enumerate(){let cite=known_cite(child);assert_eq!(cite,f.assumed_dom_facts[i].store_and_infer.primary_fact_id());let VerifyFactResult::AtomicExceptEquality(p)=child else{panic!("atomic")};let VerifyAtomicExceptEqualityFactResult::Success(p)=p.as_ref()else{panic!("success")};assert_eq!(p.fact.readable_string(),f.local_env.facts.facts_by_id.get(&cite).unwrap().readable_string());}
        let text=rule.rule_name_and_message(lang);assert!(!text.rule_name.is_empty()&&text.message.contains("=>"));let detail=crate::json_output::project_stmt_detailed(&run.statement_results[0],&rt).stringify();assert!(detail.contains(name)&&detail.contains("cite_fact_id"));crate::json_output::project_stmt_normal(&run.statement_results[0],&rt);
    }
    }
}
#[test]
fn actual_converse_strict_for_weak_and_negative_endpoint_sources_verify() {
    for code in [
        "forall x R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>-pi/2\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    -pi/2<x\n    pi/2>x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>-pi/2\n    pi/2>x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    x>-pi/2\n    x<pi/2\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    -pi/2<x\n    pi/2>x\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    x>-pi/2\n    pi/2>x\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    -(pi/2)<x\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>-(pi/2)\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    0-pi/2<x\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>0-pi/2\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    (-1)*(pi/2)<x\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>(-1)*(pi/2)\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    -pi<x\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    x>-pi\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    -pi<x\n    0>x\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    x>-pi\n    0>x\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    -pi<x\n    x<0\n    =>:\n        0>sin(x)\n",
        "forall x R:\n    x>-pi\n    x<0\n    =>:\n        0>sin(x)\n",
        "forall x R:\n    -pi<x\n    0>x\n    =>:\n        0>sin(x)\n",
        "forall x R:\n    x>-pi\n    0>x\n    =>:\n        0>sin(x)\n",
        "forall x R:\n    (-1)*pi<x\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    x>(-1)*pi\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    0-pi<x\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    x>0-pi\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    -pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    x>-pi/2\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    -pi/2<x\n    0>x\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    x>-pi/2\n    0>x\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    -pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        0>tan(x)\n",
        "forall x R:\n    x>-pi/2\n    x<0\n    cos(x)!=0\n    =>:\n        0>tan(x)\n",
        "forall x R:\n    -pi/2<x\n    0>x\n    cos(x)!=0\n    =>:\n        0>tan(x)\n",
        "forall x R:\n    x>-pi/2\n    0>x\n    cos(x)!=0\n    =>:\n        0>tan(x)\n",
        "forall x R:\n    -(pi/2)<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    x>-(pi/2)\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    0-pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    x>0-pi/2\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    (-1)*(pi/2)<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    x>(-1)*(pi/2)\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    pi/2<x\n    x<pi\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    x>pi/2\n    x<pi\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    pi/2<x\n    pi>x\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    x>pi/2\n    pi>x\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    pi/2<x\n    x<pi\n    sin(x)!=0\n    =>:\n        0>cot(x)\n",
        "forall x R:\n    x>pi/2\n    x<pi\n    sin(x)!=0\n    =>:\n        0>cot(x)\n",
        "forall x R:\n    pi/2<x\n    pi>x\n    sin(x)!=0\n    =>:\n        0>cot(x)\n",
        "forall x R:\n    x>pi/2\n    pi>x\n    sin(x)!=0\n    =>:\n        0>cot(x)\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    x>0\n    x<pi/2\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    0<x\n    pi/2>x\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    x>0\n    pi/2>x\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        sin(x)>0\n",
        "forall x R:\n    x>0\n    x<pi/2\n    =>:\n        sin(x)>0\n",
        "forall x R:\n    0<x\n    pi/2>x\n    =>:\n        sin(x)>0\n",
        "forall x R:\n    x>0\n    pi/2>x\n    =>:\n        sin(x)>0\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>0\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    0<x\n    pi/2>x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    x>0\n    pi/2>x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    x>0\n    x<pi/2\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    0<x\n    pi/2>x\n    =>:\n        cos(x)>0\n",
        "forall x R:\n    x>0\n    pi/2>x\n    =>:\n        cos(x)>0\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    a>=-pi/2\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    pi/2>=b\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    b>=a\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    a>=-pi/2\n    pi/2>=b\n    b>=a\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    b>a\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    a>=-pi/2\n    b<=pi/2\n    a<=b\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    -pi/2<=a\n    pi/2>=b\n    a<=b\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    b>=a\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    a>=-pi/2\n    pi/2>=b\n    b>=a\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<b\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    b>a\n    =>:\n        sin(b)>=sin(a)\n",
        "forall a,b R:\n    -(pi/2)<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    a>=-(pi/2)\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    0-pi/2<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    a>=0-pi/2\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    (-1)*(pi/2)<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    a>=(-1)*(pi/2)\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    a>=0\n    b<=pi\n    a<b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    pi>=b\n    a<b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>a\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    a>=0\n    pi>=b\n    b>a\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(a)>cos(b)\n",
        "forall a,b R:\n    a>=0\n    b<=pi\n    a<b\n    =>:\n        cos(a)>cos(b)\n",
        "forall a,b R:\n    0<=a\n    pi>=b\n    a<b\n    =>:\n        cos(a)>cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>a\n    =>:\n        cos(a)>cos(b)\n",
        "forall a,b R:\n    a>=0\n    pi>=b\n    b>a\n    =>:\n        cos(a)>cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    a>=0\n    b<=pi\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    pi>=b\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>=a\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    a>=0\n    pi>=b\n    b>=a\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>a\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<=b\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    a>=0\n    b<=pi\n    a<=b\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    0<=a\n    pi>=b\n    a<=b\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>=a\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    a>=0\n    pi>=b\n    b>=a\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    b>a\n    =>:\n        cos(a)>=cos(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    a>-pi/2\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    pi/2>b\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    a>-pi/2\n    pi/2>b\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>tan(a)\n",
        "forall a,b R:\n    a>-pi/2\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    pi/2>b\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>tan(a)\n",
        "forall a,b R:\n    a>-pi/2\n    pi/2>b\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>tan(a)\n",
        "forall a,b R:\n    -(pi/2)<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    a>-(pi/2)\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    0-pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    a>0-pi/2\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    (-1)*(pi/2)<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    a>(-1)*(pi/2)\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    a>-pi/2\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    pi/2>b\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>=a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    a>-pi/2\n    pi/2>b\n    b>=a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    a>-pi/2\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    pi/2>b\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>=a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    a>-pi/2\n    pi/2>b\n    b>=a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    b>a\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)>=tan(a)\n",
        "forall a,b R:\n    -(pi/2)<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    a>-(pi/2)\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    0-pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    a>0-pi/2\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    (-1)*(pi/2)<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    a>(-1)*(pi/2)\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    a>0\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    pi>b\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    a>0\n    pi>b\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>cot(b)\n",
        "forall a,b R:\n    a>0\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>cot(b)\n",
        "forall a,b R:\n    0<a\n    pi>b\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>cot(b)\n",
        "forall a,b R:\n    a>0\n    pi>b\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    a>0\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    pi>b\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>=a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    a>0\n    pi>b\n    b>=a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    a>0\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    0<a\n    pi>b\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>=a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    a>0\n    pi>b\n    b>=a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    b>a\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)>=cot(b)\n",
    ]{let r=runtime(OutputLanguage::English).run_litex_code(code).unwrap();assert!(r.success&&r.session_error.is_none(),"{code}");}
}
#[test]
fn wrong_missing_bounds_order_argument_and_poles_reject() {
    for code in [
        "forall x R:\n    x<pi/2\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    -pi/2<x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        cos(x)<0\n",
        "forall x,y R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        0<cos(y)\n",
        "forall x R:\n    x<0\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    -pi<x\n    =>:\n        sin(x)<0\n",
        "forall x R:\n    -pi<x\n    x<0\n    =>:\n        0<sin(x)\n",
        "forall x,y R:\n    -pi<x\n    x<0\n    =>:\n        sin(y)<0\n",
        "forall x R:\n    x<0\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    -pi/2<x\n    cos(x)!=0\n    =>:\n        tan(x)<0\n",
        "forall x R:\n    -pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        0<tan(x)\n",
        "forall x,y R:\n    -pi/2<x\n    x<0\n    cos(x)!=0\n    =>:\n        tan(y)<0\n",
        "forall x R:\n    x<pi\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    pi/2<x\n    sin(x)!=0\n    =>:\n        cot(x)<0\n",
        "forall x R:\n    pi/2<x\n    x<pi\n    sin(x)!=0\n    =>:\n        0<cot(x)\n",
        "forall x,y R:\n    pi/2<x\n    x<pi\n    sin(x)!=0\n    =>:\n        cot(y)<0\n",
        "forall x R:\n    x<pi/2\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    0<x\n    =>:\n        0<sin(x)\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        sin(x)<0\n",
        "forall x,y R:\n    0<x\n    x<pi/2\n    =>:\n        0<sin(y)\n",
        "forall x R:\n    0<x\n    =>:\n        0<cos(x)\n",
        "forall x R:\n    0<x\n    x<pi/2\n    =>:\n        cos(x)<0\n",
        "forall x,y R:\n    0<x\n    x<pi/2\n    =>:\n        0<cos(y)\n",
        "forall a,b R:\n    b<=pi/2\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    a<=b\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    =>:\n        sin(a)<=sin(b)\n",
        "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<=b\n    =>:\n        sin(b)<sin(a)\n",
        "forall a,b R:\n    b<=pi\n    a<b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    a<b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<b\n    =>:\n        cos(a)<cos(b)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<=b\n    =>:\n        cos(b)<cos(a)\n",
        "forall a,b R:\n    b<=pi\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    a<=b\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    =>:\n        cos(b)<=cos(a)\n",
        "forall a,b R:\n    0<=a\n    b<=pi\n    a<=b\n    =>:\n        cos(a)<cos(b)\n",
        "forall a,b R:\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)<tan(a)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    cos(a)!=0\n    cos(b)!=0\n    =>:\n        tan(b)<tan(a)\n",
        "forall a,b R:\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)<cot(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(b)<=cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    sin(a)!=0\n    sin(b)!=0\n    =>:\n        cot(a)<cot(b)\n",
        "tan(pi/2)>0\n",
        "tan(-pi/2)<0\n",
        "cot(0)<0\n",
        "cot(pi)>0\n",
        "0<sin(0)\n",
        "0<cos(pi/2)\n",
        "sin(-pi)<0\n",
        "sin(0)<0\n",
    ]{let r=runtime(OutputLanguage::English).run_litex_code(code).unwrap();assert!(!r.success&&r.session_error.is_none(),"{code}");}
}
#[test]
fn interval_order_supplies_partial_wd_and_maintained_tracers_execute() {
    for code in [
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<b\n    =>:\n        tan(a)<tan(b)\n",
        "forall a,b R:\n    -pi/2<a\n    b<pi/2\n    a<=b\n    =>:\n        tan(a)<=tan(b)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<b\n    =>:\n        cot(b)<cot(a)\n",
        "forall a,b R:\n    0<a\n    b<pi\n    a<=b\n    =>:\n        cot(b)<=cot(a)\n",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let r = rt.run_litex_code(code).unwrap();
        assert!(r.success && r.session_error.is_none(), "{code}");
        let d = crate::json_output::project_run_detailed(
            &r,
            &rt,
            "eval",
            None,
        )
        .stringify();
        assert!(d.contains("well_defined"));
    }
    for code in [
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/trig_interval_signs.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/trig_interval_monotonicity.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/trig_first_quadrant_sin_cos.lit"),
    ]{assert!(runtime(OutputLanguage::English).run_litex_code(code).unwrap().success);}
}
#[test]
fn new_interval_goal_respects_direct_state_and_real_source_reuse() {
    let code = "forall x R:\n    -pi/2<x\n    x<pi/2\n    =>:\n        0<cos(x)\n";
    let bad = code.replace("0<cos(x)", "cos(x)<0");
    let mut rt = runtime(OutputLanguage::English);
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    let before = rt.execution_environments_stack[0].facts.facts_by_id.len();
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    assert_eq!(
        rt.execution_environments_stack[0].facts.facts_by_id.len(),
        before
    );
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    let saved = rt.run_litex_code(code).unwrap();
    assert!(saved.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &saved.statement_results[0] else {
        panic!("saved")
    };
    let source = p.store_and_infer_result.primary_fact_id();
    let reused = rt.run_litex_code(code).unwrap();
    assert!(reused.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &reused.statement_results[0] else {
        panic!("reused")
    };
    let VerifyFactResult::ForallFact(f) = &p.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) = f.as_ref()
    else {
        panic!("citation")
    };
    assert_eq!(f.cite_fact_id, source);
    assert!(!rt.run_litex_code(&bad).unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("have y R\n0<cos(y)").unwrap().success);
}
