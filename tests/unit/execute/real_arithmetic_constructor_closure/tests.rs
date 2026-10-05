use super::*;
use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    in_fact::InFactSearchProofByBuiltinRule, AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut stmts = rt.parse(&tokens).unwrap();
    assert_eq!(stmts.len(), 1);
    let Stmt::Fact(fact) = stmts.remove(0) else {
        panic!("fact: {code}")
    };
    fact
}

fn atomic_success(proof: &VerifyFactResult) -> &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactSuccess{
    let VerifyFactResult::AtomicExceptEquality(result) = proof else {
        panic!("atomic proof")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        panic!("success")
    };
    proof
}

#[test]
fn real_arithmetic_constructor_closure_preserves_real_statement_tracer() {
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/atomic/by_builtin_rule/real_arithmetic_constructor_closure.lit"
    ));
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success, "maintained tracer");
    // A checked real composite can be a leaf even when its operands are complex.
    let run = runtime()
        .run_litex_code("have fn f(x R) R = x\nforall x R:\n    (f(x) + i^2) / 4 $in R\n")
        .unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success, "closed real leaf from complex expression");
    let run = runtime()
        .run_litex_code("have fn f(x R+) R+ = x\nforall x R+:\n    f(x)^(-1) / 4 $in R\n")
        .unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(
        run.success,
        "negative integer power retains its nonzero function domain"
    );
}

#[test]
fn real_arithmetic_constructor_closure_uses_parent_wd_for_tuple_function_leaves() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    assert!(rt.run_litex_code(
        "have f fn(p cart(R, R)) R\nhave point cart(R, R)\nhave x R\n"
    ).unwrap().success);
    let leaf = fact(&mut rt, "f((x, point[2])) $in R");
    let Fact::AtomicFact(atomic_leaf @ AtomicFact::InFact(leaf_fact)) = &leaf else {
        panic!("function-return membership")
    };
    assert!(!rt.verify_obj_well_definedness(
        &leaf_fact.element, VerifyState::new(BuiltinRule),
    ).unwrap().is_failed(), "the enclosing WD proves the tuple argument domain");
    assert!(rt.verify_fact(&leaf, VerifyState::new(KnownSpecialProperty))
        .unwrap().is_failed(), "WD replay must not gain a higher search ceiling");
    let terminal = rt.search_atomic_except_equality_fact_proof(
        atomic_leaf, VerifyState::new(KnownSpecialProperty),
    ).unwrap().expect("checked function-return truth uses the inherited ceiling");
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(property) = terminal else {
        panic!("registered function signature evidence")
    };
    assert!(property.cite_property_fact_id().is_some());
    let signature_fact_id = property.cite_property_fact_id();
    let goal = fact(&mut rt, "f((x, point[2])) - f(point) $in R");
    let result = rt.verify_fact(&goal, VerifyState::new(BuiltinRule)).unwrap();
    assert!(!result.is_failed(), "R closure consumes parent WD, without replaying it below its ceiling");
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(closure),
        ),
    ) = &atomic_success(&result).searched_proof else {
        panic!("real constructor route")
    };
    let RealArithmeticConstructorTree::Sub { left, .. } = &closure.constructor_tree else {
        panic!("difference tree")
    };
    let RealArithmeticConstructorTree::Leaf(terminal) = left.as_ref() else {
        panic!("function return terminal")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(property) =
        terminal.searched_proof.as_ref() else {
        panic!("preserved signature route")
    };
    assert_eq!(property.cite_property_fact_id(), signature_fact_id);
    assert!(rt.lookup_known_atomic_fact(atomic_leaf).is_none(), "carrier search publishes no terminal membership");
    let executed = rt.exec_stmt(&Stmt::Fact(goal)).unwrap();
    assert!(!executed.is_failed());
    let detail = crate::json_output::project_stmt_detailed(&executed, &rt);
    let mut terminal_detail = &detail;
    for key in ["verify", "searched_proof", "constructor_tree", "left", "proof"] {
        let crate::knowledge_base::JsonValue::Object(object) = terminal_detail else {
            panic!("JSON object at {key}")
        };
        terminal_detail = object.get(key).expect(key);
    }
    let crate::knowledge_base::JsonValue::Object(object) = terminal_detail else {
        panic!("terminal JSON")
    };
    assert!(object.get("well_defined").is_none(), "WD remains on the parent verification stage");
    assert_eq!(object.get("fact"), Some(&crate::knowledge_base::JsonValue::String("f((x, point[2])) $in R".into())));
    assert!(object.get("searched_proof").unwrap().stringify().contains("cite_property_fact_id"));
    assert!(detail.stringify().contains("well_defined"), "parent WD evidence is retained");
    assert!(rt.run_litex_code(
        "prop real_difference_wd(g fn(p cart(R, R)) R, q cart(R, R)):\n    forall y R:\n        abs(g((y, q[2])) - g(q)) >= 0\n"
    ).unwrap().success, "the original reduced prop WD must pass");
}

#[test]
fn real_arithmetic_constructor_closure_retains_permissions_tree_and_citations() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn f(x R) R = x\nhave x R\n")
            .unwrap()
            .success
    );
    let goal = fact(&mut rt, "f(x)^2 / 4 $in R");
    for level in [Direct, KnownSpecialProperty] {
        let Fact::AtomicFact(atomic) = &goal else {
            panic!("atomic carrier goal")
        };
        assert!(rt
            .search_atomic_fact(atomic, VerifyState::new(level))
            .unwrap()
            .is_none(), "truth search must retain its {level:?} ceiling");
        assert!(
            rt.verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed(),
            "must not grant constructor closure at {level:?}"
        );
    }
    let result = rt
        .verify_fact(&goal, VerifyState::new(BuiltinRule))
        .unwrap();
    let proof = atomic_success(&result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(closure),
        ),
    ) = &proof.searched_proof
    else {
        panic!("dedicated builtin evidence")
    };
    let RealArithmeticConstructorTree::Div { left, right } = &closure.constructor_tree else {
        panic!("division")
    };
    let RealArithmeticConstructorTree::IntegerPow {
        base,
        exponent_in_integer_proof,
    } = left.as_ref()
    else {
        panic!("integer power")
    };
    assert_eq!(
        format!("{} $in {}", exponent_in_integer_proof.fact.element.readable_string(), exponent_in_integer_proof.fact.set.readable_string()),
        "2 $in Z"
    );
    assert!(matches!(
        right.as_ref(),
        RealArithmeticConstructorTree::Leaf(_)
    ));
    let RealArithmeticConstructorTree::Leaf(base_proof) = base.as_ref() else {
        panic!("function return leaf")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(codomain),
        ),
    ) = base_proof.searched_proof.as_ref()
    else {
        panic!("original function-return route")
    };
    assert!(!codomain.signature_return_matches.is_empty());
    let independent = fact(&mut rt, "f(x) $in R");
    let independent = rt
        .verify_fact(&independent, VerifyState::new(KnownSpecialProperty))
        .unwrap();
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(property) =
        &atomic_success(&independent).searched_proof
    else {
        panic!("property")
    };
    assert_eq!(
        property.cite_property_fact_id(),
        Some(codomain.cite_property_fact_id)
    );

    let executed = rt.exec_stmt(&Stmt::Fact(goal)).unwrap();
    assert!(!executed.is_failed());
    let detail = crate::json_output::project_stmt_detailed(&executed, &rt).stringify();
    for text in [
        "RealArithmeticConstructorClosure",
        "constructor_tree",
        "integer_pow",
        "exponent_in_integer_proof",
        "FnApplicationInCodomain",
        "cite_property_fact_id",
    ] {
        assert!(detail.contains(text), "missing {text}: {detail}");
    }
}

#[test]
fn real_arithmetic_constructor_closure_rejects_wrong_carriers_and_domains() {
    for code in [
        "have fn f(x C) C = x\nforall x C:\n    f(x)^2 / 4 <= f(x)^2 / 4\n",
        "have fn f(x R) C = i\nforall x R:\n    f(x) / 4 <= f(x) / 4\n",
        "have fn f(x R) R = x\nforall x R:\n    f(x)^2 / 0 $in R\n",
        "have fn f(x R) R = x\nforall x R:\n    f(x)^f(x) / 4 $in R\n",
        "have fn f(x R) R = x\nforall x R:\n    f(x)^2 / 4 $in R+\n",
        "have fn f(x R) R = x\nforall x R:\n    f(x)^2 / 4 $in N\n",
        "have fn f(x R) R = x\nforall x R:\n    f(x)^2 / 4 $in Q\n",
        "have fn f(x R) R = x\nf(0)^(-1) / 4 $in R\n",
        "have fn partial(x R: x > 0) R = x\npartial(0)^2 / 4 $in R\n",
        "prop bad(f fn(p cart(R, R)) C, point cart(R, R)):\n    forall x R:\n        abs(f((x, point[2])) - f(point)) >= 0\n",
        "prop bad(f fn(p cart(R, R): p[1] > 0) R, point cart(R, R)):\n    forall x R:\n        abs(f((x, point[2])) - f(point)) >= 0\n",
        "prop bad(f fn(p cart(R, R)) R, point cart(R, R)):\n    forall x R:\n        abs((f((x, point[2])) - f(point)) / 0) >= 0\n",
        "forall f fn(p cart(R, R)) R, point cart(R, R), x R:\n    abs(f((x, point[2])) - f(point)) < 0\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "unsound admission: {code}");
    }
}

#[test]
fn real_arithmetic_constructor_closure_does_not_publish_temporary_memberships() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn f(x R) R = x\nhave x R\n")
            .unwrap()
            .success
    );
    let goal = fact(&mut rt, "f(x)^2 / 4 $in R");
    let Fact::AtomicFact(atomic) = &goal else {
        panic!("atomic")
    };
    assert!(rt.lookup_known_atomic_fact(atomic).is_none());
    let run = rt.run_litex_code(
        "claim:\n    ? f(x)^2 / 4 < f(x)^2 / 4\n    f(x)^2 / 4 $in R\n    f(x)^2 / 4 < f(x)^2 / 4\n"
    ).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(!run.success);
    assert!(
        rt.lookup_known_atomic_fact(atomic).is_none(),
        "failed claim must roll back body member"
    );
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    let run = rt
        .run_litex_code("forall y R:\n    f(y)^2 / 4 $in R\n")
        .unwrap();
    assert!(run.success);
    assert!(
        rt.lookup_known_atomic_fact(atomic).is_none(),
        "forall local membership must stay local"
    );
}
