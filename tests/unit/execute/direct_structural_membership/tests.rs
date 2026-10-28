use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipReason as P;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::prelude::AtomicExceptEqualityFactSearchedProof as PSearch;
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[path = "integer_quotient_remainder.rs"]
mod integer_quotient_remainder;

#[test]
fn maintained_structural_and_tuple_tracers() {
    for code in [
        include_str!("../../../../examples/proof_nodes/atomic/direct_structural_membership.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_known_special_property/fn_tuple_carrier_after_equality.lit"),
    ] {
        assert!(runtime().run_litex_code(code).unwrap().success);
    }
}

#[test]
fn every_standard_carrier_composes_at_direct_without_publishing_facts() {
    for (setup, goal) in [
        ("have n N", "((n+1)+1)+1 $in N"),
        ("have n N", "(n+1)^2 $in N"),
        ("have a,b Z", "-((a+1)*(b-1)) $in Z"),
        ("have a,b Q", "(a-b)*(a+b) $in Q"),
        ("have a,b R", "(a-b)^2 $in R"),
        ("have a,b C", "(a-b)*(a+b) $in C"),
        ("have a,b cart(R,R)", "(b(1)-a(1))^2 $in R"),
        ("have x R", "floor(x)+ceil(x)+sign(x) $in Z"),
        ("have x R", "sin(x)+cos(x) $in R"),
        ("have x R", "floor(x)+1 $in C"),
        ("have n N", "n! $in N+"),
        ("have x R", "exp(x) $in R+"),
        ("have z C", "re(z)+img(z)+C_abs(z) $in R"),
        ("have a,b Q", "(a-b)/2 $in Q"),
        ("have a R*", "a^(-1) $in R"),
        ("have n Z", "abs(n) $in N"),
        ("have a cart(R,R)", "a(1) $in R"),
        (
            "have a R\n$is_finite_set({a})",
            "finite_set_size({a}) $in N",
        ),
        ("have a R", "pi+e $in R"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        let goal_fact = fact(&mut rt, goal);
        let before = memory_sizes(&rt);
        assert!(
            !rt.verify_fact(&goal_fact, VerifyState::new(VerifyStateLevel::Direct))
                .unwrap()
                .is_failed(),
            "{setup}; {goal}"
        );
        assert_eq!(memory_sizes(&rt), before, "search wrote evidence: {goal}");
    }
}

#[test]
fn symbolic_carrier_tree_is_independent_of_search_depth() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have n N").unwrap().success);
    let mut expression = "n".to_string();
    for _ in 0..12 {
        expression = format!("({expression}+1)");
    }
    let goal = fact(&mut rt, &format!("{expression} $in N"));
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
}

#[test]
fn full_verify_keeps_domains_and_false_carriers_rejected() {
    for (setup, bad) in [
        ("have x R", "x/0 $in R"),
        ("have x R", "(x/0+1) $in R"),
        ("have m,n N", "m-n $in N"),
        ("have m,n Z", "m/n $in Z"),
        ("have m Z", "m/2 $in Z"),
        ("have z C", "z+1 $in R"),
        ("have z C", "abs(z) $in R"),
        ("have x R", "sqrt(-1) $in R"),
        ("have x R", "log(1,x) $in R"),
        ("have x R", "floor(i) $in Z"),
        ("have x R", "x(1) $in N"),
        ("have x R", "(1,2)(3) $in R"),
        ("have x R", "x^(-1) $in R"),
        ("have x R", "0^(-1) $in R"),
        ("have x R", "(x+1) $in R+"),
        ("have x R", "not (x+1) $in Z"),
        ("have x R", "finite_set_size(R) $in N"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success);
        let stmt = parse(&mut rt, bad);
        let before = memory_sizes(&rt);
        assert!(
            rt.exec_stmt(&stmt).unwrap().is_failed(),
            "accepted {setup}; {bad}"
        );
        assert_eq!(memory_sizes(&rt), before, "failed statement leaked: {bad}");
    }
}

#[test]
fn direct_does_not_call_sp_or_unfold_user_functions() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn f(x R) R = x\nhave x R")
            .unwrap()
            .success
    );
    for code in ["f(x) $in R", "f(x)+1 $in R", "f(x)=x", "x-x=0"] {
        let Fact::AtomicFact(goal) = fact(&mut rt, code) else {
            panic!()
        };
        assert!(
            match &goal {
                crate::ast::fact::AtomicFact::EqualFact(equal) =>
                    rt.search_equal_fact_proof_directly(equal).is_none(),
                other => rt
                    .search_atomic_except_equality_fact_proof_directly(other)
                    .unwrap()
                    .is_none(),
            },
            "{code}"
        );
    }
    assert!(rt.run_litex_code("f(x) $in R").unwrap().success);
    let goal = fact(&mut rt, "f(x)+1 $in R");
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
}

#[test]
fn carrier_proof_retains_leaf_citations_and_known_priority() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have a,b R").unwrap().success);
    let Fact::AtomicFact(goal) = fact(&mut rt, "a-b $in R") else {
        panic!()
    };
    let Some(PSearch::ByStructuralMembership(proof)) = rt
        .search_atomic_except_equality_fact_proof_directly(&goal)
        .unwrap()
    else {
        panic!("structural")
    };
    let P::Sub { left, right } = proof.reason else {
        panic!("sub")
    };
    for leaf in [left, right] {
        let P::Known(cite) = leaf.reason else {
            panic!("known leaf")
        };
        assert!(rt
            .execution_environments_stack
            .iter()
            .any(|env| env.facts.facts_by_id.contains_key(&cite.cite_fact_id)));
    }
    assert!(rt.run_litex_code("a-b $in R").unwrap().success);
    assert!(matches!(
        rt.search_atomic_except_equality_fact_proof_directly(&goal)
            .unwrap(),
        Some(PSearch::ByKnownAtomicFact(_))
    ));

    // Batched alternatives keep the nearest carrier ahead of earlier facts,
    // and set aliases still use stored equality paths rather than new search.
    for setup in ["have u N\nu $in Z", "have S set = Z\nhave u S"] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success);
        let Fact::AtomicFact(goal) = fact(&mut rt, "u $in R") else {
            panic!()
        };
        let Some(PSearch::ByStructuralMembership(proof)) = rt
            .search_atomic_except_equality_fact_proof_directly(&goal)
            .unwrap()
        else {
            panic!("structural superset: {setup}")
        };
        let P::StandardSuperset(source) = proof.reason else {
            panic!("superset")
        };
        assert!(matches!(source.set, crate::ast::obj::StandardSet::Z));
        assert!(matches!(source.reason, P::Known(_)));
    }
}

#[test]
fn direct_carrier_json_retains_tree_and_bilingual_reason() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have a,b R").unwrap().success);
    let stmt = parse(&mut rt, "(a-b)^2 $in R");
    let result = rt.exec_stmt(&stmt).unwrap();
    assert!(!result.is_failed());
    let json = crate::json_output::project_stmt_detailed(&result, &rt);
    let proof = json
        .as_object()
        .unwrap()
        .get("verify")
        .unwrap()
        .as_object()
        .unwrap()
        .get("searched_proof")
        .unwrap()
        .as_object()
        .unwrap();
    assert_eq!(
        proof.get("type").unwrap().as_str().unwrap(),
        "by_structural_membership"
    );
    assert_eq!(proof.get("kind").unwrap().as_str().unwrap(), "pow");
    let base = proof.get("base").unwrap().as_object().unwrap();
    assert_eq!(base.get("kind").unwrap().as_str().unwrap(), "sub");
    assert!(base
        .get("left")
        .unwrap()
        .as_object()
        .unwrap()
        .get("cite")
        .unwrap()
        .as_object()
        .unwrap()
        .get("cite_fact_id")
        .is_some());
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let result = rt.run_litex_code("have x R\nfloor(x)+1 $in Z").unwrap();
        assert!(result.success);
        let json = crate::json_output::emit_run_normal(&result, &rt, "eval", None);
        let expected = if language == OutputLanguage::English {
            "by_structural_membership"
        } else {
            "结构归属"
        };
        assert!(json.contains(expected), "{json}");
    }
}

#[test]
fn order_domain_reuses_checked_argument_wd_without_publishing_it() {
    use crate::prelude::*;
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have A finite_set\nhave B set")
            .unwrap()
            .success
    );
    let Fact::AtomicFact(goal) = fact(
        &mut rt,
        "finite_set_size(set_minus(A, B)) < finite_set_size(A)",
    ) else {
        panic!("atomic comparison")
    };
    let before = memory_sizes(&rt);
    let VerifyAtomicFactWellDefinedResult::Success(proof) = rt
        .verify_atomic_fact_well_definedness(
            &goal,
            VerifyState::new(VerifyStateLevel::DefinitionAndForall),
        )
        .unwrap()
    else {
        panic!("finite difference comparison WD")
    };
    let PredicateDomainProof::ByCheckedArguments(requirements) =
        &proof.detailed_ref().predicate_domain
    else {
        panic!("checked argument domain fallback")
    };
    assert_eq!(requirements.len(), 2);
    for (index, requirement) in requirements.iter().enumerate() {
        assert_eq!(requirement.argument_index, index);
        assert_eq!(requirement.membership.set, StandardSet::R);
    }
    assert_eq!(memory_sizes(&rt), before, "domain fallback published state");
}

#[test]
fn order_domain_reuse_does_not_bypass_failed_argument_guards() {
    use crate::prelude::*;
    for (setup, goal) in [
        (
            "have A set\nhave B set",
            "finite_set_size(set_minus(A, B)) < 1",
        ),
        ("", "1 / 0 < 1"),
        ("", "sqrt(-1) < 1"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success);
        let Fact::AtomicFact(goal) = fact(&mut rt, goal) else {
            panic!("atomic comparison")
        };
        let before = memory_sizes(&rt);
        assert!(rt
            .verify_atomic_fact_well_definedness(
                &goal,
                VerifyState::new(VerifyStateLevel::DefinitionAndForall)
            )
            .unwrap()
            .is_failed());
        assert_eq!(memory_sizes(&rt), before);
    }
}

#[test]
fn order_domain_reuse_projects_its_checked_argument_provenance() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code(include_str!(
            "../../../../examples/wd/checked_argument_numeric_domain.lit"
        ))
        .unwrap();
    assert!(result.success);
    let json = crate::json_output::emit_run_detailed(&result, &rt, "eval", None);
    assert!(json.contains("by_checked_argument_membership"), "{json}");
    assert!(json.contains("argument_index"), "{json}");
}

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
fn parse(rt: &mut Runtime, code: &str) -> Stmt {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    statements.remove(0)
}
fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let Stmt::Fact(f) = parse(rt, code) else {
        panic!("{code}")
    };
    f
}
fn memory_sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|e| {
            (
                e.facts.facts_by_id.len(),
                e.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}
