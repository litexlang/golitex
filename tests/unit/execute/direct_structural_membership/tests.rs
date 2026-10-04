use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::direct_atomic_fact_search_result::DirectAtomicFactSearchResult as D;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipReason as P;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

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
        ("have a,b cart(R,R)", "(b[1]-a[1])^2 $in R"),
        ("have x R", "floor(x)+ceil(x)+sign(x) $in Z"),
        ("have x R", "sin(x)+cos(x) $in R"),
        ("have x R", "floor(x)+1 $in C"),
        ("have n N", "n! $in N+"),
        ("have x R", "exp(x) $in R+"),
        ("have z C", "re(z)+img(z)+C_abs(z) $in R"),
        ("have a,b Q", "(a-b)/2 $in Q"),
        ("have a R*", "a^(-1) $in R"),
        ("have n Z", "abs(n) $in N"),
        ("have a cart(R,R)", "tuple_dim(a) $in N"),
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
        ("have x R", "tuple_dim(x) $in N"),
        ("have x R", "(1,2)[3] $in R"),
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
            matches!(rt.search_atomic_fact_proof_directly(&goal), D::NotFound),
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
    let D::ByStructuralMembership(proof) = rt.search_atomic_fact_proof_directly(&goal) else {
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
        rt.search_atomic_fact_proof_directly(&goal),
        D::ByKnownFact(_)
    ));

    // Batched alternatives keep the nearest carrier ahead of earlier facts,
    // and set aliases still use stored equality paths rather than new search.
    for setup in ["have u N\nu $in Z", "have S set = Z\nhave u S"] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success);
        let Fact::AtomicFact(goal) = fact(&mut rt, "u $in R") else {
            panic!()
        };
        let D::ByStructuralMembership(proof) = rt.search_atomic_fact_proof_directly(&goal) else {
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
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
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

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
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
