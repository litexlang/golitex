use super::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::EqualFactSearchProofByKnownSpecialProperty as Known;
use crate::execute::execute_fact_stmt::{EqualityClassSearchMode, StrategySearch};

#[test]
fn run_examples_known_tuple_tracers() {
    for source in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_known_special_property/tuple_reconstruction.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_known_special_property/tuple_projection.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/known_function_cart_projection.lit"
        )),
    ] {
        let result = runtime().run_litex_code(source).unwrap();
        assert!(result.success, "{source}");
    }
}

fn known_state() -> VerifyState {
    let mut state = VerifyState::top_level().known_only_no_wd();
    state.equality_class_search = EqualityClassSearchMode::StoredPathsOnly;
    state
}

fn known(rt: &mut Runtime, goal: &str) -> Known {
    let before = store_sizes(rt);
    let result = known_with_wd(rt, goal);
    assert_eq!(
        before,
        store_sizes(rt),
        "lookup wrote reusable state: {goal}"
    );
    let VerifyEqualityResult::Success(proof) = result else {
        panic!("unproved: {goal}")
    };
    let EqualFactSearchedProof::ByKnownSpecialProperty(proof) = proof.searched_proof else {
        panic!("expected known tuple route: {goal}");
    };
    proof
}

// WD may use its ordinary domain/type rules; only truth is known-only.
// This is the actual builtin-premise entry's split, not a cached goal setup.
fn known_with_wd(rt: &mut Runtime, goal: &str) -> VerifyEqualityResult {
    let fact = equal(rt, goal);
    let VerifyFactResult::Equality(result) = rt
        .verify_builtin_rule_premise_with_wd_state(
            &fact.into(),
            known_state(),
            VerifyState::top_level().without_well_defined_storage(),
        )
        .unwrap()
    else {
        panic!("equality")
    };
    *result
}

#[test]
fn reconstruction_preserves_arity_order_and_subject_identity() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    for goal in ["p = (p[1],p[2])", "(p[1],p[2]) = p"] {
        let Known::TupleReconstruction(p) = known(&mut rt, goal) else {
            panic!("eta")
        };
        assert_eq!(p.shape.dimension(), 2);
        assert!(rt
            .fact_by_id_in_stack(p.shape.cite_fact_id().unwrap())
            .is_some());
        assert_eq!(p.subjects.len(), 2);
    }
    exec_ok(&mut rt, "have q cart(R,R)");
    for bad in [
        "p = (p[2],p[1])",
        "p = (p[1],p[1])",
        "p = (p[1],p[2],p[1])",
        "p = (q[1],q[2])",
    ] {
        assert!(verify(&mut rt, bad, known_state()).is_failed(), "{bad}");
    }
    exec_ok(&mut rt, "have t cart(R,Q,Z)");
    known(&mut rt, "t = (t[1],t[2],t[3])");
}

#[test]
fn tuple_projection_cites_stored_chain_and_keeps_wrong_value_unknown() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have a,b R");
    exec_ok(&mut rt, "have p cart(R,R) = (a,b)");
    exec_ok(&mut rt, "have q cart(R,R) = p");
    for goal in ["p[1] = a", "a = p[1]", "q[2] = b"] {
        let Known::TupleProjection(p) = known(&mut rt, goal) else {
            panic!("projection")
        };
        assert!(!p.tuple.tuple_equal.path.is_empty());
        for (_, _, id) in p.tuple.tuple_equal.path {
            assert!(rt.fact_by_id_in_stack(id).is_some());
        }
    }
    assert!(matches!(
        verify(&mut rt, "p[1] = b", known_state()),
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof { .. })
    ));
    for bad in ["p[0] = a", "p[3] = a"] {
        assert!(
            matches!(
                verify(&mut rt, bad, known_state()),
                VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_))
            ),
            "{bad}"
        );
    }
}

#[test]
fn cart_alias_supplies_shape_without_explicit_membership_bridge() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have plane set = cart(R,R)");
    exec_ok(&mut rt, "have p plane");
    known(&mut rt, "p = (p[1],p[2])");
    known(&mut rt, "tuple_dim(p) = 2");
    exec_ok(&mut rt, "p[1] $in R");
}

#[test]
fn function_projection_and_wd_work_fresh_cached_and_in_strategy() {
    for cached in [false, true] {
        let mut rt = runtime();
        exec_ok(
            &mut rt,
            "have fn vec(a,b cart(R,R)) cart(R,R) = (b[1]-a[1],b[2]-a[2])",
        );
        exec_ok(&mut rt, "have a,b cart(R,R)");
        if cached {
            exec_ok(&mut rt, "vec(a,b) = vec(a,b)");
        }
        for goal in ["vec(a,b)[1] = b[1]-a[1]", "b[2]-a[2] = vec(a,b)[2]"] {
            assert!(matches!(known(&mut rt, goal), Known::FnTupleProjection(_)));
        }
        let fact = equal(&mut rt, "vec(a,b)[1] = b[1]-a[1]");
        let before = store_sizes(&rt);
        let result = rt
            .verify_fact_in_strategy(&fact.clone().into(), StrategySearch { depth: 0 })
            .unwrap();
        assert_eq!(before, store_sizes(&rt));
        let VerifyFactResult::Equality(result) = result else {
            panic!("equal")
        };
        let VerifyEqualityResult::Success(result) = *result else {
            panic!("strategy")
        };
        assert!(matches!(
            result.searched_proof,
            EqualFactSearchedProof::ByKnownSpecialProperty(_)
        ));
        let result = rt
            .verify_builtin_rule_premise_with_wd_state(
                &fact.into(),
                known_state(),
                VerifyState::top_level().without_well_defined_storage(),
            )
            .unwrap();
        assert!(!result.is_failed());
        assert!(matches!(
            known_with_wd(&mut rt, "vec(a,b)[1] = b[2]-a[2]"),
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof { .. })
        ));
    }
}

#[test]
fn named_function_alias_is_not_a_special_cased_geometry_name() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn pair(x R) cart(R,R) = (x,x)");
    exec_ok(&mut rt, "have f fn(x R) cart(R,R) = pair");
    exec_ok(&mut rt, "have a R");
    known(&mut rt, "f(a)[1] = a");
    known(&mut rt, "f(a) = (f(a)[1],f(a)[2])");
    exec_ok(&mut rt, "let untyped_alias = pair");
    known(&mut rt, "untyped_alias(a)[1] = a");
    exec_ok(&mut rt, "have abstract_pair fn(x R) cart(R,R)");
    exec_ok(&mut rt, "let abstract_alias = abstract_pair");
    known(
        &mut rt,
        "abstract_alias(a) = (abstract_alias(a)[1],abstract_alias(a)[2])",
    );
}

#[test]
fn application_domain_is_checked_before_known_projection() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn pair(x N) cart(N,N) = (x,x)");
    let result = verify(&mut rt, "pair(-1)[1] = -1", VerifyState::top_level());
    assert!(matches!(
        result,
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_))
    ));
}

#[test]
fn known_does_not_recursively_unfold_nested_function_bodies() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn pair(x R) cart(R,R) = (x,x)");
    exec_ok(&mut rt, "have fn outer(x R) cart(R,R) = pair(x)");
    exec_ok(&mut rt, "have a R");
    let fact = equal(&mut rt, "outer(a)[1] = a");
    let before = store_sizes(&rt);
    assert!(rt
        .search_equal_fact_proof_by_known_special_property(&fact)
        .unwrap()
        .is_none());
    assert_eq!(before, store_sizes(&rt));
}

#[test]
fn proof_output_and_strict_conversion_keep_the_new_route() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    let result = exec_ok(&mut rt, "p = (p[1],p[2])");
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("TupleReconstruction"), "{json}");
    assert!(json.contains("cite_fact_id"), "{json}");
    assert!(project_stmt_normal(&result, &rt)
        .stringify()
        .contains("known_special_property"));
    // Cartesian membership already inferred this dimension equality. Ordinary
    // search must cite that stored path before trying SpecialProperty again.
    let goal = equal(&mut rt, "tuple_dim(p) = 2");
    let before = store_sizes(&rt);
    let VerifyEqualityResult::Success(stored) = known_with_wd(&mut rt, "tuple_dim(p) = 2") else {
        panic!("stored dimension equality")
    };
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = stored.searched_proof else {
        panic!("dimension equality must reuse its stored evidence")
    };
    check_path(&rt, &path, &goal.left, &goal.right);

    // Check the property certificate's strict conversion at its own entry,
    // independently of which earlier search stage now wins for this goal.
    let proof = rt
        .search_equal_fact_proof_by_known_special_property(&goal)
        .unwrap()
        .expect("Cartesian shape still supplies its dimension certificate");
    assert_eq!(store_sizes(&rt), before);
    assert!(matches!(
        strict_equal_arg_proof_from_searched(EqualFactSearchedProof::ByKnownSpecialProperty(proof)),
        Some(StrictEqualArgProof::ByKnownSpecialProperty(_))
    ));
}

#[test]
fn local_tuple_evidence_does_not_escape_its_scope() {
    let mut rt = runtime();
    let (goal, _local) = rt
        .run_in_local_env_and_take_env(|rt| {
            exec_ok(rt, "have local_pair cart(R,R)");
            let goal = equal(rt, "local_pair = (local_pair[1],local_pair[2])");
            assert!(rt
                .search_equal_fact_proof_by_known_special_property(&goal)?
                .is_some());
            Ok(goal)
        })
        .unwrap();
    assert!(rt
        .search_equal_fact_proof_by_known_special_property(&goal)
        .unwrap()
        .is_none());
}

#[test]
fn stored_equality_cycle_terminates_and_function_proof_serializes_its_domain_evidence() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    exec_ok(&mut rt, "have q cart(R,R) = p");
    exec_ok(&mut rt, "p = q");
    known(&mut rt, "q = (q[1],q[2])");
    exec_ok(&mut rt, "have fn pair(x R) cart(R,R) = (x,x)");
    exec_ok(&mut rt, "have a R");
    let result = exec_ok(&mut rt, "pair(a)[1] = a");
    let json = project_stmt_detailed(&result, &rt).stringify();
    for evidence in [
        "FnTupleProjection",
        "function_equal",
        "cite_fact_id",
        "all_signatures_match",
        "signature_match",
        "expanded_body",
        "component_equal",
    ] {
        assert!(json.contains(evidence), "missing {evidence}: {json}");
    }
}
