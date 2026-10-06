use super::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::EqualFactSearchProofByKnownSpecialProperty as Known;

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
    VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty)
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

// Test the truth-only SP reader after separately checking ordinary goal WD.
// Production verify passes the same state to WD and truth; this helper does
// not claim a fresh complex goal's WD is available at the SP ceiling.
fn known_with_wd(rt: &mut Runtime, goal: &str) -> VerifyEqualityResult {
    let fact = equal(rt, goal);
    let wd = match rt.verify_equal_fact_well_definedness(&fact, VerifyState::top_level()).unwrap() {
        super::super::well_defined_result::VerifyEqualFactWellDefinedResult::Success(wd) => wd,
        super::super::well_defined_result::VerifyEqualFactWellDefinedResult::Failed(reason) => {
            return VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(reason));
        }
    };
    match rt.search_equal_fact_proof(&fact, known_state()).unwrap() {
        Some(searched_proof) => VerifyEqualityResult::Success(VerifyEqualitySuccess {
            fact, well_defined_proof: wd, searched_proof,
        }),
        None => VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
            fact, well_defined_proof: wd,
        }),
    }
}

#[test]
fn reconstruction_preserves_arity_order_and_subject_identity() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    for goal in ["p = (p(1),p(2))", "(p(1),p(2)) = p"] {
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
        "p = (p(2),p(1))",
        "p = (p(1),p(1))",
        "p = (p(1),p(2),p(1))",
        "p = (q(1),q(2))",
    ] {
        assert!(verify(&mut rt, bad, known_state()).is_failed(), "{bad}");
    }
    exec_ok(&mut rt, "have t cart(R,Q,Z)");
    known(&mut rt, "t = (t(1),t(2),t(3))");
}

#[test]
fn tuple_projection_cites_stored_chain_and_keeps_wrong_value_unknown() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have a,b R");
    exec_ok(&mut rt, "have p cart(R,R) = (a,b)");
    exec_ok(&mut rt, "have q cart(R,R) = p");
    for goal in ["p(1) = a", "a = p(1)", "q(2) = b"] {
        let Known::TupleProjection(p) = known(&mut rt, goal) else {
            panic!("projection")
        };
        assert!(!p.tuple.tuple_equal.path.is_empty());
        for (_, _, id) in p.tuple.tuple_equal.path {
            assert!(rt.fact_by_id_in_stack(id).is_some());
        }
    }
    assert!(matches!(
        verify(&mut rt, "p(1) = b", known_state()),
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof { .. })
    ));
    for bad in ["p(0) = a", "p(3) = a"] {
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
    known(&mut rt, "p = (p(1),p(2))");
    exec_ok(&mut rt, "p $in finite_seq(R,2)");
    exec_ok(&mut rt, "p(1) $in R");
}

#[test]
fn function_projection_and_wd_work_fresh_cached_and_in_strategy() {
    for cached in [false, true] {
        let mut rt = runtime();
        exec_ok(
            &mut rt,
            "have fn vec(a,b cart(R,R)) cart(R,R) = (b(1)-a(1),b(2)-a(2))",
        );
        exec_ok(&mut rt, "have a,b cart(R,R)");
        if cached {
            exec_ok(&mut rt, "vec(a,b) = vec(a,b)");
        }
        for goal in ["vec(a,b)(1) = b(1)-a(1)", "b(2)-a(2) = vec(a,b)(2)"] {
            assert!(matches!(known(&mut rt, goal), Known::FnTupleProjection(_)));
        }
        let fact = equal(&mut rt, "vec(a,b)(1) = b(1)-a(1)");
        let before = store_sizes(&rt);
        let result = rt
            .verify_fact(&fact.clone().into(), VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule))
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
        assert!(rt.search_equal_fact_proof(&fact, known_state()).unwrap().is_some());
        assert!(matches!(
            known_with_wd(&mut rt, "vec(a,b)(1) = b(2)-a(2)"),
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
    known(&mut rt, "f(a)(1) = a");
    known(&mut rt, "f(a) = (f(a)(1),f(a)(2))");
    exec_ok(&mut rt, "let untyped_alias = pair");
    known(&mut rt, "untyped_alias(a)(1) = a");
    exec_ok(&mut rt, "have abstract_pair fn(x R) cart(R,R)");
    exec_ok(&mut rt, "let abstract_alias = abstract_pair");
    known(
        &mut rt,
        "abstract_alias(a) = (abstract_alias(a)(1),abstract_alias(a)(2))",
    );
}

#[test]
fn application_domain_is_checked_before_known_projection() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn pair(x N) cart(N,N) = (x,x)");
    let result = verify(&mut rt, "pair(-1)(1) = -1", VerifyState::top_level());
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
    let fact = equal(&mut rt, "outer(a)(1) = a");
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
    let result = exec_ok(&mut rt, "p = (p(1),p(2))");
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("TupleReconstruction"), "{json}");
    assert!(json.contains("cite_fact_id"), "{json}");
    assert!(project_stmt_normal(&result, &rt)
        .stringify()
        .contains("known_special_property"));
    // The accepted reconstruction equality must be reused before searching
    // its complete-domain certificate again.
    let goal = equal(&mut rt, "p = (p(1),p(2))");
    let before = store_sizes(&rt);
    let VerifyEqualityResult::Success(stored) = known_with_wd(&mut rt, "p = (p(1),p(2))") else {
        panic!("stored reconstruction equality")
    };
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = stored.searched_proof else {
        panic!("reconstruction must reuse its stored evidence")
    };
    check_path(&rt, &path, &goal.left, &goal.right);
    let proof = rt.search_equal_fact_proof_by_known_special_property(&goal).unwrap()
        .expect("exact Cartesian element domain supplies the reconstruction certificate");
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
            let goal = equal(rt, "local_pair = (local_pair(1),local_pair(2))");
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
    known(&mut rt, "q = (q(1),q(2))");
    exec_ok(&mut rt, "have fn pair(x R) cart(R,R) = (x,x)");
    exec_ok(&mut rt, "have a R");
    let result = exec_ok(&mut rt, "pair(a)(1) = a");
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

#[test]
fn run_examples_template_aliases_and_named_results_retain_tuple_value_paths() {
    use crate::execute::execute_fact_stmt::known_tuple::KnownFunctionTupleApplicability;
    let mut rt = runtime();
    exec_ok(&mut rt, "struct Triple<X set>:\n    first X\n    second X\n    third X");
    exec_ok(&mut rt, "template<X set>:\n    have fn triple(a,b,c X) &Triple<X> = (a,b,c)");
    exec_ok(&mut rt, "let alias = \\triple<R>");
    exec_ok(&mut rt, "let second_alias = alias");
    let Known::FnTupleValue(value) = known(&mut rt, "second_alias(4,5,6) = (4,5,6)") else { panic!("tuple value") };
    assert_eq!(value.function.function_equal.path.len(), 2);
    for (_, _, id) in &value.function.function_equal.path {
        assert!(rt.fact_by_id_in_stack(*id).is_some());
    }
    assert!(matches!(value.function.applicability, KnownFunctionTupleApplicability::TemplateDefinition { .. }));
    exec_ok(&mut rt, "let chosen = second_alias(1,2,3)");
    exec_ok(&mut rt, "have chosen_struct &Triple<R> = chosen");
    // Truth lookup must not publish an intermediate chosen=(1,2,3) fact.
    let Known::FnTupleProjection(projection) = known(&mut rt, "chosen_struct(1) = 1") else { panic!("projection") };
    assert_eq!(projection.subject_equal.path.len(), 2);
    for (_, _, id) in &projection.subject_equal.path {
        assert!(rt.fact_by_id_in_stack(*id).is_some());
    }
    for code in ["chosen_struct.first = 1", "chosen_struct.second = 2", "chosen_struct.third = 3"] {
        exec_ok(&mut rt, code);
    }
    assert!(matches!(known(&mut rt, "chosen = (1,2,3)"), Known::FnTupleValue(_)));
    for wrong in ["chosen_struct.first = 2", "chosen_struct.second = 1", "chosen = (3,2,1)", "chosen = (1,2)"] {
        assert!(verify(&mut rt, wrong, VerifyState::top_level()).is_failed(), "{wrong}");
    }
    let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/stmt_nodes/definition/template_alias_struct_tuple.lit"));
    assert!(runtime().run_litex_code(source).unwrap().success);
}

#[test]
fn template_tuple_aliases_keep_function_domains_and_header_guards() {
    let mut rt = runtime();
    exec_ok(&mut rt, "template<S set: $is_nonempty_set(S)>:\n    have fn positive_pair(x N: x > 0) cart(N,N) = (x,x)");
    exec_ok(&mut rt, "let alias = \\positive_pair<R>");
    exec_ok(&mut rt, "let second_alias = alias");
    known(&mut rt, "second_alias(2) = (2,2)");
    for wrong in ["second_alias(-1) = (-1,-1)", "second_alias(0) = (0,0)", "second_alias(2,3) = (2,3)", "\\positive_pair<{}>(2) = (2,2)", "\\positive_pair<R,1>(2) = (2,2)"] {
        assert!(verify(&mut rt, wrong, VerifyState::top_level()).is_failed(), "{wrong}");
    }
    let before = store_sizes(&rt);
    let failed = rt.run_litex_code("let invalid = \\positive_pair<{}>\n").unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    assert_eq!(before, store_sizes(&rt));
    assert!(!rt.run_litex_code("invalid(2) = (2,2)\n").unwrap().success);
}

#[test]
fn template_tuple_output_keeps_alias_and_subject_citations() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language });
        for source in ["template<S set>:\n    have fn pair(x S) cart(S,S) = (x,x)", "let alias = \\pair<R>", "let value = alias(2)", "have typed cart(R,R) = value"] {
            exec_ok(&mut rt, source);
        }
        let result = exec_ok(&mut rt, "typed(1) = 2");
        let json = project_stmt_detailed(&result, &rt).stringify();
        let subject_path = if language == OutputLanguage::English { "subject_equal" } else { "对象等式路径" };
        for field in ["FnTupleProjection", subject_path, "function_equal", "template_definition", "instance", "signature_match", "expanded_body"] {
            assert!(json.contains(field), "{field}: {json}");
        }
        let result = exec_ok(&mut rt, "value = (2,2)");
        assert!(project_stmt_detailed(&result, &rt).stringify().contains("FnTupleValue"));
        let output = project_stmt_normal(&result, &rt).stringify();
        assert!(output.contains(if language == OutputLanguage::English { "Equivalence class" } else { "等价类" }) || output.contains(if language == OutputLanguage::English { "known_special_property" } else { "已知特殊属性" }), "{output}");
    }
}

#[test]
fn homogeneous_cart_coordinate_variable_index_and_binder_wd() {
    for source in [
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_known_special_property/homogeneous_cart_coordinate.lit")),
        "have A set = R\nforall p cart(R,A), j closed_range(1,2):\n    p(j) $in A",
        "have fn vec(x R) cart(R,R) = (x,x)\nclaim:\n    ? forall x R:\n        x = x\n    vec(x) $in finite_seq(R,2)\n    forall j closed_range(1,2):\n        vec(x)(j) $in R",
    ] {
        assert!(runtime().run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn homogeneous_cart_coordinate_rejects_wrong_carrier_and_invalid_index() {
    for source in [
        "forall p cart(R,Z), j closed_range(1,2):\n    p(j) $in Z",
        "forall p cart(R,R), j closed_range(1,2):\n    p(j) $in N",
        "forall p cart(R,R), j closed_range(0,2):\n    p(j) $in R",
        "forall p cart(R,R), j closed_range(1,3):\n    p(j) $in R",
        "forall p cart(R,R), j R:\n    1 <= j\n    j <= 2\n    =>:\n        p(j) $in R",
        "forall p set, j closed_range(1,2):\n    p(j) $in R",
    ] {
        assert!(!runtime().run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn homogeneous_cart_coordinate_keeps_all_factor_and_shape_evidence_read_only() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::
        search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
    let mut rt = runtime();
    exec_ok(&mut rt, "have A nonempty_set = R");
    exec_ok(&mut rt, "have p cart(R,A)");
    exec_ok(&mut rt, "have j closed_range(1,2)");
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(fact))) = parse(&mut rt, "p(j) $in A") else {
        panic!("membership")
    };
    assert!(!rt.verify_fact_well_definedness(
        &Fact::AtomicFact(AtomicFact::InFact(fact.clone())), VerifyState::top_level(),
    ).unwrap().is_failed());
    let before = store_sizes(&rt);
    let Some(InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(proof)) =
        rt.search_in_fact_proof_by_known_special_property(&fact) else {
            panic!("homogeneous coordinate leaf")
        };
    assert_eq!(before, store_sizes(&rt));
    assert_eq!(proof.carrier_equals.len(), 2);
    assert_eq!(proof.shape.dimension(), 2);
    assert!(rt.fact_by_id_in_stack(proof.shape.cite_fact_id().unwrap()).is_some());
    let result = exec_ok(&mut rt, "p(j) $in A");
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("HomogeneousTupleCoordinate"), "{json}");
    assert!(json.contains("carrier_equals"), "{json}");
    assert!(json.contains("cite_fact_id"), "{json}");
}

#[test]
fn known_cart_index_upper_bound_handles_alias_and_function_shape() {
    for source in [
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_known_special_property/known_cart_index_upper_bound.lit")),
        "have X set = Z\nhave c set = cart(X,X,X,X)\nforall p c, j closed_range(1,4):\n    p(j) $in X",
        "have n N+ = 3\nhave c set = cart(R,R,R)\nhave fn encode(p c) fn(k closed_range(1,n)) R = fn(j closed_range(1,n)) R {p(j)}",
    ] {
        assert!(runtime().run_litex_code(source).unwrap().success, "{source}");
    }
    for source in [
        "have n N+ = 4\nhave c set = cart(R,R,R)\nforall p c, j closed_range(1,n):\n    p(j) $in R",
        "have c set = cart(R,R,R)\nforall p c, j closed_range(0,3):\n    p(j) $in R",
        "have c set = cart(R,R,R)\nforall p c, j R:\n    1 <= j\n    j <= 3\n    =>:\n        p(j) $in R",
        "have c set = cart(R,R,R)\nforall p c, j N+:\n    p(j) $in R",
    ] {
        assert!(!runtime().run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn known_cart_index_upper_bound_preserves_read_only_source_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::
        search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
    let mut rt = runtime();
    exec_ok(&mut rt, "have c nonempty_set = cart(R,R,R)");
    exec_ok(&mut rt, "have p c");
    exec_ok(&mut rt, "have j closed_range(1,3)");
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(fact))) = parse(&mut rt, "p(j) $in R") else {
        panic!("coordinate membership")
    };
    assert!(!rt.verify_fact_well_definedness(
        &Fact::AtomicFact(AtomicFact::InFact(fact.clone())), VerifyState::top_level(),
    ).unwrap().is_failed());
    let before = store_sizes(&rt);
    let Some(InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(proof)) =
        rt.search_in_fact_proof_by_known_special_property(&fact) else {
            panic!("known complete-domain coordinate leaf")
        };
    assert_eq!(before, store_sizes(&rt));
    assert_eq!(proof.shape.dimension(), 3);
    assert_eq!(proof.carrier_equals.len(), 3);
    assert!(rt.fact_by_id_in_stack(proof.shape.cite_fact_id().unwrap()).is_some());
    let result = exec_ok(&mut rt, "p(j) $in R");
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("HomogeneousTupleCoordinate"), "{json}");
    assert!(json.contains("carrier_equals") && json.contains("cite_fact_id"), "{json}");
}
