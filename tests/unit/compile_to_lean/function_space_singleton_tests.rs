use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::function_domain::{FunctionDomainEmptyProof as Empty, FunctionDomainEmptyCarrierEvidence as Carrier};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyDomainFunctionSpaceSingletonBuiltinRuleProof;
use crate::prelude::*;

const GUARD: &str = "forall B set:\n    fn(x R:x!=x) B={{}}\n";
const CARRIER: &str = "forall B set:\n    fn(x {}) B={{}}\n";
const REVERSE: &str = "forall B set:\n    {{}}=fn(x {}) B\n";
const FINITE: &str = "cart()={{}}\n";
const ALIAS: &str = "forall A,B set:\n    A={}\n    =>:\n        fn(x A) B={{}}\n";
const AMBIENT_GUARD: &str = "forall a,b R,B set:\n    a=b\n    =>:\n        fn(x R:a!=b) B={{}}\n";

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!("original fact")
    };
    let result = match &mut p.verify_result {
        VerifyFactResult::ForallFact(p) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!("original local forall")
            };
            &mut p.proved_then_facts.last_mut().unwrap().verify_result
        }
        p => p,
    };
    super::equality_proof_mut(result)
}
fn selected(
    run: &mut RunLitexCodeResult,
) -> &mut EmptyDomainFunctionSpaceSingletonBuiltinRuleProof {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyDomainFunctionSpaceSingleton(p),
    ) = &mut equality(run).searched_proof
    else {
        panic!("original empty-range rule")
    };
    p
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, label: &str) {
    assert!(
        super::compile_run(run, c, label).is_err(),
        "altered original absence evidence accepted: {label}"
    );
}

#[test]
fn space_singleton_replays_original_guard_carrier_finite_and_both_orientations() {
    for source in [GUARD, CARRIER, REVERSE, FINITE] {
        let (mut run, c) = super::execute(source);
        selected(&mut run);
        let output = super::compile_run(&run, &c, "space_singleton_original").unwrap();
        assert!(output.contains("Litex.functionSpaceSingletonOfEmptyDomain"));
        assert_eq!(
            output,
            super::compile_run(&run, &c, "space_singleton_original").unwrap()
        );
    }
}

#[test]
fn space_singleton_preserves_exact_source_and_absence_signature() {
    for source in [GUARD, CARRIER] {
        let (mut run, c) = super::execute(source);
        let p = selected(&mut run);
        let s = match &mut p.domain_empty {
            Empty::GuardExclusion(p) => &mut p.signature,
            Empty::ParameterCarrier(p) => &mut p.signature,
        };
        s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        reject(&run, &c, "absence_signature");
    }
}

#[test]
fn space_singleton_preserves_original_binder_identity_even_if_both_signatures_change() {
    let (mut run, c) = super::execute(CARRIER);
    let p = selected(&mut run);
    p.signature.set_bound_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
    let Empty::ParameterCarrier(empty) = &mut p.domain_empty else {
        panic!()
    };
    empty.signature = p.signature.clone();
    reject(&run, &c, "changed_both_signature_binders");
}

#[test]
fn space_singleton_cannot_drop_original_guards_from_both_signatures() {
    let (mut run, c) = super::execute(GUARD);
    let p = selected(&mut run);
    p.signature.dom_facts.clear();
    let Empty::GuardExclusion(empty) = &mut p.domain_empty else {
        panic!()
    };
    empty.signature = p.signature.clone();
    reject(&run, &c, "changed_both_signature_guards");
}

#[test]
fn space_singleton_requires_original_carrier_equality_path() {
    let (mut run, c) = super::execute(ALIAS);
    let Empty::ParameterCarrier(p) = &mut selected(&mut run).domain_empty else {
        panic!()
    };
    assert!(!p.carrier_equal.path.is_empty());
    p.carrier_equal.path.clear();
    reject(&run, &c, "missing_carrier_transport");
}

#[test]
fn space_singleton_exclusion_replays_exact_ambient_equality_citations() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::EqualFactSearchedProofByEquivalenceClass as Known;
    for future in [false, true] {
        let (mut run, c) = super::execute(AMBIENT_GUARD);
        super::compile_run(&run, &c, "ambient_exclusion_original").unwrap();
        let future_id = equality(&mut run).fact.fact_id;
        let Empty::GuardExclusion(p) = &mut selected(&mut run).domain_empty else {
            panic!()
        };
        let VerifyFactResult::ForallFact(result) = p.exclusion.as_mut() else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
            result.as_mut()
        else {
            panic!()
        };
        let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByEquivalenceClass(Known::KnownPath(path)) =
            &mut p.searched_proof
        else {
            panic!("original ambient equality path")
        };
        assert!(!path.path.is_empty());
        path.path[0].2 = if future {
            future_id
        } else {
            FactId::new(9_029_002)
        };
        reject(&run, &c, "exclusion_ambient_citation");
    }
}

#[test]
fn space_singleton_rejects_nonempty_or_wrong_equation_endpoint() {
    let (mut run, c) = super::execute(CARRIER);
    equality(&mut run).fact.right = Obj::StandardSet(StandardSet::R);
    reject(&run, &c, "wrong_empty_endpoint");
}

#[test]
fn space_singleton_requires_original_endpoint_formation() {
    let (mut run, c) = super::execute(GUARD);
    let p = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut p.left, &mut p.right);
    reject(&run, &c, "parent_graph_formation");
}

#[test]
fn space_singleton_requires_original_excluded_guard_and_local_conclusion() {
    for change in ["index", "conclusion"] {
        let (mut run, c) = super::execute(GUARD);
        let Empty::GuardExclusion(p) = &mut selected(&mut run).domain_empty else {
            panic!()
        };
        if change == "index" {
            p.excluded_guard_index = usize::MAX;
        } else {
            let VerifyFactResult::ForallFact(result) = p.exclusion.as_mut() else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                result.as_mut()
            else {
                panic!()
            };
            p.proved_then_facts.clear();
        }
        reject(&run, &c, change);
    }
}

#[test]
fn space_singleton_validates_actual_parameter_carrier_evidence() {
    for change in ["group", "variant", "subject"] {
        let (mut run, c) = super::execute(CARRIER);
        let Empty::ParameterCarrier(p) = &mut selected(&mut run).domain_empty else {
            panic!()
        };
        match change {
            "group" => p.parameter_group_index = usize::MAX,
            "variant" => p.evidence = Carrier::EmptyIntegerRange,
            _ => p.empty_carrier = Obj::StandardSet(StandardSet::R),
        }
        reject(&run, &c, change);
    }
}

#[test]
fn space_singleton_borrows_only_its_actual_exclusion_child_after_endpoint_wd() {
    let (mut run, _) = super::execute(GUARD);
    let statement = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let result = &statement.proved_then_facts.last().unwrap().verify_result;
    let VerifyFactResult::Equality(eq) = result else {
        panic!()
    };
    let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyDomainFunctionSpaceSingleton(p),
    ) = &eq.searched_proof
    else {
        panic!()
    };
    let Empty::GuardExclusion(p) = &p.domain_empty else {
        panic!()
    };
    let position = SourcePosition::new(None, SourceOwner::Verify(result), 2);
    let prior = position
        .function_domain_empty_verify_prior(&p.exclusion)
        .unwrap();
    assert_eq!(prior.before, 2);
    assert!(position.function_domain_empty_verify_prior(result).is_err());
}

#[test]
fn space_singleton_does_not_prove_arbitrary_nonempty_function_graphs_empty() {
    for source in ["fn(x R) R={{}}\n", "fn(x R:x=x) R={{}}\n"] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}

#[test]
fn space_singleton_requires_exact_original_space_subject() {
    let (mut run, c) = super::execute(CARRIER);
    selected(&mut run).source_space = Obj::StandardSet(StandardSet::R);
    reject(&run, &c, "wrong_source_space");
}

#[test]
fn space_singleton_validates_cart_zero_canonical_signature() {
    for change in ["return", "domain", "arity", "guards"] {
        let (mut run, c) = super::execute(FINITE);
        let p = selected(&mut run);
        match change {
            "return" => p.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            "domain" => {
                p.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "arity" => p.signature.set_bound_parameters.groups[0].params.clear(),
            _ => {
                let (mut other, _) = super::execute(GUARD);
                p.signature.dom_facts = selected(&mut other).signature.dom_facts.clone();
            }
        }
        let Empty::ParameterCarrier(empty) = &mut p.domain_empty else {
            panic!()
        };
        empty.signature = p.signature.clone();
        reject(&run, &c, change);
    }
}

#[test]
fn space_singleton_replays_all_space_wrappers_and_empty_literal_kinds() {
    for source in [
        "cart()={tuple()}\n",
        "finite_seq(R,0)={{}}\n",
        "finite_seq({},0)={tuple()}\n",
        "matrix(R,0,2)={{}}\n",
        "matrix({},2,0)={tuple()}\n",
        "fn(x {}) {}={{}}\n",
        "forall B set:\n    fn(x R+:x!=x) B={tuple()}\n",
    ] {
        let (mut run, c) = super::execute(source);
        selected(&mut run);
        super::compile_run(&run, &c, "space_wrappers").unwrap();
    }
}

#[test]
fn space_singleton_cannot_replace_guard_exclusion_with_siblings_child() {
    let (mut run, c) = super::execute(&format!("{AMBIENT_GUARD}\n{GUARD}"));
    let (first, rest) = run.statement_results.split_at_mut(1);
    let first = super::forall_proof_mut(&mut first[0]);
    let first =
        super::equality_proof_mut(&mut first.proved_then_facts.last_mut().unwrap().verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyDomainFunctionSpaceSingleton(a),
    ) = &mut first.searched_proof
    else {
        panic!()
    };
    let second = super::forall_proof_mut(&mut rest[0]);
    let second =
        super::equality_proof_mut(&mut second.proved_then_facts.last_mut().unwrap().verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyDomainFunctionSpaceSingleton(b),
    ) = &mut second.searched_proof
    else {
        panic!()
    };
    let (Empty::GuardExclusion(a), Empty::GuardExclusion(b)) =
        (&mut a.domain_empty, &mut b.domain_empty)
    else {
        panic!()
    };
    std::mem::swap(&mut a.exclusion, &mut b.exclusion);
    reject(&run, &c, "sibling_guard_exclusion");
}

const NESTED: &str = "forall source_x R:\n    source_x=source_x\nforall B set:\n    fn(target_y R:target_y!=target_y) B={{}}\n";
const PRIVATE: &str = "forall source_x R:\n    source_x=source_x\nforall private_tag R:\n    forall private_x R:\n        private_x=private_x\n    =>:\n        private_tag=private_tag\nforall B set:\n    fn(target_y R:target_y!=target_y) B={{}}\n";

fn reused_exclusion(run: &mut RunLitexCodeResult) -> &mut VerifyKnownForallFactProof {
    let Empty::GuardExclusion(p) = &mut selected(run).domain_empty else {
        panic!()
    };
    let VerifyFactResult::ForallFact(p) = p.exclusion.as_mut() else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) = p.as_mut()
    else {
        panic!("actual known-forall exclusion")
    };
    p
}

#[test]
fn space_singleton_known_exclusion_keeps_exact_citation_mapping_and_formation() {
    for mutation in ["missing", "future", "map", "formation"] {
        let (mut run, c) = super::execute(NESTED);
        super::compile_run(&run, &c, "known_exclusion_original").unwrap();
        let future = equality(&mut run).fact.fact_id;
        let p = reused_exclusion(&mut run);
        match mutation {
            "missing" => p.cite_fact_id = FactId::new(9_032_001),
            "future" => p.cite_fact_id = future,
            "map" => p.parameter_renamings[0].target = IdentifierId::new(9_032_002),
            _ => p.well_defined.as_detailed_mut().unwrap().then.clear(),
        }
        reject(&run, &c, mutation);
    }
}

#[test]
fn space_singleton_known_exclusion_rejects_matching_stored_private_forall() {
    let (mut run, c) = super::execute(PRIVATE);
    super::compile_run(&run, &c, "known_private_original").unwrap();
    let sibling = super::forall_proof_mut(&mut run.statement_results[1]);
    let StoreFactResult::ForallFact(store) = &sibling.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!()
    };
    let foreign_id = store.fact_id;
    let foreign_binder = store.fact.typed_parameters.groups[0].params[0].id;
    let p = reused_exclusion(&mut run);
    p.cite_fact_id = foreign_id;
    p.parameter_renamings[0].source = foreign_binder;
    reject(&run, &c, "matching_private_forall");
}
