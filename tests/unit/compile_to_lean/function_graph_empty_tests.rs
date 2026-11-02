use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::function_domain::{FunctionDomainEmptyProof as Empty, FunctionDomainEmptyCarrierEvidence as Carrier};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyFunctionGraphBuiltinRuleProof;
use crate::prelude::*;

const GUARD: &str = "forall B set,f fn(x R:x!=x) B:\n    f={}\n";
const CARRIER: &str = "forall B set,f fn(x {}) B:\n    f={}\n";
const REVERSE: &str = "forall B set,f fn(x {}) B:\n    {}=f\n";
const FINITE: &str = "forall p cart():\n    p={}\n";
const RETURNED_GUARD: &str = "forall B set,h fn(t R) fn(x R:x!=x) B,a R:\n    h(a)={}\n";
const ALIAS: &str = "forall A,B set,f fn(x A) B:\n    A={}\n    =>:\n        f={}\n";
const AMBIENT_GUARD: &str =
    "forall a,b R,B set,f fn(x R:a!=b) B:\n    a=b\n    =>:\n        f={}\n";

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
fn selected(run: &mut RunLitexCodeResult) -> &mut EmptyFunctionGraphBuiltinRuleProof {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyFunctionGraph(p),
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
fn graph_empty_replays_original_guard_carrier_finite_and_both_orientations() {
    for source in [GUARD, CARRIER, REVERSE, FINITE] {
        let (mut run, c) = super::execute(source);
        selected(&mut run);
        let output = super::compile_run(&run, &c, "empty_graph_original").unwrap();
        assert!(output.contains("Litex.functionGraphEmptyOfDomainEmpty"));
        assert_eq!(
            output,
            super::compile_run(&run, &c, "empty_graph_original").unwrap()
        );
    }
}

#[test]
fn graph_empty_replays_six_actual_complete_source_variants() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
    let sources = [
        CARRIER,
        FINITE,
        RETURNED_GUARD,
        "fn(x {}) R {0}={}\n",
        "forall B set,f fn(y R) B,g fn(x {}) R:\n    (f ∘ g)={}\n",
        "identity_matrix(0)={}\n",
    ];
    let mut kinds = std::collections::BTreeSet::new();
    for source in sources {
        let (mut run, c) = super::execute(source);
        kinds.insert(match selected(&mut run).source.source {
            S::Membership { .. } => "membership",
            S::FiniteFunction(_) => "finite",
            S::ApplicationReturn { .. } => "returned",
            S::AnonymousFunction { .. } => "anonymous",
            S::Composition(_) => "composition",
            S::Matrix(_) => "matrix",
            _ => panic!("unprofiled original source"),
        });
        super::compile_run(&run, &c, "empty_graph_source_variants").unwrap();
    }
    assert_eq!(kinds.len(), 6);
}

#[test]
fn graph_empty_preserves_exact_source_and_absence_signature() {
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
fn graph_empty_preserves_original_binder_identity_even_if_both_signatures_change() {
    let (mut run, c) = super::execute(CARRIER);
    let p = selected(&mut run);
    p.source.signature.set_bound_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
    let Empty::ParameterCarrier(empty) = &mut p.domain_empty else {
        panic!()
    };
    empty.signature = p.source.signature.clone();
    reject(&run, &c, "changed_both_signature_binders");
}

#[test]
fn graph_empty_cannot_drop_original_guards_from_both_signatures() {
    let (mut run, c) = super::execute(GUARD);
    let p = selected(&mut run);
    p.source.signature.dom_facts.clear();
    let Empty::GuardExclusion(empty) = &mut p.domain_empty else {
        panic!()
    };
    empty.signature = p.source.signature.clone();
    reject(&run, &c, "changed_both_signature_guards");
}

#[test]
fn graph_empty_requires_original_carrier_equality_path() {
    let (mut run, c) = super::execute(ALIAS);
    let Empty::ParameterCarrier(p) = &mut selected(&mut run).domain_empty else {
        panic!()
    };
    assert!(!p.carrier_equal.path.is_empty());
    p.carrier_equal.path.clear();
    reject(&run, &c, "missing_carrier_transport");
}

#[test]
fn graph_empty_exclusion_replays_exact_ambient_equality_citations() {
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
fn graph_empty_original_exclusion_follows_all_returned_application_stages() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
    let (mut run, c) = super::execute(RETURNED_GUARD);
    super::compile_run(&run, &c, "returned_guard_original").unwrap();
    let statement = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let result = &statement.proved_then_facts.last().unwrap().verify_result;
    let VerifyFactResult::Equality(eq) = result else {
        panic!()
    };
    let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyFunctionGraph(p),
    ) = &eq.searched_proof
    else {
        panic!()
    };
    let S::ApplicationReturn {
        application_check, ..
    } = &p.source.source
    else {
        panic!()
    };
    let Empty::GuardExclusion(empty) = &p.domain_empty else {
        panic!()
    };
    let original = application_check.detailed_ref();
    let position = SourcePosition::new(None, SourceOwner::Verify(result), 2);
    let prior = position
        .function_domain_empty_verify_prior(&empty.exclusion)
        .unwrap();
    assert_eq!(
        prior.before,
        2 + original.child_obj_well_defined.len() + original.requirement_fact_verified.len()
    );
}

#[test]
fn graph_empty_requires_complete_returned_application_formation() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
    let (mut run, c) = super::execute(RETURNED_GUARD);
    let S::ApplicationReturn {
        application_check, ..
    } = &mut selected(&mut run).source.source
    else {
        panic!()
    };
    application_check
        .as_detailed_mut()
        .unwrap()
        .child_obj_well_defined
        .pop();
    reject(&run, &c, "returned_source_formation");
}

#[test]
fn graph_empty_cannot_borrow_a_sibling_foralls_private_function_citation() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
    let first_source =
        "forall sibling_f fn(sibling_x R:sibling_x!=sibling_x) R:\n    sibling_f={}\n";
    let (mut run, c) = super::execute(&format!("{first_source}\n{GUARD}"));
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let first =
        super::equality_proof_mut(&mut first.proved_then_facts.last_mut().unwrap().verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EmptyFunctionGraph(first),
    ) = &first.searched_proof
    else {
        panic!()
    };
    let S::Membership { membership, .. } = &first.source.source else {
        panic!()
    };
    let foreign = membership.fact_id;
    let S::Membership { membership, .. } = &mut selected(&mut run).source.source else {
        panic!()
    };
    assert_ne!(foreign, membership.fact_id);
    membership.fact_id = foreign;
    reject(&run, &c, "sibling_function_citation");
}

#[test]
fn graph_empty_needs_original_function_membership_citation() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
    for future in [false, true] {
        let (mut run, c) = super::execute(GUARD);
        let goal_id = equality(&mut run).fact.fact_id;
        let S::Membership { membership, .. } = &mut selected(&mut run).source.source else {
            panic!()
        };
        membership.fact_id = if future {
            goal_id
        } else {
            FactId::new(9_000_029)
        };
        reject(&run, &c, "membership_citation");
    }
}

#[test]
fn graph_empty_rejects_nonempty_or_wrong_equation_endpoint() {
    let (mut run, c) = super::execute(CARRIER);
    equality(&mut run).fact.right = Obj::StandardSet(StandardSet::R);
    reject(&run, &c, "wrong_empty_endpoint");
}

#[test]
fn graph_empty_requires_original_endpoint_formation() {
    let (mut run, c) = super::execute(GUARD);
    let p = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut p.left, &mut p.right);
    reject(&run, &c, "parent_graph_formation");
}

#[test]
fn graph_empty_requires_original_excluded_guard_and_local_conclusion() {
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
fn graph_empty_validates_actual_parameter_carrier_evidence() {
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
fn graph_empty_borrows_only_its_actual_exclusion_child_after_endpoint_wd() {
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
        EqualitySearchProofByBuiltinRule::EmptyFunctionGraph(p),
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
fn graph_empty_does_not_prove_arbitrary_nonempty_function_graphs_empty() {
    for source in [
        "forall f fn(x R) R:\n    f={}\n",
        "forall f fn(x R:x=x) R:\n    f={}\n",
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}
