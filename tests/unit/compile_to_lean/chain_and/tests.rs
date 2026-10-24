use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    ForallConclusionArgMatchProof, SearchProofByKnownForallFact, StrictEqualArgProof,
};
use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{ChainTransitiveCite, InferAtomicFactResult, InferResult};
use crate::store_fact_and_infer::{
    InferInFactResult, InferLessEqualFactResult, InferLessFactResult,
};

const ENDPOINT: &str = "have x R=2\nhave y R=x+1\ny=x+1=3\ny^2=9\n";
const ORDER: &str = "forall a,b,c R:\n    a<=b<c\n    =>:\n        a<c\n";
const INFER_SEED: &str = "forall a,b,k C:\n    k!=0\n    a*k=b*k=0\n    =>:\n        a=b\n";
const WEAK_BOUND: &str = "forall x Z:\n    1<=x\n    =>:\n        x $in N\n";
const STRICT_BOUND: &str = "forall b,x R:\n    0<=b\n    b<x\n    =>:\n        0<x\n";
const WHOLE_CHAIN: &str = "forall t R:\n    t=t=t\nhave x R=2\nx=x=x\n";
const WHOLE_AND: &str = "forall t R:\n    t=t and t=t\nhave x R=2\nx=2 and 2=x\n";

fn whole_known_mut(statement: &mut ExecStmtResult) -> &mut SearchProofByKnownForallFact {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("successful source fact")
    };
    match &mut proof.verify_result {
        VerifyFactResult::ChainFact(proof) => {
            let VerifyChainFactResult::Success(proof) = proof.as_mut() else {
                panic!("successful chain")
            };
            assert!(proof.adjacent.is_empty());
            proof
                .known_forall
                .as_mut()
                .expect("selected whole-known chain")
        }
        VerifyFactResult::AndFact(proof) => {
            let VerifyAndFactResult::Success(proof) = proof.as_mut() else {
                panic!("successful conjunction")
            };
            assert!(proof.components.is_empty());
            proof
                .known_forall
                .as_mut()
                .expect("selected whole-known conjunction")
        }
        _ => panic!("actual flat compound family"),
    }
}

#[test]
fn chain_and_replays_selected_whole_forall_location_requirements_and_rebound_equalities() {
    for source in [
        WHOLE_CHAIN,
        WHOLE_AND,
        "forall t R:\n    t=t\n    t=t=t\nhave x R=2\nx=x=x\n",
        "forall t R:\n    t>=0\n    =>:\n        0<=t=t\nhave x R=2\nx>=0\n0<=x=x\n",
    ] {
        let (mut result, compiler) = super::execute(source);
        let capture = whole_known_mut(result.statement_results.last_mut().unwrap());
        assert_eq!(
            capture
                .instantiation_requirements
                .param_type_requirements
                .len(),
            1
        );
        let output = super::compile_run(&result, &compiler, "whole_compound").unwrap();
        assert!(output.contains("And.intro") && output.contains("Eq.trans"));
        assert!(!output.contains("sorry"));
    }
}

#[test]
fn chain_and_whole_forall_rejects_location_order_subjects_and_matching_capture_corruption() {
    for source in [WHOLE_CHAIN, WHOLE_AND] {
        for mutation in ["location", "arity", "bound", "previous", "type"] {
            let (mut result, compiler) = super::execute(source);
            let proof = whole_known_mut(&mut result.statement_results[2]);
            match mutation {
                "location" => {
                    let ForallConclusionLocation::DirectThenFact(location) =
                        &mut proof.cite.location
                    else {
                        panic!("direct whole conclusion")
                    };
                    location.then_fact_index = 99;
                }
                "arity" => {
                    proof.arg_match_proofs.pop();
                }
                "bound" => {
                    let ForallConclusionArgMatchProof::BoundParam { goal_arg, .. } =
                        &mut proof.arg_match_proofs[0]
                    else {
                        panic!("original first binder")
                    };
                    *goal_arg = super::number_object("7");
                }
                "previous" => {
                    let ForallConclusionArgMatchProof::ReboundParamEqual { previous, .. } =
                        &mut proof.arg_match_proofs[1]
                    else {
                        panic!("original repeated binder")
                    };
                    *previous = super::number_object("7");
                }
                "type" => {
                    let Fact::AtomicFact(AtomicFact::InFact(member)) =
                        &mut proof.instantiation_requirements.param_type_requirements[0].type_fact
                    else {
                        panic!("real type requirement")
                    };
                    member.set = Obj::StandardSet(StandardSet::C);
                }
                _ => unreachable!(),
            }
            super::compile_run(&result,&compiler,"wrong_whole_capture").expect_err("whole application requires the exact original location, order, subjects and equality certificate");
        }
    }
}

#[test]
fn chain_and_whole_forall_denies_future_application_truth_and_instantiates_callee_constructor_wd() {
    let (mut result, compiler) = super::execute(WHOLE_CHAIN);
    let known = whole_known_mut(&mut result.statement_results[2]);
    let pending = SourcePosition::new(None, SourceOwner::KnownApplication(known), 0);
    let id = known.instantiation_requirements.param_type_requirements[0]
        .type_fact
        .fact_id();
    let error = pending.visible_fact(id, &compiler.runtime).unwrap_err();
    assert_eq!(error.route, "CompoundKnown/FutureRequirement");
    let completed = SourcePosition {
        before: known.arg_match_proofs.len() + 1,
        ..pending
    };
    assert_eq!(
        completed.visible_fact(id, &compiler.runtime).unwrap().1,
        format!("h_{}", id.value())
    );

    let source = "forall t R:\n    t=t+0=t\nhave x R=2\nx=x+0=x\n";
    let (mut result, compiler) = super::execute(source);
    let member_id = whole_known_mut(&mut result.statement_results[2])
        .instantiation_requirements
        .param_type_requirements[0]
        .type_fact
        .fact_id();
    let output = super::compile_run(&result, &compiler, "instantiated_whole_constructor").unwrap();
    assert!(output.contains("(fun {") && output.contains("Type _") && output.contains("Litex.add"));
    assert!(output.contains(&format!("have h_{} : Litex.In", member_id.value())));
    assert!(!output.contains("sorry"));
}

#[test]
fn callee_constructor_factory_rejects_missing_and_wrong_original_formation() {
    let source = "forall t R:\n    t=t+0=t\nhave x R=2\nx=x+0=x\n";
    for missing in [true, false] {
        let (mut result, compiler) = super::execute(source);
        let callee = super::forall_proof_mut(&mut result.statement_results[0]);
        let VerifyFactResult::ChainFact(proof) = &mut callee.proved_then_facts[0].verify_result
        else {
            panic!("source chain")
        };
        let VerifyChainFactResult::Success(proof) = proof.as_mut() else {
            panic!("successful source chain")
        };
        let original = &mut super::equality_proof_mut(&mut proof.adjacent[0])
            .well_defined_proof
            .right;
        if missing {
            *original = ObjWellDefinedProof::ByKnown {
                obj: original.obj().clone(),
                wd_id: WellDefinednessId::new(u64::MAX),
            };
        } else {
            let ObjWellDefinedProof::ByDef { obj, .. } = original else {
                panic!("original add constructor")
            };
            *obj = super::number_object("7");
        }
        super::compile_run(&result, &compiler, "wrong_callee_constructor")
            .expect_err("factory cannot invent or relabel the callee's source constructor");
    }
}

#[test]
fn callee_constructor_factory_requires_exact_caller_parameter_and_wd_evidence() {
    let source = "forall t R:\n    t=t+0=t\nhave x R=2\nx=x+0=x\n";
    for mutation in ["parameter", "argument", "carrier"] {
        let (mut result, compiler) = super::execute(source);
        let capture = whole_known_mut(&mut result.statement_results[2]);
        let requirement = &mut capture.instantiation_requirements.param_type_requirements[0];
        match mutation {
            "parameter" => requirement.param_id = IdentifierId::new(u64::MAX),
            "argument" => requirement.arg = super::number_object("7"),
            "carrier" => {
                let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut requirement.type_fact
                else {
                    panic!("original real membership")
                };
                member.set = Obj::StandardSet(StandardSet::C);
                let AtomicFact::InFact(member) =
                    &mut super::atomic_proof_mut(&mut requirement.proof).fact
                else {
                    panic!("verified membership")
                };
                member.set = Obj::StandardSet(StandardSet::C);
            }
            "wd" => {
                let wd = &mut super::atomic_proof_mut(&mut requirement.proof)
                    .well_defined_proof
                    .well_defined_of_each_parameter[0];
                *wd = ObjWellDefinedProof::ByKnown {
                    obj: wd.obj().clone(),
                    wd_id: WellDefinednessId::new(u64::MAX),
                };
            }
            _ => unreachable!(),
        }
        super::compile_run(&result, &compiler, "wrong_caller_constructor_evidence").expect_err(
            "callee formation requires the exact recorded caller parameter, carrier and WD proofs",
        );
    }
}

#[test]
fn callee_constructor_factory_rejects_a_constructor_moved_to_a_future_then() {
    let source = "forall t R:\n    t=t+0=t\n    t+0=t\nhave x R=2\nx=x+0=x\n";
    let (mut result, compiler) = super::execute(source);
    let callee = super::forall_proof_mut(&mut result.statement_results[0]);
    let (first, later) = callee.proved_then_facts.split_at_mut(1);
    let VerifyFactResult::ChainFact(proof) = &mut first[0].verify_result else {
        panic!("source chain")
    };
    let VerifyChainFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful source chain")
    };
    let first = &mut super::equality_proof_mut(&mut proof.adjacent[0])
        .well_defined_proof
        .right;
    let later = &mut super::equality_proof_mut(&mut later[0].verify_result)
        .well_defined_proof
        .left;
    assert!(matches!(first, ObjWellDefinedProof::ByDef { .. }));
    assert!(matches!(later, ObjWellDefinedProof::ByDef { .. }));
    assert_eq!(first.obj().ir(), later.obj().ir());
    std::mem::swap(first, later);
    // This source actually returns fresh ByDef evidence in both then facts.
    // Move the selected constructor to the later then and delete the selected
    // formation closure rather than fabricating a cache certificate.
    proof.adjacent.clear();
    // Bypass recompiling the earlier declaration so this specifically checks
    // the factory's original prefix, not only the ordinary declaration gate.
    let caller = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(goal)) = &result.statement_results[2]
    else {
        panic!("goal")
    };
    let VerifyFactResult::ChainFact(goal) = &goal.verify_result else {
        panic!("chain")
    };
    let VerifyChainFactResult::Success(goal) = goal.as_ref() else {
        panic!("successful goal")
    };
    let capture = goal.known_forall.as_ref().expect("selected known forall");
    let error = compiler
        .compile_known_application(&Fact::ChainFact(goal.fact.clone()), capture, &caller)
        .unwrap_err();
    assert_eq!(error.route, "WD/CalleeProducer", "{error}");
}

#[test]
fn callee_constructor_factory_reuses_inner_formation_without_foreign_requirement_truth() {
    let source = "forall s R:\n    s=s=s\nforall t R:\n    t+0=t+0=t+0\n";
    let (mut result, compiler) = super::execute(source);
    let callee = super::forall_proof_mut(&mut result.statement_results[1]);
    let VerifyFactResult::ChainFact(proof) = &callee.proved_then_facts[0].verify_result else {
        panic!("source chain")
    };
    let VerifyChainFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful source chain")
    };
    assert!(proof.adjacent.is_empty());
    let inner = proof
        .known_forall
        .as_ref()
        .expect("original inner whole-known route");
    let foreign = inner.instantiation_requirements.param_type_requirements[0]
        .type_fact
        .fact_id();
    let pattern = proof.fact.objs[0].clone();
    let source_id = callee.fact.fact_id;
    let caller = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let actual = caller
        .with_visible_forall_constructor(source_id, 0, &pattern, &mut |_, _, _, wd, site, _| {
            let error = site.visible_fact(foreign, &compiler.runtime).unwrap_err();
            assert_eq!(error.route, "CompoundKnown/FutureRequirement");
            compiler.compile_wd(wd, site)
        })
        .unwrap()
        .expect("actual caller type-check captured the original addition WD");
    assert!(actual.contains("Litex.add"));
    super::compile_run(&result, &compiler, "inner_header_closure")
        .expect("the real captured constructor needs only the original header");
}

#[test]
fn callee_constructor_factory_does_not_publish_pending_domain_truth_to_argument_matching() {
    let source = "forall t R:\n    t=t\n    =>:\n        t=t+0=t\nhave x R=2\nx=x+0=x\n";
    let (mut result, compiler) = super::execute(source);
    let proof = whole_known_mut(&mut result.statement_results[2]);
    let future = proof.instantiation_requirements.dom_facts[0].fact_id();
    let ForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        &mut proof.arg_match_proofs[1]
    else {
        panic!("original add match")
    };
    let ForallConclusionArgMatchProof::ReboundParamEqual {
        previous,
        goal_arg,
        equal,
        ..
    } = &mut child_matches[0]
    else {
        panic!("original repeated parameter")
    };
    equal.equal_proof = StrictEqualArgProof::ByEquivalenceClass(
        KnownEqualityPathProof::new(vec![(previous.clone(), goal_arg.clone(), future)]).into(),
    );
    let error = super::compile_run(&result, &compiler, "future_requirement_in_match").unwrap_err();
    assert_eq!(error.route, "CompoundKnown/FutureRequirement");
}

#[test]
fn projected_chain_publication_preserves_nested_future_inference_ceiling() {
    let source = "have Interval set={x R:0<=x<=1}\n(1/2) $in Interval\nforall x Interval:\n    0<=x<=1\nInterval $subset R\n";
    let (mut result, compiler) = super::execute(source);
    let forall = super::forall_proof_mut(&mut result.statement_results[2]);
    let member = &forall
        .introduced_params
        .defined_params
        .store_and_infer_results[0];
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &member.infer else {
        panic!("original member inference")
    };
    let projections = rules
        .iter()
        .find_map(|rule| match rule {
            InferInFactResult::SetBuilder(proof) => Some(proof),
            _ => None,
        })
        .expect("actual set-builder projection");
    let projected = &projections.steps[0].projections[1].stored().store;
    let StoreFactResult::ChainFact(stored) = projected else {
        panic!("projected chain store")
    };
    assert_eq!(projected.stored_fact_ids().len(), 3);
    let outer = SourcePosition::new(None, SourceOwner::Forall(forall), 1);
    let pending = SourcePosition::new(Some(&outer), SourceOwner::PropInference(member), 1);
    for edge in &stored.adjacent {
        assert_eq!(
            pending
                .visible_fact(edge.fact_id, &compiler.runtime)
                .unwrap_err()
                .route,
            "Inference/FutureProducer"
        );
    }
    let published = SourcePosition {
        before: 2,
        ..pending
    };
    for edge in &stored.adjacent {
        published
            .visible_fact(edge.fact_id, &compiler.runtime)
            .expect("adjacent stores are published with the chain");
    }
    let ids: Vec<_> = stored.adjacent.iter().map(|edge| edge.fact_id).collect();
    let output = super::compile_run(&result, &compiler, "projected_chain_publication").unwrap();
    for id in ids {
        assert!(output.contains(&format!("have h_{} :", id.value())));
    }
}

enum OrderRuleMut<'a> {
    Strict(&'a mut crate::store_fact_and_infer::InferStrictLowerBoundPositiveResult),
    Weak(&'a mut crate::store_fact_and_infer::InferWeakIntegerLowerBoundInNResult),
}

fn order_rule_mut(statement: &mut ExecStmtResult, strict: bool) -> OrderRuleMut<'_> {
    let proof = super::forall_proof_mut(statement);
    let Some(InferResult::AtomicFact(atomic)) = &mut proof.assumed_dom_facts[usize::from(strict)]
        .store_and_infer
        .infer
    else {
        panic!("actual atomic order inference")
    };
    match atomic {
        InferAtomicFactResult::LessFact(rules) if strict => {
            let [InferLessFactResult::StrictLowerBoundPositive(p)] = rules.as_mut_slice() else {
                panic!("strict rule")
            };
            OrderRuleMut::Strict(p)
        }
        InferAtomicFactResult::LessEqualFact(rules) if !strict => {
            let [InferLessEqualFactResult::WeakIntegerLowerBoundInN(p)] = rules.as_mut_slice()
            else {
                panic!("weak rule")
            };
            OrderRuleMut::Weak(p)
        }
        _ => panic!("matching order family"),
    }
}

#[test]
fn chain_and_replays_conditional_order_and_nested_natural_sign_on_atomic_seeds() {
    for (source, lemma) in [
        (WEAK_BOUND, "Litex.weakIntegerLowerBoundInN"),
        (STRICT_BOUND, "Litex.leLtTrans"),
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "conditional_order").unwrap();
        assert!(output.contains(lemma));
        if source == WEAK_BOUND {
            assert!(output.contains("Litex.naturalNonnegative"));
        }
    }
}

#[test]
fn chain_and_conditional_order_rejects_wrong_seed_certificate_subject_and_wd() {
    for strict in [false, true] {
        for mutation in ["source_id", "bound", "derived"] {
            let (mut result, compiler) =
                super::execute(if strict { STRICT_BOUND } else { WEAK_BOUND });
            let rule = order_rule_mut(&mut result.statement_results[0], strict);
            let (source_id, bound, derived) = match rule {
                OrderRuleMut::Strict(rule) => (
                    &mut rule.source_fact_id,
                    &mut rule.bound_nonnegative_proof,
                    &mut rule.derived,
                ),
                OrderRuleMut::Weak(rule) => (
                    &mut rule.source_fact_id,
                    &mut rule.bound_nonnegative_proof,
                    &mut rule.derived,
                ),
            };
            match mutation {
                "source_id" => *source_id = derived.store.primary_fact_id(),
                "bound" => {
                    let VerifyFactResult::AtomicExceptEquality(bound) = bound else {
                        panic!("atomic bound proof")
                    };
                    let VerifyAtomicExceptEqualityFactResult::Success(bound) = bound.as_mut()
                    else {
                        panic!("successful bound proof")
                    };
                    let AtomicFact::LessEqualFact(bound) = &mut bound.fact else {
                        panic!("zero <= bound")
                    };
                    bound.right = super::number_object("7");
                }
                "derived" => {
                    let StoreFactResult::AtomicFact(stored) = &mut derived.store else {
                        panic!("derived atomic store")
                    };
                    match &mut stored.fact {
                        AtomicFact::InFact(member) => member.set = Obj::StandardSet(StandardSet::Z),
                        AtomicFact::LessFact(fact) => fact.left = super::number_object("7"),
                        _ => panic!("actual conditional conclusion family"),
                    }
                }
                _ => unreachable!(),
            }
            super::compile_run(&result, &compiler, "wrong_order_capture").expect_err("original conditional order certificates must retain source identity, subjects and WD");
        }
    }
}

fn fact_store_mut(statement: &mut ExecStmtResult) -> &mut StoreFactAndInferResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("successful fact")
    };
    &mut proof.store_and_infer_result
}

fn chain_adjacent_mut(statement: &mut ExecStmtResult) -> &mut Vec<VerifyFactResult> {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("successful fact")
    };
    let VerifyFactResult::ChainFact(result) = &mut proof.verify_result else {
        panic!("chain verification")
    };
    let VerifyChainFactResult::Success(proof) = result.as_mut() else {
        panic!("successful chain")
    };
    assert!(
        proof.known_forall.is_none(),
        "this profile exercises the selected adjacent route"
    );
    &mut proof.adjacent
}

#[test]
fn chain_and_replays_endpoint_use_and_flat_component_citations() {
    for source in [
        ENDPOINT,
        "1=1 and 2<3\n1=1\n2<3\n",
        "forall a,b,c C:\n    a=b and b=c\n    =>:\n        a=c\n",
        "have a R\na=a=a\n",
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "compound_replay").unwrap();
        assert!(output.contains("And."));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn chain_and_replays_every_numeric_closure_orientation_and_equality_segment() {
    for (seed, conclusion) in [
        ("a<=b<c", "a<c"),
        ("a<b<=c", "a<c"),
        ("a<b<c", "a<c"),
        ("a<=b<=c", "a<=c"),
        ("a=b<c", "a<c"),
        ("a<b=c", "a<c"),
        ("a>=b>c", "a>c"),
        ("a>b>=c", "a>c"),
        ("a>b>c", "a>c"),
        ("a>=b>=c", "a>=c"),
        ("a=b>c", "a>c"),
        ("a>b=c", "a>c"),
    ] {
        let source = format!("forall a,b,c R:\n    {seed}\n    =>:\n        {conclusion}\n");
        let (result, compiler) = super::execute(&source);
        let output = super::compile_run(&result, &compiler, "numeric_chain")
            .unwrap_or_else(|error| panic!("{seed}: {error}"));
        assert!(output.contains("Litex.lt") || output.contains("Litex.le"));
    }
    let source = "forall a,b,c,d R:\n    a=b=c<d\n    =>:\n        a=c\n        a<d\n";
    let (result, compiler) = super::execute(source);
    let output = super::compile_run(&result, &compiler, "mixed_chain").unwrap();
    assert!(output.contains("Eq.trans"));
    assert!(output.contains("Litex.ltOfSame"));
}

#[test]
fn chain_and_preserves_three_edge_id_domains_and_actual_closure_wd() {
    let (mut result, compiler) = super::execute(ENDPOINT);
    let verified_id =
        super::equality_proof_mut(&mut chain_adjacent_mut(&mut result.statement_results[2])[0])
            .fact
            .fact_id;
    let store = fact_store_mut(&mut result.statement_results[2]);
    let StoreFactResult::ChainFact(stored) = &store.store else {
        panic!("chain store")
    };
    let Some(InferResult::ChainFact(inferred)) = &store.infer else {
        panic!("chain inference")
    };
    let stored_id = stored.adjacent[0].fact_id;
    let inference_id = inferred.adjacent_infers[0].fact.fact_id();
    assert_ne!(verified_id, stored_id);
    assert_ne!(stored_id, inference_id);
    assert_ne!(verified_id, inference_id);
    let closure = &inferred.transitive_closures[0];
    assert!(matches!(closure.cite, ChainTransitiveCite::BuiltinEquality));
    let closure_id = closure.derived.store.primary_fact_id();
    let output = super::compile_run(&result, &compiler, "edge_identity").unwrap();
    for id in [stored_id, inference_id, closure_id] {
        assert!(output.contains(&format!("theorem h_{}", id.value())));
    }
    assert!(!output.contains(&format!("theorem h_{}", verified_id.value())));
}

#[test]
fn chain_and_replays_atomic_inference_from_the_actual_chain_seed() {
    let (mut result, compiler) = super::execute(INFER_SEED);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let store = &forall.assumed_dom_facts[1].store_and_infer;
    let Some(InferResult::ChainFact(inferred)) = &store.infer else {
        panic!("chain inference")
    };
    let source_id = inferred.adjacent_infers[0].fact.fact_id();
    let output = super::compile_run(&result, &compiler, "chain_cancellation").unwrap();
    assert!(output.contains("Litex.mulCancelRightRight"));
    assert!(output.contains(&format!("have h_{}", source_id.value())));
}

#[test]
fn chain_and_rejects_wrong_adjacent_order_wd_and_stored_projection_ids() {
    for change in ["adjacent", "store_id", "store_index"] {
        let (mut result, compiler) = super::execute(ENDPOINT);
        if change == "adjacent" {
            chain_adjacent_mut(&mut result.statement_results[2]).swap(0, 1);
        } else if change == "wd" {
            let proof = super::equality_proof_mut(
                &mut chain_adjacent_mut(&mut result.statement_results[2])[0],
            );
            std::mem::swap(
                &mut proof.well_defined_proof.left,
                &mut proof.well_defined_proof.right,
            );
        } else {
            let StoreFactResult::ChainFact(stored) =
                &mut fact_store_mut(&mut result.statement_results[2]).store
            else {
                panic!("chain store")
            };
            if change == "store_id" {
                stored.adjacent[0].fact_id = stored.adjacent[1].fact_id;
            } else {
                stored.adjacent[0].edge_index = 1;
            }
        }
        super::compile_run(&result, &compiler, "wrong_compound_capture")
            .expect_err("different ordered source evidence cannot be replayed");
    }
    let (mut result, compiler) = super::execute("1=1 and 2<3\n");
    let StoreFactResult::AndFact(stored) =
        &mut fact_store_mut(&mut result.statement_results[0]).store
    else {
        panic!("conjunction store")
    };
    stored.components.swap(0, 1);
    let error = super::compile_run(&result, &compiler, "wrong_and_capture").unwrap_err();
    assert_eq!(error.route, "And/StoreSubject");
}

#[test]
fn chain_and_rejects_changed_inference_seed_subject_and_identity() {
    for change in ["subject", "identity", "index"] {
        let (mut result, compiler) = super::execute(INFER_SEED);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let forbidden = forall
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id();
        let Some(InferResult::ChainFact(inferred)) =
            &mut forall.assumed_dom_facts[1].store_and_infer.infer
        else {
            panic!("chain inference")
        };
        let seed = &mut inferred.adjacent_infers[0];
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &mut seed.fact else {
            panic!("equality seed")
        };
        match change {
            "subject" => equal.right = super::number_object("7"),
            "identity" => equal.fact_id = forbidden,
            "index" => seed.edge_index = 1,
            _ => unreachable!(),
        }
        super::compile_run(&result, &compiler, "wrong_inference_seed")
            .expect_err("the inferred source equality retains its actual subject and identity");
    }
}

#[test]
fn chain_and_rejects_wrong_closure_route_path_subject_and_formation() {
    for change in ["indexes", "rule", "subject", "deleted"] {
        let (mut result, compiler) = super::execute(ORDER);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let Some(InferResult::ChainFact(inferred)) =
            &mut forall.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("chain inference")
        };
        if change == "deleted" {
            inferred.transitive_closures.clear();
        } else {
            let closure = &mut inferred.transitive_closures[0];
            match change {
                "indexes" => closure.premise_edge_indexes.reverse(),
                "rule" => closure.cite = ChainTransitiveCite::BuiltinEquality,
                "subject" => {
                    let StoreFactResult::AtomicFact(stored) = &mut closure.derived.store else {
                        panic!("closure store")
                    };
                    let AtomicFact::LessFact(fact) = &mut stored.fact else {
                        panic!("strict closure")
                    };
                    std::mem::swap(&mut fact.left, &mut fact.right);
                }
                _ => unreachable!(),
            }
        }
        super::compile_run(&result, &compiler, "invalid_closure")
            .expect_err("numeric closure requires every original path and formation stage");
    }
}

#[test]
fn chain_and_scope_cursor_rejects_future_closures_despite_completed_ancestors() {
    let (mut result, compiler) = super::execute(ORDER);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let store = &forall.assumed_dom_facts[0].store_and_infer;
    let Some(InferResult::ChainFact(inferred)) = &store.infer else {
        panic!("chain inference")
    };
    let id = inferred.transitive_closures[0]
        .derived
        .store
        .primary_fact_id();
    let completed_header = SourcePosition::new(None, SourceOwner::Forall(forall), usize::MAX);
    for owner in [
        SourceOwner::CompoundInference(store),
        SourceOwner::PropInference(store),
    ] {
        let pending = SourcePosition::new(
            Some(&completed_header),
            owner,
            inferred.adjacent_infers.len(),
        );
        assert_eq!(
            pending
                .visible_fact(id, &compiler.runtime)
                .unwrap_err()
                .route,
            "Inference/FutureProducer"
        );
        let complete = SourcePosition {
            before: usize::MAX,
            ..pending
        };
        complete
            .visible_fact(id, &compiler.runtime)
            .expect("the exact closure becomes visible after its actual original stage");
    }
}

#[test]
fn chain_and_rejects_a_closure_citation_from_a_closed_prior_scope() {
    let prefix = ORDER.replace("a,b,c R", "a,b,c,closed_marker R");
    let (mut result, compiler) = super::execute(&format!("{prefix}\n{ORDER}"));
    let forbidden = {
        let first = super::forall_proof_mut(&mut result.statement_results[0]);
        let Some(InferResult::ChainFact(inferred)) =
            &first.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("first actual chain inference")
        };
        inferred.transitive_closures[0]
            .derived
            .store
            .primary_fact_id()
    };
    let second = super::forall_proof_mut(&mut result.statement_results[1]);
    let proof = super::atomic_proof_mut(&mut second.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = &mut proof.searched_proof
    else {
        panic!("selected citation of the second scope's actual closure")
    };
    known.cite_fact_id = forbidden;
    let error = super::compile_run(&result, &compiler, "closed_chain_citation")
        .expect_err("an earlier closed chain's local endpoint fact is not an enclosing premise");
    assert_eq!(error.route, "FactId/Resolution");
}
