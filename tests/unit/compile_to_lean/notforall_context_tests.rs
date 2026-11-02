use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
pub(super) const SOURCES65: &[(&str,&str)] = &[
("returned_ternary_counterexample","have fn sc65_return(t R) fn(u,v,w R) R = fn(u,v,w R) R {t+u+v+w}\nsc65_return(1)(0,0,0)=1\nwitness exist sc65_x,sc65_y,sc65_z R st {not sc65_return(1)(sc65_x,sc65_y,sc65_z)=0} from 0,0,0\nnot forall sc65_p,sc65_q,sc65_r R:\n    sc65_return(1)(sc65_p,sc65_q,sc65_r)=0\n"),
("returned_guarded_counterexample","have fn sc65_guard(t R) fn(u,v,w R:u+v>w) R = fn(u,v,w R:u+v>w) R {t+u+v+w}\nsc65_guard(1)(1,1,0)=3\nwitness exist x,y,z R st {x+y>z,not sc65_guard(1)(x,y,z)=0} from 1,1,0\nnot forall x,y,z R:\n    x+y>z\n    =>:\n        sc65_guard(1)(x,y,z)=0\n"),
("returned_three_groups_counterexample","have fn sc65_three(t R) fn(u R) fn(v,w R) R = fn(u R) (fn(v,w R) R) {fn(b,c R) R {t+u+b+c}}\nsc65_three(1)(0)(0,0)=1\nwitness exist x,y,z R st {not sc65_three(1)(x)(y,z)=0} from 0,0,0\nnot forall x,y,z R:\n    sc65_three(1)(x)(y,z)=0\n"),
("returned_heterogeneous_counterexample","have fn sc65_hetero(t R) fn(u R,v R+,w N) R = fn(u R,v R+,w N) R {t+u+v+w}\nsc65_hetero(1)(0,1,0)=2\nwitness exist x R,y R+,z N st {not sc65_hetero(1)(x,y,z)=0} from 0,1,0\nnot forall x R,y R+,z N:\n    sc65_hetero(1)(x,y,z)=0\n"),
("returned_two_conclusions","have fn sc65_return(t R) fn(u,v,w R) R = fn(u,v,w R) R {t+u+v+w}\nsc65_return(1)(0,0,0)=1\nwitness exist x,y,z R st {sc65_return(1)(x,y,z)!=0 or sc65_return(1)(x,y,z)!=2} from 0,0,0\nnot forall p,q,r R:\n    sc65_return(1)(p,q,r)=0\n    sc65_return(1)(p,q,r)=2\n"),
("returned_disjunctive_conclusion","have fn sc65_return(t R) fn(u,v,w R) R = fn(u,v,w R) R {t+u+v+w}\nsc65_return(1)(0,0,0)=1\nwitness exist x,y,z R st {sc65_return(1)(x,y,z)!=0,sc65_return(1)(x,y,z)!=2} from 0,0,0\nnot forall p,q,r R:\n    sc65_return(1)(p,q,r)=0 or sc65_return(1)(p,q,r)=2\n"),
("nonuniversal_premise_inferred_witness","thm sc65_counterexample_from_nonuniversal:\n    ? forall sc65_F fn(t R) fn(u,v,w R) R:\n        not forall p,q,r R:\n            sc65_F(1)(p,q,r)=0\n        =>:\n            exist x,y,z R st {sc65_F(1)(x,y,z)!=0}\n    exist x,y,z R st {sc65_F(1)(x,y,z)!=0}\n"),
];
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::*;
use crate::execute::execute_witness_stmt::*;
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

fn statement65(run: &RunLitexCodeResult, index: usize) -> &ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &run.statement_results[index] else {
        panic!("original successful fact")
    };
    p
}
fn negative65(run: &RunLitexCodeResult) -> &VerifyNotForallFactSuccess {
    let VerifyFactResult::NotForall(p) = &statement65(run, 3).verify_result else {
        panic!("original negated forall")
    };
    let VerifyNotForallFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn plain65(fact: &ExistShapedFact) -> &PlainExistFact {
    let ExistShapedFact::Exist(p) = fact else {
        panic!("original plain counterexample")
    };
    p
}
fn exist65(result: &VerifyFactResult) -> &VerifyPlainExistFactSuccess {
    let VerifyFactResult::ExistShapedFact(p) = result else {
        panic!("original existential child")
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_ref()
    else {
        panic!()
    };
    p
}
fn cite65(result: &VerifyFactResult) -> FactId {
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(p) = &exist65(result).searched_proof
    else {
        panic!("actual winning known-exist route")
    };
    p.cite_fact_id
}
fn witness65(run: &RunLitexCodeResult) -> &ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = &run.statement_results[2]
    else {
        panic!("original concrete witness")
    };
    p
}
fn stored_exist65(store: &StoreFactAndInferResult) -> &ExistShapedFact {
    let StoreFactResult::ExistShapedFact(p) = &store.store else {
        panic!("original existential publication")
    };
    &p.fact
}
fn check_formation65(
    fact: &PlainExistFact,
    wd:&crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof,
) {
    let wd = wd.as_detailed().unwrap();
    let ids = fact.typed_parameters.ordered_param_ids();
    assert_eq!(ids.len(), 3);
    assert_eq!(
        wd.introduced_params
            .defined_params
            .store_and_infer_results
            .len(),
        3
    );
    assert_eq!(wd.assumed_body_facts.len(), fact.facts.len());
    for (clause, assumed) in fact.facts.iter().zip(&wd.assumed_body_facts) {
        let fact = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
        assert_eq!(assumed.store_and_infer.primary_fact_id(), fact.fact_id());
    }
}

#[test]
fn notforall_returned_original_counterexample_witness_alpha_and_body_certificates() {
    for (name, source) in SOURCES65.iter().take(6) {
        let (run, compiler) = super::execute(source);
        assert_eq!(run.statement_results.len(), 4);
        let proof = negative65(&run);
        let derived = plain65(&proof.derived_exist);
        let child = exist65(&proof.prove_derived_exist);
        assert_eq!(child.fact, proof.derived_exist);
        assert_eq!(proof.fact.typed_parameters, derived.typed_parameters);
        assert_ne!(proof.fact.fact_id, derived.fact_id);
        let ids = derived.typed_parameters.ordered_param_ids();
        assert_eq!(ids.len(), 3);
        let expected = usize::from(*name == "returned_guarded_counterexample");
        assert_eq!(proof.fact.dom_facts.len(), expected);
        assert_eq!(derived.facts[..expected], proof.fact.dom_facts);
        assert_eq!(
            derived.facts.len(),
            if *name == "returned_guarded_counterexample"
                || *name == "returned_disjunctive_conclusion"
            {
                2
            } else {
                1
            }
        );
        if *name == "returned_two_conclusions" {
            assert_eq!(proof.fact.then_facts.len(), 2);
            assert!(matches!(&derived.facts[0], QuantifierFreeFact::OrFact(_)));
        }
        if *name == "returned_disjunctive_conclusion" {
            assert!(matches!(
                &proof.fact.then_facts[0],
                QuantifierFreeFact::OrFact(_)
            ));
        }
        check_formation65(derived, &child.well_defined_proof);
        let witness = witness65(&run);
        let original = plain65(stored_exist65(&witness.store_and_infer_result));
        let source_ids = original.typed_parameters.ordered_param_ids();
        assert!(source_ids.iter().all(|id| !ids.contains(id)));
        assert_eq!(source_ids.len(), ids.len());
        assert_eq!(
            original.typed_parameters.groups.len(),
            derived.typed_parameters.groups.len()
        );
        for (a, b) in original
            .typed_parameters
            .groups
            .iter()
            .zip(&derived.typed_parameters.groups)
        {
            assert_eq!(a.param_type, b.param_type);
            assert_eq!(a.params.len(), b.params.len());
        }
        assert_eq!(cite65(&proof.prove_derived_exist), original.fact_id);
        assert_ne!(original.fact_id, derived.fact_id);
        assert_eq!(original.facts.len(), derived.facts.len());
        assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(original,derived));
        assert_eq!(witness.statement.equal_tos.len(), 3);
        assert_eq!(witness.ambient.witness_obj_well_defined.len(), 3);
        assert_eq!(witness.ambient.witness_type_checks.len(), 3);
        assert_eq!(witness.witness_equalities.len(), 3);
        assert_eq!(
            witness
                .introduced_params
                .defined_params
                .store_and_infer_results
                .len(),
            3
        );
        assert!(witness.proof_steps.is_empty());
        assert_eq!(witness.obligations.body_checks.len(), original.facts.len());
        assert!(witness.obligations.uniqueness_check.is_none());
        for (index, equality) in witness.witness_equalities.iter().enumerate() {
            let StoreFactResult::AtomicFact(p) = &equality.store else {
                panic!()
            };
            let AtomicFact::EqualFact(f) = &p.fact else {
                panic!()
            };
            assert_eq!(
                f.left.ir(),
                Obj::Identifier(IdentifierObj::from_bound_name(
                    original
                        .typed_parameters
                        .groups
                        .iter()
                        .flat_map(|g| &g.params)
                        .nth(index)
                        .unwrap()
                ))
                .ir()
            );
            assert_eq!(f.right.ir(), witness.statement.equal_tos[index].ir());
        }
        let output = compiler.compile_run(&run, "NotForall65Original").unwrap();
        assert!(output.contains("_counterexample"));
        assert!(output.contains(&format!("h_{}", original.fact_id.value())));
        assert!(!output.contains("sorry"));
        eprintln!("ORIGINAL65 {name} NotForall:{} verified_exist:{} cite:{} binders:{} domains:{} negative_clauses:{} witness_body:{}",proof.fact.fact_id.value(),derived.fact_id.value(),original.fact_id.value(),ids.len(),expected,derived.facts.len()-expected,witness.obligations.body_checks.len());
    }
}

#[test]
fn notforall_returned_original_inferred_exist_publication_and_private_boundaries() {
    for (name, source) in SOURCES65.iter().take(6) {
        let (run, compiler) = super::execute(source);
        let proof = negative65(&run);
        let child = exist65(&proof.prove_derived_exist);
        let Some(InferResult::NotForall(infer)) =
            &statement65(&run, 3).store_and_infer_result.infer
        else {
            panic!("original inference capture")
        };
        let StoreFactResult::ExistShapedFact(inferred) = &infer.derived_exist.store else {
            panic!()
        };
        let inferred = plain65(&inferred.fact);
        let derived = plain65(&proof.derived_exist);
        assert_ne!(inferred.fact_id, derived.fact_id);
        assert_ne!(inferred.fact_id, proof.fact.fact_id);
        assert_eq!(inferred.typed_parameters, derived.typed_parameters);
        assert_eq!(inferred.facts.len(), derived.facts.len());
        for (a, b) in inferred.facts.iter().zip(&derived.facts) {
            assert_eq!(a.ir(), b.ir());
        }
        let before = SourcePosition::new(None, SourceOwner::Run(&run), 3);
        let after = SourcePosition {
            before: 4,
            ..before
        };
        assert!(compiler
            .cited_fact_reference(inferred.fact_id, &before)
            .is_err());
        assert!(compiler
            .cited_fact_reference(inferred.fact_id, &after)
            .is_ok());
        assert!(compiler
            .cited_fact_reference(derived.fact_id, &after)
            .is_err());
        let wd = child.well_defined_proof.as_detailed().unwrap();
        for p in &wd.introduced_params.defined_params.store_and_infer_results {
            assert!(compiler
                .cited_fact_reference(p.primary_fact_id(), &after)
                .is_err());
        }
        for p in &wd.assumed_body_facts {
            assert!(compiler
                .cited_fact_reference(p.store_and_infer.primary_fact_id(), &after)
                .is_err());
        }
        for p in &witness65(&run).witness_equalities {
            assert!(compiler
                .cited_fact_reference(p.primary_fact_id(), &after)
                .is_err());
        }
        eprintln!(
            "ORIGINAL65 {name} published_inference:{} private_verified:{}",
            inferred.fact_id.value(),
            derived.fact_id.value()
        );
    }
}

#[test]
fn notforall_returned_original_premise_inference_is_the_actual_known_exist_source() {
    let (name, source) = SOURCES65[6];
    let (run, compiler) = super::execute(source);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    let Fact::ForallFact(fact) = &p.statement.fact else {
        panic!()
    };
    let Fact::NotForall(negative) = &fact.dom_facts[0] else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(body) = &p.body else {
        panic!()
    };
    assert_eq!(body.assumed_dom_facts.len(), 1);
    assert_eq!(body.proof_steps.len(), 1);
    assert_eq!(body.conclusion_proofs.len(), 1);
    let Some(InferResult::NotForall(infer)) = &body.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!()
    };
    let StoreFactResult::ExistShapedFact(stored) = &infer.derived_exist.store else {
        panic!()
    };
    let inferred = plain65(&stored.fact);
    assert_eq!(negative.typed_parameters, inferred.typed_parameters);
    assert_ne!(negative.fact_id, inferred.fact_id);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &body.proof_steps[0] else {
        panic!()
    };
    assert_eq!(cite65(&step.verify_result), inferred.fact_id);
    assert_eq!(cite65(&body.conclusion_proofs[0]), inferred.fact_id);
    check_formation65(
        plain65(&exist65(&step.verify_result).fact),
        &exist65(&step.verify_result).well_defined_proof,
    );
    let parent = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let before = SourcePosition::new(Some(&parent), SourceOwner::Named(p), 1);
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(compiler
        .cited_fact_reference(inferred.fact_id, &before)
        .is_err());
    assert!(compiler
        .cited_fact_reference(inferred.fact_id, &after)
        .is_ok());
    let outer = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler
        .cited_fact_reference(inferred.fact_id, &outer)
        .is_err());
    assert!(compiler
        .cited_fact_reference(negative.fact_id, &outer)
        .is_err());
    let output = compiler.compile_run(&run, "NotForall65Premise").unwrap();
    assert!(output.contains(&format!("h_{}", inferred.fact_id.value())));
    eprintln!(
        "ORIGINAL65 {name} premise:{} inferred_cite:{} proof_steps:1 conclusion_proofs:1",
        negative.fact_id.value(),
        inferred.fact_id.value()
    );
}

const PRIVATE65: &str = "have fn sc65_return(t R) fn(u,v,w R) R = fn(u,v,w R) R {t+u+v+w}\nsc65_return(1)(0,0,0)=1\nwitness exist sc65_x,sc65_y,sc65_z R st {not sc65_return(1)(sc65_x,sc65_y,sc65_z)=0} from 0,0,0:\n    witness exist sc65_private_x,sc65_private_y,sc65_private_z R st {sc65_return(1)(sc65_private_x,sc65_private_y,sc65_private_z)!=0} from 0,0,0\nnot forall sc65_p,sc65_q,sc65_r R:\n    sc65_return(1)(sc65_p,sc65_q,sc65_r)=0\n";
const FUTURE65: &str = "have fn sc65_return(t R) fn(u,v,w R) R = fn(u,v,w R) R {t+u+v+w}\nsc65_return(1)(0,0,0)=1\nwitness exist sc65_x,sc65_y,sc65_z R st {not sc65_return(1)(sc65_x,sc65_y,sc65_z)=0} from 0,0,0\nnot forall sc65_p,sc65_q,sc65_r R:\n    sc65_return(1)(sc65_p,sc65_q,sc65_r)=0\nwitness exist sc65_x,sc65_y,sc65_z R st {not sc65_return(1)(sc65_x,sc65_y,sc65_z)=0} from 0,0,0\n";
fn statement65_mut(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[index]
    else {
        panic!()
    };
    p
}
fn negative65_mut(run: &mut RunLitexCodeResult) -> &mut VerifyNotForallFactSuccess {
    let VerifyFactResult::NotForall(p) = &mut statement65_mut(run, 3).verify_result else {
        panic!()
    };
    let VerifyNotForallFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn plain65_mut(fact: &mut ExistShapedFact) -> &mut PlainExistFact {
    let ExistShapedFact::Exist(p) = fact else {
        panic!()
    };
    p
}
fn exist65_mut(result: &mut VerifyFactResult) -> &mut VerifyPlainExistFactSuccess {
    let VerifyFactResult::ExistShapedFact(p) = result else {
        panic!()
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    p
}
fn child65_mut(run: &mut RunLitexCodeResult) -> &mut VerifyPlainExistFactSuccess {
    exist65_mut(&mut negative65_mut(run).prove_derived_exist)
}
fn cite65_mut(child: &mut VerifyPlainExistFactSuccess) -> &mut FactId {
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(p) = &mut child.searched_proof else {
        panic!()
    };
    &mut p.cite_fact_id
}
fn witness65_from_stmt_mut(
    stmt: &mut ExecStmtResult,
) -> &mut ExecWitnessExistFactStmtSuccessResult {
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = stmt
    else {
        panic!()
    };
    p
}
fn witness65_mut(run: &mut RunLitexCodeResult) -> &mut ExecWitnessExistFactStmtSuccessResult {
    witness65_from_stmt_mut(&mut run.statement_results[2])
}
fn theorem65_mut(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    p
}
fn theorem_body65_mut(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_def_thm_stmt::ExecDefThmForallProof {
    let ExecDefThmBodyProof::Forall(p) = &mut theorem65_mut(run).body else {
        panic!()
    };
    p
}
fn reject65(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "NotForall65ChangedEvidence")
        .expect_err("changed original counterexample evidence must reject");
}

#[test]
fn notforall_returned_preserves_plain_counterexample_family_and_distinct_identity() {
    for (_, source) in SOURCES65.iter().take(6) {
        for family in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = negative65_mut(&mut run);
            if family {
                p.derived_exist = ExistShapedFact::ExistUnique(plain65(&p.derived_exist).clone());
            } else {
                plain65_mut(&mut p.derived_exist).fact_id = p.fact.fact_id;
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_preserves_quantified_binder_identities_and_carriers() {
    for (_, source) in SOURCES65.iter().take(6) {
        for id in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = plain65_mut(&mut negative65_mut(&mut run).derived_exist);
            if id {
                p.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
            } else {
                p.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C));
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_preserves_ordered_domains_and_negative_body() {
    for change in [0, 1, 2] {
        let (mut run, compiler) = super::execute(SOURCES65[1].1);
        let p = negative65_mut(&mut run);
        match change {
            0 => p.fact.dom_facts.clear(),
            1 => plain65_mut(&mut p.derived_exist).facts.swap(0, 1),
            _ => {
                plain65_mut(&mut p.derived_exist).facts[1] = p.fact.then_facts[0].clone();
            }
        }
        reject65(&run, &compiler);
    }
    for index in [4, 5] {
        let (mut run, compiler) = super::execute(SOURCES65[index].1);
        let p = negative65_mut(&mut run);
        plain65_mut(&mut p.derived_exist).facts[0] = p.fact.then_facts[0].clone();
        reject65(&run, &compiler);
    }
}
#[test]
fn notforall_returned_requires_exact_derived_exist_verification_subject() {
    for (_, source) in SOURCES65.iter().take(6) {
        for identity in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = plain65_mut(&mut child65_mut(&mut run).fact);
            if identity {
                p.fact_id = FactId::new(u64::MAX);
            } else {
                p.facts.clear();
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_requires_complete_ordered_binder_formation() {
    for (_, source) in SOURCES65.iter().take(6) {
        for change in [0, 1, 2] {
            let (mut run, compiler) = super::execute(source);
            let p = &mut child65_mut(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params;
            match change {
                0 => {
                    p.store_and_infer_results.pop();
                }
                1 => p.stored_fact_ids.clear(),
                _ => p.store_and_infer_results.swap(0, 1),
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_requires_complete_ordered_body_formation() {
    for (index, source) in SOURCES65.iter().take(6).enumerate() {
        let (mut run, compiler) = super::execute(source.1);
        child65_mut(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .assumed_body_facts
            .pop();
        reject65(&run, &compiler);
        if index == 1 || index == 5 {
            let (mut run, compiler) = super::execute(source.1);
            child65_mut(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .swap(0, 1);
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_requires_the_original_visible_known_exist_source() {
    for (_, source) in SOURCES65.iter().take(6) {
        for kind in [0, 1, 2] {
            let (mut run, compiler) = super::execute(source);
            let p = negative65(&run);
            let wrong = match kind {
                0 => FactId::new(u64::MAX),
                1 => p.fact.fact_id,
                _ => plain65(&p.derived_exist).fact_id,
            };
            assert_ne!(wrong, cite65(&p.prove_derived_exist));
            *cite65_mut(child65_mut(&mut run)) = wrong;
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_rejects_a_future_mathematically_matching_witness() {
    let (mut run, compiler) = super::execute(FUTURE65);
    compiler
        .compile_run(&run, "NotForall65FuturePristine")
        .unwrap();
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(p),
    )) = &run.statement_results[4]
    else {
        panic!()
    };
    let future = plain65(stored_exist65(&p.store_and_infer_result));
    let derived = plain65(&negative65(&run).derived_exist);
    assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(future,derived));
    let wrong = future.fact_id;
    assert_ne!(wrong, cite65(&negative65(&run).prove_derived_exist));
    *cite65_mut(child65_mut(&mut run)) = wrong;
    reject65(&run, &compiler);
}
#[test]
fn notforall_returned_rejects_a_closed_private_mathematically_matching_witness() {
    let (mut run, compiler) = super::execute(PRIVATE65);
    compiler
        .compile_run(&run, "NotForall65PrivatePristine")
        .unwrap();
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(inner),
    )) = &witness65(&run).proof_steps[0]
    else {
        panic!()
    };
    let private = plain65(stored_exist65(&inner.store_and_infer_result));
    let derived = plain65(&negative65(&run).derived_exist);
    assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(private,derived));
    let wrong = private.fact_id;
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 4);
    assert!(compiler.cited_fact_reference(wrong, &after).is_err());
    *cite65_mut(child65_mut(&mut run)) = wrong;
    reject65(&run, &compiler);
}
#[test]
fn notforall_returned_requires_its_exact_inferred_exist_capture() {
    for (_, source) in SOURCES65.iter().take(6) {
        for change in [0, 1, 2] {
            let (mut run, compiler) = super::execute(source);
            let store = &mut statement65_mut(&mut run, 3).store_and_infer_result;
            if change == 0 {
                store.infer = None;
            } else {
                let Some(InferResult::NotForall(p)) = &mut store.infer else {
                    panic!()
                };
                let StoreFactResult::ExistShapedFact(p) = &mut p.derived_exist.store else {
                    panic!()
                };
                if change == 1 {
                    p.whole_fact_id = FactId::new(u64::MAX);
                } else {
                    plain65_mut(&mut p.fact).facts.clear();
                }
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_requires_every_original_witness_stage() {
    for (_, source) in SOURCES65.iter().take(6) {
        for stage in [0, 1, 2, 3, 4] {
            let (mut run, compiler) = super::execute(source);
            let p = witness65_mut(&mut run);
            match stage {
                0 => {
                    p.ambient.witness_obj_well_defined.pop();
                }
                1 => {
                    p.ambient.witness_type_checks.pop();
                }
                2 => {
                    p.introduced_params
                        .defined_params
                        .store_and_infer_results
                        .pop();
                }
                3 => {
                    p.witness_equalities.pop();
                }
                _ => {
                    p.obligations.body_checks.pop();
                }
            }
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_preserves_each_witness_equality_subject() {
    for (_, source) in SOURCES65.iter().take(6) {
        for index in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let StoreFactResult::AtomicFact(p) =
                &mut witness65_mut(&mut run).witness_equalities[index].store
            else {
                panic!()
            };
            let AtomicFact::EqualFact(f) = &mut p.fact else {
                panic!()
            };
            assert_ne!(f.left.ir(), f.right.ir());
            f.left = f.right.clone();
            reject65(&run, &compiler);
        }
    }
}
#[test]
fn notforall_returned_preserves_the_original_witness_argument_identity() {
    let (mut run, compiler) = super::execute(SOURCES65[3].1);
    let p = witness65_mut(&mut run);
    assert_ne!(p.statement.equal_tos[0].ir(), p.statement.equal_tos[1].ir());
    p.statement.equal_tos.swap(0, 1);
    reject65(&run, &compiler);
}
#[test]
fn notforall_returned_requires_the_exact_substituted_witness_body_proof() {
    for (_, source) in SOURCES65.iter().take(6) {
        let (mut run, compiler) = super::execute(source);
        let (mut donor, _) = super::execute(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(replacement)) =
            donor.statement_results.remove(1)
        else {
            panic!()
        };
        witness65_mut(&mut run).obligations.body_checks[0] = replacement.verify_result;
        reject65(&run, &compiler);
    }
}
#[test]
fn notforall_returned_requires_original_premise_inference_capture() {
    for change in [0, 1, 2] {
        let (mut run, compiler) = super::execute(SOURCES65[6].1);
        let store = &mut theorem_body65_mut(&mut run).assumed_dom_facts[0].store_and_infer;
        if change == 0 {
            store.infer = None;
        } else {
            let Some(InferResult::NotForall(p)) = &mut store.infer else {
                panic!()
            };
            let StoreFactResult::ExistShapedFact(p) = &mut p.derived_exist.store else {
                panic!()
            };
            if change == 1 {
                p.whole_fact_id = FactId::new(u64::MAX);
            } else {
                plain65_mut(&mut p.fact).typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C));
            }
        }
        reject65(&run, &compiler);
    }
}
#[test]
fn notforall_returned_requires_premise_known_exist_to_cite_its_inferred_source() {
    for wrong_family in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES65[6].1);
        let p = theorem_body65_mut(&mut run);
        let wrong = if wrong_family {
            p.assumed_dom_facts[0].store_and_infer.primary_fact_id()
        } else {
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &p.proof_steps[0] else {
                panic!()
            };
            step.store_and_infer_result.primary_fact_id()
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut p.proof_steps[0] else {
            panic!()
        };
        assert_ne!(cite65(&step.verify_result), wrong);
        *cite65_mut(exist65_mut(&mut step.verify_result)) = wrong;
        reject65(&run, &compiler);
    }
}
#[test]
fn notforall_returned_preserves_original_premise_proof_steps() {
    let (mut run, compiler) = super::execute(SOURCES65[6].1);
    assert_eq!(theorem_body65_mut(&mut run).proof_steps.len(), 1);
    theorem_body65_mut(&mut run).proof_steps.clear();
    reject65(&run, &compiler);
}
