use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef,
};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
    StoreInferredFactResult,
};
use std::rc::Rc;

const NATURAL_SAME: &str = "prop natural_same(x N):\n    x=x\n";
const NATURAL_CLAUSE: &str =
    "prop natural_pair(x N):\n    x $in N\n    x=x\nby def $natural_pair(1)\n";
const NATURAL_BUILDER: &str = "have NaturalFilter set={x N:x $in N}\n1 $in NaturalFilter\nforall x NaturalFilter:\n    0<=x\n";
const NESTED_NATURAL_BUILDER: &str = "have NaturalFilter set={x N:x $in N}\nhave NestedFilter set={y NaturalFilter:y $in N}\nforall y NestedFilter:\n    0<=y\n";
const DIRECT_STANDARD_N: &str =
    "forall n N:\n    N={x N:x=x}\n    n $in N\n    =>:\n        0<=n\n";

fn statement_store(statement: &ExecStmtResult) -> &StoreFactAndInferResult {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => &proof.store_and_infer_result,
        ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) => {
            &proof.stored
        }
        _ => panic!("an actual stored predicate occurrence"),
    }
}

fn natural_sign_ids(store: &StoreFactAndInferResult) -> Vec<FactId> {
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &store.infer
    else {
        return Vec::new();
    };
    let mut ids = Vec::new();
    for rule in rules {
        match rule {
            InferAtomicExceptEqualityResult::NormalAtomicParamTypes(_) => {}
            InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(_) => {}
            InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(proof) => {
                for derived in &proof.derived {
                    ids.push(derived.store.primary_fact_id());
                }
            }
            InferAtomicExceptEqualityResult::InFactSetBuilder(_) => {}
            _ => {}
        }
    }
    ids
}

fn introduction(statement: &ExecStmtResult) -> &VerifyForallFactSuccess {
    let proof = super::fact_statement(statement);
    let VerifyFactResult::ForallFact(proof) = &proof.verify_result else {
        panic!("an actual quantified proof")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("the original parameter and domain introduction")
    };
    proof
}

fn concrete_prop(statement: &ExecStmtResult) -> &ExecDefPropStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = statement
    else {
        panic!("the actual concrete predicate declaration")
    };
    proof
}

fn concrete_prop_mut(statement: &mut ExecStmtResult) -> &mut ExecDefPropStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = statement
    else {
        panic!("the actual concrete predicate declaration")
    };
    proof
}

fn builder(statement: &ExecStmtResult) -> (&SetBuilder, &SetBuilderObjWellDefinedProof) {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("the actual bounded-set declaration")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        obj: Obj::SetFormer(SetFormer::SetBuilder(set)),
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(wd)),
    }) = &proof.equal_to_well_defined[0]
    else {
        panic!("the original bounded-set formation")
    };
    (set, wd)
}

fn builder_mut(statement: &mut ExecStmtResult) -> &mut SetBuilderObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("the actual bounded-set declaration")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(wd)),
        ..
    }) = &mut proof.equal_to_well_defined[0]
    else {
        panic!("the original bounded-set formation")
    };
    wd
}

fn sign_capture(store: &StoreFactAndInferResult) -> &StoreInferredFactResult {
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &store.infer
    else {
        panic!("the original natural member infer dispatcher")
    };
    rules
        .iter()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) => {
                assert_eq!(sign.derived.len(), 1);
                Some(&sign.derived[0])
            }
            _ => None,
        })
        .expect("the exact natural member sign capture")
}

fn sign_zero(store: &StoreFactAndInferResult) -> &ObjWellDefinedProof {
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &sign_capture(store).well_defined else {
        panic!("the original nonnegative formation")
    };
    &wd.well_defined_of_each_parameter[0]
}

fn sign_formation_mut(store: &mut StoreFactAndInferResult) -> &mut AtomicFactWellDefinedProof {
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &mut store.infer
    else {
        panic!("the original natural member infer dispatcher")
    };
    let sign = rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) => Some(sign),
            _ => None,
        })
        .expect("the exact natural member sign capture");
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut sign.derived[0].well_defined else {
        panic!("the original nonnegative formation")
    };
    wd
}

fn sign_zero_mut(store: &mut StoreFactAndInferResult) -> &mut ObjWellDefinedProof {
    &mut sign_formation_mut(store).well_defined_of_each_parameter[0]
}

#[test]
fn folded_and_explicit_definition_natural_projections_publish_each_original_id_once() {
    for occurrence in ["$natural_same(1)\n", "by def $natural_same(1)\n"] {
        let source = format!("{NATURAL_SAME}{occurrence}");
        let (result, compiler) = super::execute(&source);
        let ids = natural_sign_ids(statement_store(&result.statement_results[1]));
        assert_eq!(
            ids.len(),
            1,
            "the actual parameter-type projection owns one sign result"
        );
        let output = super::compile_run(&result, &compiler, "natural_projection_once").unwrap();
        for id in ids {
            let producer = format!("theorem h_{} :", id.value());
            assert_eq!(output.matches(&producer).count(), 1, "{producer}");
        }
    }
}

#[test]
fn natural_function_result_predicate_keeps_each_original_domain_and_body_sign_once() {
    let source = "have fn double(x N) N=2*x\nhave fn square(x N) N=x^2\ndouble(3)=6\nsquare(3)=9\nprop natural_square_result(x N):\n    square(x) $in N\nby def $natural_square_result(3)\n";
    let (result, compiler) = super::execute(source);
    let ids = natural_sign_ids(statement_store(&result.statement_results[5]));
    assert_eq!(
        ids.len(),
        2,
        "both the source argument and function-result N memberships have original sign captures"
    );
    let output = super::compile_run(&result, &compiler, "natural_function_predicate_once").unwrap();
    for id in ids {
        let declaration = format!("theorem h_{} :", id.value());
        assert_eq!(output.matches(&declaration).count(), 1, "{declaration}");
    }
}

#[test]
fn parameter_only_natural_sign_producers_are_preserved() {
    let (result, compiler) = super::execute("have n N\n0<=n\nforall k N:\n    0<=k\n");
    let have = super::ordinary_have(&result.statement_results[0]);
    let global = natural_sign_ids(&have.store_and_infer_result.store_and_infer_results[0]);
    let forall = introduction(&result.statement_results[2]);
    let local = natural_sign_ids(
        &forall
            .introduced_params
            .defined_params
            .store_and_infer_results[0],
    );
    assert_eq!(global.len(), 1);
    assert_eq!(local.len(), 1);
    let output = super::compile_run(&result, &compiler, "parameter_sign_once").unwrap();
    assert_eq!(
        output
            .matches(&format!("theorem h_{}", global[0].value()))
            .count(),
        1
    );
    assert_eq!(
        output
            .matches(&format!("have h_{} :", local[0].value()))
            .count(),
        1
    );
}

#[test]
fn actual_direct_equality_builder_and_natural_rules_retain_original_publication_order() {
    let (result, compiler) = super::execute(DIRECT_STANDARD_N);
    let forall = introduction(&result.statement_results[0]);
    let store = &forall.assumed_dom_facts[1].store_and_infer;
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &store.infer
    else {
        panic!("the original domain membership infer dispatcher")
    };
    let builder_index = rules
        .iter()
        .position(|rule| matches!(rule, InferAtomicExceptEqualityResult::InFactSetBuilder(_)))
        .expect("the direct N=builder premise gives this actual projection rule");
    let sign_index = rules
        .iter()
        .position(|rule| {
            matches!(
                rule,
                InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(_)
            )
        })
        .expect("the same source N membership has its actual sign rule");
    assert!(builder_index < sign_index);
    let InferAtomicExceptEqualityResult::InFactSetBuilder(builder) = &rules[builder_index] else {
        unreachable!()
    };
    let builder_id = builder.steps[0].derived[0].store.primary_fact_id();
    let sign_id = natural_sign_ids(store)[0];
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let formed = SourcePosition::new(Some(&run), SourceOwner::Forall(forall), 3);
    let subject = compiler
        .resolve_fact(store.primary_fact_id(), &formed)
        .unwrap();
    let member = (
        compiler.fact_proposition(&subject, &formed).unwrap(),
        format!("h_{}", subject.fact_id().value()),
    );
    let definitions = compiler
        .compile_parameter_inferences(store, &subject, &member, &formed)
        .expect("both original parameter-rule families retain their own publication");
    let output = definitions.join("\n");
    let builder_name = format!("have h_{} :", builder_id.value());
    let sign_name = format!("have h_{} :", sign_id.value());
    assert_eq!(output.matches(&builder_name).count(), 1);
    assert_eq!(output.matches(&sign_name).count(), 1);
    assert!(output.find(&builder_name).unwrap() < output.find(&sign_name).unwrap());
}

#[test]
fn bare_natural_clause_and_nested_builder_replay_original_parameter_formation() {
    for source in [NATURAL_CLAUSE, NATURAL_BUILDER, NESTED_NATURAL_BUILDER] {
        let (result, compiler) = super::execute(source);
        super::compile_run(&result, &compiler, "natural_clause_builder_once")
            .expect("the earlier original parameter sign WD supplies the later zero token");
    }
}

#[test]
fn original_parameter_formation_respects_pending_and_completed_prop_and_builder_stages() {
    for is_builder in [false, true] {
        let source = if is_builder {
            NATURAL_BUILDER
        } else {
            NATURAL_CLAUSE
        };
        let (result, compiler) = super::execute(source);
        let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
        let (owner, parameter, cached, pending_before, complete_before) = if is_builder {
            let (set, proof) = builder(&result.statement_results[0]);
            (
                SourceOwner::SetBuilder(set, proof),
                &*proof.defined_params.store_and_infer_results[0],
                sign_zero(&proof.assumed_facts[0].store_and_infer),
                1,
                2,
            )
        } else {
            let proof = concrete_prop(&result.statement_results[0]);
            (
                SourceOwner::PropDefinition(proof),
                &*proof.defined_params.store_and_infer_results[0],
                sign_zero(&proof.assumed_iff_facts[0].store_and_infer),
                0,
                1,
            )
        };
        assert!(matches!(
            sign_zero(parameter),
            ObjWellDefinedProof::ByDef { .. }
        ));
        assert!(matches!(cached, ObjWellDefinedProof::ByKnown { .. }));
        let pending = SourcePosition::new(Some(&run), owner, pending_before);
        compiler
            .compile_wd(cached, &pending)
            .expect_err("a future parameter's original constructor is not available");
        let completed = SourcePosition {
            before: complete_before,
            ..pending
        };
        compiler
            .compile_wd(cached, &completed)
            .expect("the earlier completed parameter supplies the actual cached zero WD");
        let nearest =
            SourcePosition::new(Some(&completed), SourceOwner::PropInference(parameter), 0);
        compiler
            .compile_wd(cached, &nearest)
            .expect_err("ancestor traversal cannot reopen this active pending inference");
        let sign_id = sign_capture(parameter).store.primary_fact_id();
        assert_eq!(
            nearest
                .visible_fact(sign_id, &compiler.runtime)
                .unwrap_err()
                .route,
            "Inference/FutureProducer"
        );
        assert!(completed.visible_fact(sign_id, &compiler.runtime).is_ok());
        let Some(InferFactResult::AtomicFact(infer)) = &parameter.infer else {
            panic!("the same original atomic inference node")
        };
        let seed = compiler
            .resolve_fact(parameter.primary_fact_id(), &completed)
            .unwrap();
        let atomic_pending = SourcePosition::new(
            Some(&completed),
            SourceOwner::AtomicInference(&seed, infer),
            0,
        );
        compiler
            .compile_wd(cached, &atomic_pending)
            .expect_err("the PropInference alias cannot reopen the same pending AtomicInference");
        assert_eq!(
            atomic_pending
                .visible_fact(sign_id, &compiler.runtime)
                .unwrap_err()
                .route,
            "Inference/FutureProducer"
        );
        let prop_reopen = SourcePosition::new(
            Some(&atomic_pending),
            SourceOwner::PropInference(parameter),
            usize::MAX,
        );
        compiler
            .compile_wd(cached, &prop_reopen)
            .expect_err("an explicit full alias also obeys the nearest pending atomic stage");
        let atomic_reopen = SourcePosition::new(
            Some(&nearest),
            SourceOwner::AtomicInference(&seed, infer),
            usize::MAX,
        );
        compiler
            .compile_wd(cached, &atomic_reopen)
            .expect_err("an explicit full atomic alias obeys the nearest pending store stage");
        let atomic_completed = SourcePosition {
            before: 1,
            ..atomic_pending
        };
        compiler
            .compile_wd(cached, &atomic_completed)
            .expect("the same original capture is available after its real atomic stage");
    }
}

#[test]
fn original_parameter_formation_rejects_missing_wrong_and_moved_future_zero_evidence() {
    for is_builder in [false, true] {
        for mutation in ["missing", "subject", "future"] {
            let source = if is_builder {
                NATURAL_BUILDER
            } else {
                NATURAL_CLAUSE
            };
            let (mut result, compiler) = super::execute(source);
            let (parameters, clauses) = if is_builder {
                let proof = builder_mut(&mut result.statement_results[0]);
                (&mut proof.defined_params, &mut proof.assumed_facts)
            } else {
                let proof = concrete_prop_mut(&mut result.statement_results[0]);
                (&mut proof.defined_params, &mut proof.assumed_iff_facts)
            };
            let parameter = Rc::get_mut(&mut parameters.store_and_infer_results[0])
                .expect("the sole original parameter store");
            let original = sign_zero_mut(parameter);
            let later = sign_zero_mut(&mut clauses[0].store_and_infer);
            if mutation == "future" {
                // Move the actual original ByDef to the later defining clause;
                // the parameter receives that clause's actual cache token.
                std::mem::swap(original, later);
            } else if mutation == "missing" {
                let ObjWellDefinedProof::ByKnown { obj, wd_id } = later else {
                    panic!("the real later defining-clause cache token")
                };
                *original = ObjWellDefinedProof::ByKnown {
                    obj: obj.clone(),
                    wd_id: *wd_id,
                };
            } else {
                super::replace_wd_subject(original, super::number_object("7"));
            }
            super::compile_run(&result, &compiler, "invalid_parameter_zero_formation").expect_err(
                "the missing original zero constructor cannot be recovered from a future clause",
            );
        }
    }
}

#[test]
fn completed_first_parameter_does_not_make_a_future_second_parameter_visible() {
    let (result, compiler) = super::execute("prop two_naturals(x,y N):\n    x=x\n");
    let proof = concrete_prop(&result.statement_results[0]);
    let second = &proof.defined_params.store_and_infer_results[1];
    let second_member = second.primary_fact_id();
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &sign_capture(second).well_defined else {
        panic!("the original second-parameter nonnegative formation")
    };
    let second_object = &wd.well_defined_of_each_parameter[1];
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let first = SourcePosition::new(Some(&run), SourceOwner::PropDefinition(proof), 1);
    assert!(first
        .visible_fact(second_member, &compiler.runtime)
        .is_err());
    compiler
        .compile_wd(second_object, &first)
        .expect_err("a later source parameter cannot be used at the earlier header stage");
    let completed = SourcePosition { before: 2, ..first };
    assert!(completed
        .visible_fact(second_member, &compiler.runtime)
        .is_ok());
    compiler
        .compile_wd(second_object, &completed)
        .expect("the exact second parameter becomes usable after its original introduction");
}

#[test]
fn parameter_only_sign_wd_cannot_cite_its_own_future_truth_via_a_real_later_domain_certificate() {
    for is_builder in [false, true] {
        let source = if is_builder {
            NATURAL_BUILDER
        } else {
            NATURAL_CLAUSE
        };
        let (mut result, compiler) = super::execute(source);
        let (parameters, clauses) = if is_builder {
            let proof = builder_mut(&mut result.statement_results[0]);
            (&mut proof.defined_params, &mut proof.assumed_facts)
        } else {
            let proof = concrete_prop_mut(&mut result.statement_results[0]);
            (&mut proof.defined_params, &mut proof.assumed_iff_facts)
        };
        let parameter = Rc::get_mut(&mut parameters.store_and_infer_results[0])
            .expect("the sole original parameter store");
        let original_sign = sign_capture(parameter).store.primary_fact_id();
        let later = &mut sign_formation_mut(&mut clauses[0].store_and_infer).predicate_domain;
        let PredicateDomainProof::ByKnownFact(citation) = later else {
            panic!("the actual later clause cites the earlier parameter sign")
        };
        assert_eq!(citation.cite_fact_id, original_sign);
        // Both certificates come from the same successful source. Moving the
        // later one into the parameter formation puts its citation before the
        // sign's own publication; no synthetic fact or proof is introduced.
        std::mem::swap(&mut sign_formation_mut(parameter).predicate_domain, later);
        let error = super::compile_run(&result, &compiler, "future_parameter_sign_domain")
            .expect_err("parameter-only replay also owns a pending original inference stage");
        assert_eq!(error.route, "Inference/FutureProducer");
    }
}
