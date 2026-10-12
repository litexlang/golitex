use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
    InFactSearchProofByBuiltinRule, SetBuilderMembershipBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::prelude::*;
use crate::prelude::verify_chain_fact::VerifyChainFactResult;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
    SetBuilderMembershipProjectionStep,
};
use std::rc::Rc;

const INTERVAL: &str = "have Interval set={x R:0<=x<=1}\n(1/2) $in Interval\nforall x Interval:\n    0<=x<=1\nInterval $subset R\n";
const GUARDED_ALIAS: &str = "prop is_unit_interval(x R):\n    0<=x<=1\nhave Guarded set={t R:$is_unit_interval(t)}\nlet Alias=Guarded\nby def $is_unit_interval(1/2)\n(1/2) $in Guarded\n(1/2) $in Alias\n";

fn declaration(statement: &ExecStmtResult) -> &ExecHaveObjEqualStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => proof,
        _ => panic!("actual set declaration"),
    }
}

fn builder_mut(statement: &mut ExecStmtResult) -> &mut SetBuilderObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("set declaration")
    };
    match &mut proof.equal_to_well_defined[0] {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(
                    builder,
                )),
            ..
        }) => builder,
        _ => panic!("actual set-builder formation"),
    }
}

fn introduction(statement: &ExecStmtResult) -> &VerifyForallFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("forall statement")
    };
    match &proof.verify_result {
        VerifyFactResult::ForallFact(proof) => match proof.as_ref() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) => {
                proof
            }
            _ => panic!("original forall introduction"),
        },
        _ => panic!("forall result"),
    }
}

fn projection_mut(statement: &mut ExecStmtResult) -> &mut SetBuilderMembershipProjectionStep {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("forall statement")
    };
    let VerifyFactResult::ForallFact(proof) = &mut proof.verify_result else {
        panic!("forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_mut()
    else {
        panic!("original forall introduction")
    };
    let store = Rc::get_mut(
        &mut proof
            .introduced_params
            .defined_params
            .store_and_infer_results[0],
    )
    .expect("sole actual parameter store");
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &mut store.infer
    else {
        panic!("membership inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::InFactSetBuilder(proof) => Some(&mut proof.steps[0]),
            _ => None,
        })
        .expect("original bounded-set projection")
}

fn membership_mut(proof: &mut VerifyFactResult) -> &mut SetBuilderMembershipBuiltinRuleProof {
    let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
        panic!("atomic membership proof")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful membership proof")
    };
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::SetBuilderMembership(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(proof),
        ) => membership_mut(&mut proof.proof_of_rewritten_fact),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
                proof,
            ),
        ) => membership_mut(&mut proof.proof_of_rewritten_fact),
        _ => panic!("actual set-builder membership route"),
    }
}

fn chain_membership_mut(statement: &mut ExecStmtResult) -> &mut Vec<VerifyFactResult> {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("membership statement")
    };
    let requirements = membership_mut(&mut proof.verify_result);
    let VerifyFactResult::ChainFact(proof) = &mut requirements.proof_of_requirement_facts[1] else {
        panic!("original ordered filter certificate")
    };
    let VerifyChainFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful filter certificate")
    };
    &mut proof.adjacent
}

#[test]
fn bounded_chain_filter_replays_actual_compound_stores_and_projection_dependencies() {
    let (result, compiler) = super::execute(INTERVAL);
    let introduction = introduction(&result.statement_results[2]);
    let store = &introduction
        .introduced_params
        .defined_params
        .store_and_infer_results[0];
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &store.infer
    else {
        panic!("original membership inference")
    };
    let projection = rules
        .iter()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::InFactSetBuilder(proof) => Some(&proof.steps[0]),
            _ => None,
        })
        .expect("bounded-set projection");
    assert_eq!(
        projection.source_membership.fact_id,
        store.primary_fact_id()
    );
    let equality_id = declaration(&result.statement_results[0])
        .store_and_infer_result
        .store_and_infer_results[1]
        .primary_fact_id();
    assert_eq!(projection.equality_path.len(), 1);
    assert_eq!(projection.equality_path[0].2, equality_id);
    assert_eq!(projection.derived.len(), 2);
    let chain = &projection.derived[1];
    let StoreFactResult::ChainFact(stored) = &chain.store else {
        panic!("actual projected chain store")
    };
    assert_eq!(stored.adjacent.len(), 2);
    assert_eq!(
        chain.stored_fact_ids().len(),
        3,
        "whole chain and adjacent stores only"
    );
    let output = super::compile_run(&result, &compiler, "bounded_chain").unwrap();
    assert!(output.contains("Litex.inSetBuilder_iff"));
    // This inferred leaf owns only the whole chain and its two stored edges.
    // Other source owners in the same file can legitimately emit leTrans.
    for id in chain.store.stored_fact_ids() {
        assert!(
            output.contains(&format!("have h_{} :", id.value())),
            "actual projected producer {id} is not emitted"
        );
    }
    assert!(output.contains(&format!("h_{}", equality_id.value())));
}

#[test]
fn bounded_filter_cannot_replace_its_actual_binder_store() {
    let (mut result, compiler) = super::execute(INTERVAL);
    let builder = builder_mut(&mut result.statement_results[0]);
    let store = Rc::get_mut(&mut builder.defined_params.store_and_infer_results[0]).unwrap();
    let StoreFactResult::AtomicFact(stored) = &mut store.store else {
        panic!("binder store")
    };
    let AtomicFact::InFact(member) = &mut stored.fact else {
        panic!("binder member")
    };
    member.element = Obj::Literal(Literal::Number(Number {
        normalized_value: "7".into(),
    }));
    super::compile_run(&result, &compiler, "wrong_bounded_binder")
        .expect_err("an unchanged FactId cannot relabel the binder");
}

#[test]
fn bounded_filter_requires_original_bound_wd_and_subject() {
    for missing in [true, false] {
        let (mut result, compiler) = super::execute(INTERVAL);
        let builder = builder_mut(&mut result.statement_results[0]);
        if missing {
            builder.param_set_well_defined = Box::new(ObjWellDefinedProof::ByKnown {
                obj: Obj::StandardSet(StandardSet::R),
                wd_id: WellDefinednessId::new(u64::MAX),
            });
        } else {
            match builder.param_set_well_defined.as_mut() {
                ObjWellDefinedProof::ByDef { obj, .. }
                | ObjWellDefinedProof::ByKnown { obj, .. } => {
                    *obj = Obj::StandardSet(StandardSet::Q)
                }
            }
        }
        super::compile_run(&result, &compiler, "wrong_bound_wd")
            .expect_err("bound WD must come from its exact visible original producer");
    }
}

#[test]
fn bounded_chain_filter_cannot_drop_or_reorder_original_formation() {
    for corruption in 0..3 {
        let (mut result, compiler) = super::execute(INTERVAL);
        let builder = builder_mut(&mut result.statement_results[0]);
        if corruption == 0 {
            builder.assumed_facts.clear();
        } else {
            let FactWellDefinedProof::ChainFact { adjacent } =
                &mut builder.assumed_facts[0].well_defined
            else {
                panic!("actual filter formation")
            };
            if corruption == 1 {
                adjacent.pop();
            } else {
                adjacent[0].well_defined_of_each_parameter.swap(0, 1);
            }
        }
        super::compile_run(&result, &compiler, "wrong_filter_formation")
            .expect_err("each ordered original chain edge needs matching formation");
    }
}

#[test]
fn bounded_chain_projection_cannot_drop_or_change_selected_filter() {
    for missing in [true, false] {
        let (mut result, compiler) = super::execute(INTERVAL);
        let projection = projection_mut(&mut result.statement_results[2]);
        if missing {
            projection.derived.pop();
        } else {
            let StoreFactResult::ChainFact(stored) = &mut projection.derived[1].store else {
                panic!("selected chain store")
            };
            stored.fact.objs[1] = Obj::Literal(Literal::Number(Number {
                normalized_value: "7".into(),
            }));
        }
        super::compile_run(&result, &compiler, "wrong_filter_projection").expect_err(
            "later companion inequalities cannot use deleted or mismatched projection evidence",
        );
    }
}

#[test]
fn bounded_membership_requires_both_ordered_companion_inequality_proofs() {
    for missing in [true, false] {
        let (mut result, compiler) = super::execute(INTERVAL);
        let adjacent = chain_membership_mut(&mut result.statement_results[1]);
        assert_eq!(adjacent.len(), 2);
        if missing {
            adjacent.pop();
        } else {
            adjacent.swap(0, 1);
        }
        super::compile_run(&result, &compiler, "wrong_companion_inequality").expect_err(
            "one side of the filter or a reordered companion cannot establish the original chain",
        );
    }
}

#[test]
fn bounded_concrete_predicate_and_set_alias_replay_selected_source_definitions() {
    let (result, compiler) = super::execute(GUARDED_ALIAS);
    let output = super::compile_run(&result, &compiler, "bounded_predicate_alias").unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(predicate),
    )) = &result.statement_results[0]
    else {
        panic!("actual concrete predicate declaration")
    };
    let parameter = &predicate.statement.typed_parameters.groups[0].params[0];
    let parameter_name = format!("_value_i{}", parameter.id.value());
    let declaration = output
        .lines()
        .find(|line| line.starts_with("def prop_") && line.contains(&parameter_name))
        .expect("the original predicate binder appears in its generated declaration");
    let predicate_name = declaration
        .split_whitespace()
        .nth(1)
        .expect("actual generated predicate symbol");
    assert!(
        output
            .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
            .filter(|name| *name == predicate_name)
            .count()
            >= 2,
        "the actual predicate declaration must be emitted and consumed"
    );
    assert!(output.contains("Litex.inSetBuilder_iff"));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(alias)),
    )) = &result.statement_results[2]
    else {
        panic!("actual alias")
    };
    let alias_id = alias.stored_fact_ids[0];
    assert!(
        output.matches(&format!("h_{}", alias_id.value())).count() >= 2,
        "alias equality must be emitted and used by membership replay"
    );
}
