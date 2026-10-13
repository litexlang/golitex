use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef,
};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult};

const NATURAL_SAME: &str = "prop natural_same(x N):\n    x=x\n";
const NATURAL_CLAUSE: &str =
    "prop natural_pair(x N):\n    x $in N\n    x=x\nby def $natural_pair(1)\n";
const NATURAL_BUILDER: &str = "have NaturalFilter set={x N:x $in N}\n1 $in NaturalFilter\nforall x NaturalFilter:\n    x $in N\n    0<=x\n";
const NESTED_NATURAL_BUILDER: &str = "have NaturalFilter set={x N:x $in N}\nhave NestedFilter set={y NaturalFilter:y $in N}\nforall y NestedFilter:\n    y $in NaturalFilter\n    y $in N\n    0<=y\n";
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
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &store.infer else {
        return Vec::new();
    };
    rules
        .iter()
        .filter_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(p) => Some(&p.derived),
            _ => None,
        })
        .flatten()
        .map(|d| d.store.primary_fact_id())
        .collect()
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

#[test]
fn folded_and_explicit_definition_natural_projections_do_not_infer_their_children() {
    for occurrence in ["$natural_same(1)\n", "by def $natural_same(1)\n"] {
        let source = format!("{NATURAL_SAME}{occurrence}");
        let (result, compiler) = super::execute(&source);
        let ids = natural_sign_ids(statement_store(&result.statement_results[1]));
        assert_eq!(
            ids.len(),
            0,
            "the parameter-type projection stores N membership without inferring its sign"
        );
        let output = super::compile_run(&result, &compiler, "natural_projection_once").unwrap();
        for id in ids {
            let producer = format!("theorem h_{} :", id.value());
            assert_eq!(output.matches(&producer).count(), 1, "{producer}");
        }
    }
}

#[test]
fn natural_function_result_predicate_stores_domain_and_body_without_child_signs() {
    let source = "have fn double(x N) N=2*x\nhave fn square(x N) N=x^2\ndouble(3)=6\nsquare(3)=9\nprop natural_square_result(x N):\n    square(x) $in N\nby def $natural_square_result(3)\n";
    let (result, compiler) = super::execute(source);
    let ids = natural_sign_ids(statement_store(&result.statement_results[5]));
    assert_eq!(
        ids.len(),
        0,
        "derived argument and function-result memberships do not infer signs"
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
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &store.infer else {
        panic!("the original domain membership infer dispatcher")
    };
    let builder_index = rules
        .iter()
        .position(|rule| matches!(rule, InferInFactResult::SetBuilder(_)))
        .expect("the direct N=builder premise gives this actual projection rule");
    let sign_index = rules
        .iter()
        .position(|rule| matches!(rule, InferInFactResult::SignedStandardSetSign(_)))
        .expect("the same source N membership has its actual sign rule");
    assert!(builder_index < sign_index);
    let InferInFactResult::SetBuilder(builder) = &rules[builder_index] else {
        unreachable!()
    };
    let builder_id = builder.steps[0].projections[0]
        .stored()
        .store
        .primary_fact_id();
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
fn named_inference_constructors_follow_the_actual_parameter_stage() {
    let zero = super::number_object("0");
    for is_builder in [false, true] {
        let source = if is_builder {
            NATURAL_BUILDER
        } else {
            NATURAL_CLAUSE
        };
        let (result, _) = super::execute(source);
        let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
        let (owner, pending, complete) = if is_builder {
            let (set, proof) = builder(&result.statement_results[0]);
            (SourceOwner::SetBuilder(set, proof), 1, 2)
        } else {
            (
                SourceOwner::PropDefinition(concrete_prop(&result.statement_results[0])),
                0,
                1,
            )
        };
        let before = SourcePosition::new(Some(&run), owner, pending);
        assert!(before
            .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
            .unwrap()
            .is_none());
        let after = SourcePosition {
            before: complete,
            ..before
        };
        assert!(after
            .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
            .unwrap()
            .is_some());
    }
}

#[test]
fn generated_primitive_cannot_be_recovered_before_its_named_rule() {
    let (result, compiler) = super::execute("have n N\n0<=n\n");
    let zero = super::number_object("0");
    let before = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    assert!(before
        .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(compiler.compile_object_reference(&zero, &before).is_err());
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(after
        .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
        .unwrap()
        .is_some());
    assert!(compiler
        .compile_object_reference(&zero, &after)
        .unwrap()
        .contains("Litex.number"));
}
