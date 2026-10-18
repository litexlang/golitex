use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnObjWellDefinedProof, SetBuilderObjWellDefinedProof,
    SetFormerObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;

const LINE: &str = "have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {p cart(R, R): a * p(1) + b * p(2) + c = 0}\n";
const GUARDED_SLICE: &str =
    "have fn constrained_slice(a R) power_set(R) = {x R: x != 0, a / x = a / x}\n";

fn function(statement: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )) => proof,
        _ => panic!("actual successful function declaration"),
    }
}

fn anonymous(statement: &mut ExecStmtResult) -> &mut AnonymousFnObjWellDefinedProof {
    match &mut function(statement).anonymous_fn_well_defined {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof),
                ),
            ..
        }) => proof,
        _ => panic!("actual defining anonymous-function WD"),
    }
}

fn builder(statement: &mut ExecStmtResult) -> (&SetBuilder, &mut SetBuilderObjWellDefinedProof) {
    match anonymous(statement).body_well_defined.as_mut() {
        ObjWellDefinedProof::ByDef {
            obj: Obj::SetFormer(SetFormer::SetBuilder(set)),
            proof:
                ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(
                    proof,
                )),
        } => (set, proof),
        _ => panic!("actual bounded set-builder body"),
    }
}

#[test]
fn set_builder_function_body_replays_original_line_formation_and_return_membership() {
    let (mut result, compiler) = super::execute(LINE);
    let (_, proof) = builder(&mut result.statement_results[0]);
    assert_eq!(proof.assumed_facts.len(), 1);
    let output = compiler
        .compile_run(&result, "set_builder_line")
        .expect("original line definition and selected power-set return proof replay");
    assert_eq!(
        output.matches("(Litex.formulaFnOn ").count(),
        1,
        "the stored defining equality reuses the exact already checked object"
    );
}

#[test]
fn set_builder_function_body_preserves_prior_clause_proof_binder() {
    let (mut result, compiler) = super::execute(GUARDED_SLICE);
    let (_, proof) = builder(&mut result.statement_results[0]);
    assert_eq!(proof.assumed_facts.len(), 2);
    let nonzero_id = proof.assumed_facts[0].store_and_infer.primary_fact_id();
    let output = compiler
        .compile_run(&result, "set_builder_guarded_slice")
        .expect("the first clause certifies division in the second clause");
    assert!(output.contains(&format!("∃ (h_{} :", nonzero_id.value())));
}

#[test]
fn set_builder_function_body_rejects_missing_original_prior_clause() {
    let (mut result, compiler) = super::execute(GUARDED_SLICE);
    let (_, proof) = builder(&mut result.statement_results[0]);
    proof.assumed_facts.remove(0);
    let error = compiler
        .compile_run(&result, "missing_set_builder_guard")
        .expect_err("raw template rendering cannot replace a missing source assumption");
    assert_eq!(error.route, "SetBuilder/Stages");
}

#[test]
fn shared_function_definition_keeps_its_original_equality_citation_for_later_beta() {
    let source = "have fn shift_once(x R) R = x + 1\nshift_once(2) = 3\n";
    let (mut result, compiler) = super::execute(source);
    let proof = function(&mut result.statement_results[0]);
    let object = format!("(_object_i{} (M := M))", proof.statement.name.id.value());
    let equality = format!(
        "h_{}",
        proof.store_and_infer_result.defining_equal_fact_id.value()
    );
    let output = compiler
        .compile_run(&result, "shared_function_definition")
        .expect("the original beta proof can consume the shared defining equality");
    assert!(output.contains(&format!("Litex.Same {object} {object}")));
    assert!(output.matches(&equality).count() >= 2);
}

#[test]
fn shared_function_definition_rejects_another_original_anonymous_wd() {
    let source = "have fn first_formula(x R) R = x + 1\nhave fn other_formula(x R) R = x + 2\n";
    let (mut result, compiler) = super::execute(source);
    let other = Obj::FunctionSpace(FunctionSpace::AnonymousFn(
        function(&mut result.statement_results[1])
            .statement
            .equal_to_anonymous_fn
            .clone(),
    ));
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef { obj, .. }) =
        &mut function(&mut result.statement_results[0]).anonymous_fn_well_defined
    else {
        panic!("actual original anonymous WD")
    };
    *obj = other;
    let error = compiler
        .compile_run(&result, "wrong_shared_function_wd")
        .expect_err("emission reuse cannot replace the exact original anonymous WD");
    assert_eq!(error.route, "WD/Subject");
}

#[test]
fn shared_function_definition_rejects_another_stored_literal_with_the_same_fact_id() {
    let source = "have fn first_formula(x R) R = x + 1\nhave fn other_formula(x R) R = x + 2\n";
    let (mut result, compiler) = super::execute(source);
    let other = Obj::FunctionSpace(FunctionSpace::AnonymousFn(
        function(&mut result.statement_results[1])
            .statement
            .equal_to_anonymous_fn
            .clone(),
    ));
    let StoreFactResult::AtomicFact(stored) = &mut function(&mut result.statement_results[0])
        .store_and_infer_result
        .defining_equal
        .store
    else {
        panic!("actual stored defining equality")
    };
    let AtomicFact::EqualFact(equal) = &mut stored.fact else {
        panic!("actual equality subject")
    };
    equal.right = other;
    super::phase2_rejected(
        &result,
        &compiler,
        "sharing a generated definition must not repair a corrupted original equality store",
        &["Declaration/StoreSubject", "Store/Subject"],
    );
}
