use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnObjWellDefinedProof, SetBuilderObjWellDefinedProof,
    SetFormerObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_fn_application::{
        EqualitySearchProofByFnApplicationObjectDefinition,
        normalize_function_body::{AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof},
    },
};

const LINE: &str = "have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {p cart(R, R): a * p(1) + b * p(2) + c = 0}\n";
const GUARDED_SLICE: &str =
    "have fn constrained_slice(a R) power_set(R) = {x R: x != 0, a / x = a / x}\n";
const SET_RETURN_BETA: &str =
    "have fn cut(a R) power_set(R) = {x R: x = a}\nhave a R\ncut(a) = {y R: y = a}\n";

fn set_return_beta(statement: &mut ExecStmtResult) -> &mut AnonymousFunctionBodyExpansionProof {
    let proof = super::equality_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual set-valued function expansion")
    };
    let [FunctionBodyExpansionProof::Anonymous(expansion)] =
        &mut proof.normalization.expansions[..]
    else {
        panic!("one captured beta substitution")
    };
    expansion
}

#[test]
fn set_builder_beta_replays_outer_parameter_substitution_and_bound_renaming() {
    let (mut result, compiler) = super::execute(SET_RETURN_BETA);
    set_return_beta(&mut result.statement_results[2]);
    compiler
        .compile_run(&result, "set_return_beta")
        .expect("replay the recorded set-valued beta step, then the alpha-equal residual");
}

#[test]
fn set_builder_beta_rejects_changed_captured_carrier_body_and_binder() {
    for change in ["carrier", "missing_clause", "argument", "binder"] {
        let (mut result, compiler) = super::execute(SET_RETURN_BETA);
        let step = set_return_beta(&mut result.statement_results[2]);
        let Obj::FnObj(call) = &step.application else {
            panic!("actual call")
        };
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = call.body[0][0].as_ref() else {
            panic!("original caller parameter")
        };
        let wrong_binder = *id;
        let Obj::SetFormer(SetFormer::SetBuilder(set)) = &mut step.expanded_body else {
            panic!("original expanded set")
        };
        match change {
            "carrier" => set.param_set = Box::new(Obj::StandardSet(StandardSet::C)),
            "missing_clause" => set.facts.clear(),
            "binder" => set.param_binding.id = wrong_binder,
            "argument" => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(fact)) = &mut set.facts[0]
                else {
                    panic!("original equality predicate")
                };
                fact.right = super::number_object("7");
            }
            _ => unreachable!(),
        }
        step.continued_body = step.expanded_body.clone();
        let error = compiler
            .compile_run(&result, "changed_set_beta")
            .unwrap_err();
        assert_eq!(error.route, "FunctionDefinition/Substitution", "{change}");
    }
}

#[test]
fn set_builder_alpha_rejects_changed_carrier_predicate_and_free_parameter() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (result, compiler) = super::execute(SET_RETURN_BETA);
    let success =
        super::equality_proof(&super::fact_statement(&result.statement_results[2]).verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(expansion),
        ),
    ) = &success.searched_proof
    else {
        panic!("actual beta evidence")
    };
    let residual = super::equality_proof(&expansion.residual_equal);
    let EqualFactSearchedProof::ByTheyAreTheSame(identity) = &residual.searched_proof else {
        panic!("actual alpha evidence")
    };
    let position = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    for change in ["carrier", "predicate", "free_parameter", "family"] {
        let mut wrong = residual.fact.right.clone();
        let Obj::SetFormer(SetFormer::SetBuilder(set)) = &mut wrong else {
            panic!("actual set endpoint")
        };
        match change {
            "carrier" => set.param_set = Box::new(Obj::StandardSet(StandardSet::C)),
            "predicate" => set.facts.clear(),
            "free_parameter" => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(fact)) = &mut set.facts[0]
                else {
                    panic!("equality clause")
                };
                fact.right = Obj::Identifier(IdentifierObj::from_bound_name(&set.param_binding));
            }
            "family" => wrong = super::number_object("1"),
            _ => unreachable!(),
        }
        let error = compiler
            .compile_identity(&residual.fact.left, &wrong, identity, &position)
            .expect_err("bound renaming never changes the carrier, predicate or free variable");
        assert_eq!(error.route, "Equality/SetBuilderAlphaSubject", "{change}");
    }
}

fn function(statement: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )) => proof,
        _ => panic!("actual successful function declaration"),
    }
}

fn anonymous(statement: &mut ExecStmtResult) -> &mut AnonymousFnObjWellDefinedProof {
    match (&mut function(statement).anonymous_fn_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    {
        Some(DetailedObjWellDefinedProof::ByDef {
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
    match (anonymous(statement).body_well_defined.as_mut())
        .as_detailed_mut()
        .unwrap()
    {
        DetailedObjWellDefinedProof::ByDef {
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
    let Some(DetailedObjWellDefinedProof::ByDef { obj, .. }) =
        (&mut function(&mut result.statement_results[0]).anonymous_fn_well_defined)
            .as_detailed_success_mut()
            .unwrap()
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

#[test]
fn projected_line_condition_replays_its_original_builder_constructor() {
    let (result, compiler) = super::execute(include_str!(
        "../../../../lean/examples/line_membership_condition/statement.lit"
    ));
    let output = compiler
        .compile_run(&result, "line_condition_constructor")
        .unwrap();
    assert!(output.contains("fun (_value_i"));
    assert!(output.contains("Litex.inSetBuilder_iff"));
}

#[test]
fn projected_line_condition_rejects_missing_original_clause_formation() {
    let (mut result, compiler) = super::execute(include_str!(
        "../../../../lean/examples/line_membership_condition/statement.lit"
    ));
    let theorem = super::named_theorem_mut(&mut result.statement_results[3]);
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("original theorem body")
    };
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut body.proof_steps[0]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(builder)),
        ..
    } = (&mut equality.well_defined_proof.as_detailed_mut().unwrap().right)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original bounded builder")
    };
    builder.assumed_facts.clear();
    assert!(compiler
        .compile_run(&result, "missing_builder_clause_formation")
        .is_err());
}
