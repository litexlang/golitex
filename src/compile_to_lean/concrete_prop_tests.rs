use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::prelude::*;
use crate::store_fact_and_infer::InferNormalAtomicFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult};

const NONZERO: &str = "prop nonzero(x R):\n    x != 0\n$nonzero(1)\nby def $nonzero(1)\n1 != 0";
const SQUARE: &str = "prop square_is_one(x R):\n    x * x = 1\n$square_is_one(1)\n1 * 1 = 1";
const GUARDED: &str =
    "prop guarded_identity(x R):\n    x != 0\n    x / x = 1\n$guarded_identity(1)\n1 / 1 = 1";
const GUARDED_SET_PROJECTION: &str = "have fn guarded_reals(a R: a != 0) power_set(R) = R\nprop in_guarded_reals(x, y R):\n    y != 0\n    x $in guarded_reals(y)\nprop nested_guarded_reals(x, y R):\n    $in_guarded_reals(x, y)\n    x = x\n";

fn checked(source: &str) -> (Runtime, RunLitexCodeResult) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).unwrap();
    assert!(result.success && result.session_error.is_none(), "{source}");
    (runtime, result)
}

#[test]
fn concrete_prop_retains_domains_and_actual_explicit_definition_route() {
    let (runtime, result) = checked(NONZERO);
    let ExecStmtResult::By(ExecByStmtResult::Def(
        crate::execute::execute_by_stmt::ExecByDefStmtResult::Success(by_def),
    )) = &result.statement_results[2]
    else {
        panic!("explicit definition request");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &by_def.proof else {
        panic!("atomic definition proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful definition proof");
    };
    assert!(matches!(
        &proof.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByDefinition(_)
    ));
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_nonzero")
        .unwrap();
    assert!(output.contains("def prop_1"));
    assert!(output.contains("∃ (h_"));
    assert!(output.contains("Litex.In _value_i"));
    assert!(output.contains("Exists.intro"));
    assert!(output.contains("rcases"));
}

#[test]
fn concrete_prop_inference_retains_named_domain_and_body_stores() {
    let (runtime, result) = checked(SQUARE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &result.statement_results[1]
    else {
        panic!("predicate seed");
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) =
        &seed.store_and_infer_result.infer
    else {
        panic!("predicate infer dispatcher");
    };
    let InferNormalAtomicFactResult::ParamTypes(members) = &rules[0] else {
        panic!("ordered parameter projections");
    };
    let InferNormalAtomicFactResult::ExpandDefinition(body) = &rules[1] else {
        panic!("ordered definition expansion");
    };
    assert_eq!(members.derived.len(), 1);
    assert_eq!(body.derived.len(), 1);
    let derived = &body.derived[0];
    let StoreFactResult::AtomicFact(stored) = &derived.store else {
        panic!("atomic defining clause");
    };
    let AtomicFact::EqualFact(_equality) = &stored.fact else {
        panic!("square defining equality");
    };
    let actual_id = derived.store.primary_fact_id();
    assert!(seed
        .store_and_infer_result
        .stored_fact_ids()
        .contains(&actual_id));
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_square")
        .unwrap();
    assert!(output.contains(&format!("theorem h_{}", actual_id.value())));
    assert!(output.contains("Litex.mul"));
    assert!(output.contains("rcases"));
}

#[test]
fn concrete_prop_earlier_clause_certifies_later_guarded_constructor() {
    let (runtime, result) = checked(GUARDED);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(definition),
    )) = &result.statement_results[0]
    else {
        panic!("concrete definition");
    };
    assert_eq!(definition.assumed_iff_facts.len(), 2);
    let nonzero_id = definition.assumed_iff_facts[0]
        .store_and_infer
        .primary_fact_id();
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "concrete_guarded")
        .unwrap();
    assert!(output.contains(&format!("∃ (h_{}", nonzero_id.value())));
    assert!(output.contains("Litex.div"));
}

#[test]
fn concrete_prop_cannot_resolve_a_removed_definition_from_final_runtime() {
    let (runtime, mut result) = checked(NONZERO);
    result.statement_results.remove(0);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "missing_prop")
        .unwrap_err();
    assert!(error.route.starts_with("Prop/"), "{error:?}");
}

#[test]
fn concrete_prop_rejects_definition_requirements_without_their_actual_proof_ids() {
    let (runtime, mut result) = checked(NONZERO);
    let ExecStmtResult::By(ExecByStmtResult::Def(
        crate::execute::execute_by_stmt::ExecByDefStmtResult::Success(by_def),
    )) = &mut result.statement_results[2]
    else {
        panic!("explicit definition request");
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut by_def.proof else {
        panic!("atomic definition proof");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful definition proof");
    };
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(definition)) = &mut proof.searched_proof else { panic!("selected concrete fold"); };
    definition.proof_of_requirement_facts.pop();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "missing_fold_child")
        .unwrap_err();
    assert_eq!(error.route, "Prop/FoldArity");
}

#[test]
fn concrete_prop_rejects_reordered_domain_and_body_inferences() {
    let (runtime, mut result) = checked(SQUARE);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(seed)) = &mut result.statement_results[1]
    else {
        panic!("predicate seed");
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) =
        &mut seed.store_and_infer_result.infer
    else {
        panic!("predicate infer dispatcher");
    };
    rules.swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "reordered_prop_inference")
        .unwrap_err();
    assert!(error.route.starts_with("Prop/Infer"), "{error:?}");
}

fn local_projection_rules(
    result: &mut RunLitexCodeResult,
) -> &mut Vec<InferNormalAtomicFactResult> {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(definition),
    )) = &mut result.statement_results[2]
    else {
        panic!("original nested predicate declaration");
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) =
        &mut definition.assumed_iff_facts[0].store_and_infer.infer
    else {
        panic!("original predicate inference");
    };
    rules
}

#[test]
fn local_prop_projection_retains_a_guarded_set_valued_call_without_new_wd() {
    let (runtime, mut result) = checked(GUARDED_SET_PROJECTION);
    let rules = local_projection_rules(&mut result);
    let InferNormalAtomicFactResult::ParamTypes(parameters) = &rules[0] else {
        panic!("parameter projections precede the body");
    };
    assert_eq!(parameters.derived.len(), 2);
    let InferNormalAtomicFactResult::ExpandDefinition(body) = &rules[1] else {
        panic!("original definition expansion");
    };
    assert_eq!(body.derived.len(), 2);
    let StoreFactResult::AtomicFact(stored) = &body.derived[1].store else {
        panic!("atomic membership projection");
    };
    let AtomicFact::InFact(member) = &stored.fact else {
        panic!("membership in the returned set");
    };
    assert!(matches!(member.set, Obj::FnObj(_)));
    let ids = rules
        .iter()
        .flat_map(InferNormalAtomicFactResult::stored_conclusions)
        .map(|stored| stored.primary_fact_id())
        .collect::<Vec<_>>();
    let compiler = LitexToLeanCompiler::new(runtime);
    let statement = &result.statement_results[2];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(definition),
    )) = statement
    else {
        panic!("original nested predicate declaration");
    };
    let run_position = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let statement_position =
        SourcePosition::new(Some(&run_position), SourceOwner::Statement(statement), 0);
    let completed = SourcePosition::new(
        Some(&statement_position),
        SourceOwner::PropDefinition(definition),
        definition
            .statement
            .typed_parameters
            .ordered_param_ids()
            .len()
            + 1,
    );
    let seed = &definition.statement.iff_facts[0];
    let compiled_seed = (
        compiler.fact_proposition(seed, &completed).unwrap(),
        format!("h_{}", seed.fact_id().value()),
    );
    let projections = compiler
        .compile_stored_inferences(
            &definition.assumed_iff_facts[0].store_and_infer,
            seed,
            &compiled_seed,
            &completed,
        )
        .unwrap();
    assert_eq!(projections.len(), ids.len());
    for (index, (id, projection)) in ids.iter().zip(&projections).enumerate() {
        assert!(projection.starts_with(&format!("have h_{} :=\n", id.value())));
        assert!(projection.contains(&format!(
            "(show {} from {})",
            compiled_seed.0, compiled_seed.1
        )));
        assert_eq!(projection.matches("Classical.choose_spec").count(), index);
        assert_eq!(
            projection.contains("(Classical.choose "),
            index + 1 < ids.len()
        );
    }
    let output = compiler
        .compile_run(&result, "local_guarded_set_projection")
        .unwrap();
    assert!(output.contains("def prop_3 "));
    // The final clause is x = x; none of these local projections is a lexical
    // dependency, so the existing scope closer omits them from the artifact.
    for id in ids {
        assert!(!output.contains(&format!("let h_{} ", id.value())));
    }
}

#[test]
fn local_prop_projection_rejects_another_instantiated_set_subject() {
    let (runtime, mut result) = checked(GUARDED_SET_PROJECTION);
    let InferNormalAtomicFactResult::ExpandDefinition(body) =
        &mut local_projection_rules(&mut result)[1]
    else {
        panic!("definition expansion");
    };
    let StoreFactResult::AtomicFact(stored) = &mut body.derived[1].store else {
        panic!("atomic store");
    };
    let AtomicFact::InFact(member) = &mut stored.fact else {
        panic!("membership store");
    };
    member.set = Obj::StandardSet(StandardSet::R);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "changed_local_projection_subject")
        .unwrap_err();
    assert_eq!(error.route, "Prop/InferBodySubject");
}

#[test]
fn local_prop_projection_rejects_another_original_store_identity() {
    let (runtime, mut result) = checked(GUARDED_SET_PROJECTION);
    let InferNormalAtomicFactResult::ExpandDefinition(body) =
        &mut local_projection_rules(&mut result)[1]
    else {
        panic!("definition expansion");
    };
    let wrong_id = body.derived[0].primary_fact_id();
    let StoreFactResult::AtomicFact(stored) = &mut body.derived[1].store else {
        panic!("atomic store");
    };
    stored.fact_id = wrong_id;
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "changed_local_projection_identity")
        .unwrap_err();
    assert_eq!(error.route, "Prop/InferIdentity");
}

#[test]
fn local_prop_projection_rejects_reordered_defining_clauses() {
    let (runtime, mut result) = checked(GUARDED_SET_PROJECTION);
    let InferNormalAtomicFactResult::ExpandDefinition(body) =
        &mut local_projection_rules(&mut result)[1]
    else {
        panic!("definition expansion");
    };
    body.derived.swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "reordered_local_projection_clauses")
        .unwrap_err();
    assert_eq!(error.route, "Prop/InferBodySubject");
}
