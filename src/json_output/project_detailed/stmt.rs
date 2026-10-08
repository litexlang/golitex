//! Detailed projection for non-fact statement kinds.

use super::induction::{
    project_by_induc, project_by_strong_induc, project_induc_algo, project_induc_definition,
};
use super::store::{project_have_store_ids, project_store_and_infer, project_verify_facts};
use super::verify::project_verify_fact;
use super::wd::{
    project_fact_wd_proof, project_obj_wd_proof, project_param_type_wd,
    project_verify_fact_wd_result, project_verify_obj_wd,
};
use crate::execute::execute_by_stmt::{ByContradictionClosingFailed, ExecByContraStmtFailed};
use crate::execute::execute_by_stmt::{
    ExecByCasesStmtResult, ExecByContraStmtResult, ExecByDefStmtResult,
    ExecByEnumerateFiniteSetStmtResult, ExecByExtensionStmtResult, ExecByFnExtensionStmtResult,
    ExecByForStmtResult, ExecByInducStmtResult, ExecByStmtResult, ExecByStrongInducStmtResult,
    ExecByThmStmtResult,
};
use crate::execute::execute_fact_stmt::ExecFactStmtResult;
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtResult,
};
use crate::execute::execute_witness_stmt::ExecWitnessStmtResult;
use crate::execute::{
    ExecAxiomStmtResult, ExecCommandStmtResult, ExecDefAbstractPropStmtSuccessResult,
    ExecDefAlgoByCasesStmtResult, ExecDefPropStmtResult, ExecDefStrategyStmtResult,
    ExecDefStructStmtResult, ExecDefTemplateStmtResult, ExecDefThmStmtResult,
    ExecDefineObjStmtResult, ExecDefinitionStmtResult, ExecEvalStmtResult,
    ExecHaveByFnPreimageStmtResult, ExecHaveByReplacementAxiomStmtResult,
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByInducStmtResult,
    ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualStmtFailed, ExecHaveFnEqualStmtResult,
    ExecHaveObjByExistFactsStmtResult, ExecHaveObjEqualStmtResult,
    ExecHaveObjInNonemptySetStmtResult, ExecLetObjStmtResult,
    ExecObtainObjFromAtomicFactStmtResult, ExecObtainObjFromExistFactStmtResult,
    ExecReleaseAndExpandStmtResult, ExecStmtResult, ExecTrustBoundaryStmtResult,
    ParamTypeFactCheckResult,
};
use crate::json_output::helper::{bool_value, object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub fn project_stmt_detailed(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecStmtResult::Fact(fact) => super::entry::project_fact_only(fact, runtime),
        ExecStmtResult::Definition(def) => project_definition(def, runtime),
        ExecStmtResult::Witness(w) => project_witness(w, runtime),
        ExecStmtResult::Trust(t) => project_trust(t, runtime),
        ExecStmtResult::By(b) => project_by(b, runtime),
        ExecStmtResult::Register(r) => super::register::project_register(r, runtime),
        ExecStmtResult::ReleaseAndExpand(r) => project_release_and_expand(r, runtime),
        ExecStmtResult::ProofBlock(p) => project_proof_block(p, runtime),
        ExecStmtResult::Command(c) => project_command(c, runtime),
    }
}

fn project_definition(def: &ExecDefinitionStmtResult, runtime: &Runtime) -> JsonValue {
    match def {
        ExecDefinitionStmtResult::DefineObj(d) => project_define_obj(d, runtime),
        ExecDefinitionStmtResult::HaveFnEqual(r) => match r {
            ExecHaveFnEqualStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("have_fn_equal")),
                    (
                        "statement",
                        string(crate::display_and_ir::readable_string_from_ir_text(
                            s.statement.ir().as_str(),
                        )),
                    ),
                    (
                        "anonymous_fn_well_defined",
                        project_verify_obj_wd(&s.anonymous_fn_well_defined, runtime),
                    ),
                    (
                        "fn_set_well_defined",
                        project_verify_obj_wd(&s.fn_set_well_defined, runtime),
                    ),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecHaveFnEqualStmtResult::Failed(failed) => {
                let (phase, wd) = match failed {
                    ExecHaveFnEqualStmtFailed::AnonymousFnWellDefined(wd) => {
                        ("anonymous_fn_well_defined", wd)
                    }
                    ExecHaveFnEqualStmtFailed::FnSetWellDefined(wd) => ("fn_set_well_defined", wd),
                };
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(false)),
                        ("kind", string("have_fn_equal")),
                        (phase, project_verify_obj_wd(wd, runtime)),
                    ],
                )
            }
        },
        ExecDefinitionStmtResult::HaveFnEqualCaseByCase(r) => match r {
            ExecHaveFnEqualCaseByCaseStmtResult::Success(s) => project_success_failed_shell(
                "have_fn_equal_case_by_case",
                true,
                Some(s.statement.readable_string()),
                Some(project_have_store_ids(
                    &s.store_and_infer_result.stored_fact_ids,
                    runtime,
                )),
                runtime,
            ),
            ExecHaveFnEqualCaseByCaseStmtResult::Failed(failure) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("have_fn_equal_case_by_case")),
                    (
                        "failure",
                        project_cases_definition_failure(failure, runtime),
                    ),
                ],
            ),
        },
        ExecDefinitionStmtResult::HaveFnByForallExistUnique(r) => {
            use crate::execute::ExecHaveFnByForallExistUniqueStmtFailed;
            match r {
                ExecHaveFnByForallExistUniqueStmtResult::Success(s) => object_for(
                    runtime,
                    vec![
                        ("success", bool_value(true)),
                        ("kind", string("have_fn_by_forall_exist_unique")),
                        ("statement", string(s.statement.readable_string())),
                        (
                            "source_forall",
                            project_verify_fact(&s.source_forall, runtime),
                        ),
                        (
                            "fn_set_well_defined",
                            super::wd::project_verify_obj_wd(&s.fn_set_well_defined, runtime),
                        ),
                        (
                            "store_and_infer",
                            project_have_store_ids(&s.stored_fact_ids, runtime),
                        ),
                    ],
                ),
                ExecHaveFnByForallExistUniqueStmtResult::Failed(f) => {
                    let (phase, failure) = match f {
                        ExecHaveFnByForallExistUniqueStmtFailed::SourceForall(v) => {
                            ("source_forall", project_verify_fact(v, runtime))
                        }
                        ExecHaveFnByForallExistUniqueStmtFailed::FnSetWellDefined(v) => (
                            "fn_set_well_defined",
                            super::wd::project_verify_obj_wd(v, runtime),
                        ),
                        ExecHaveFnByForallExistUniqueStmtFailed::PropertyWellDefined(v) => (
                            "property_well_defined",
                            super::wd_failure::project_fact_wd_failure(v, runtime),
                        ),
                    };
                    object_for(
                        runtime,
                        vec![
                            ("success", bool_value(false)),
                            ("kind", string("have_fn_by_forall_exist_unique")),
                            ("phase", string(phase)),
                            ("failure", failure),
                        ],
                    )
                }
            }
        }
        ExecDefinitionStmtResult::HaveFnByInduc(r) => project_induc_definition(r, runtime),
        ExecDefinitionStmtResult::DefProp(r) => project_def_prop(r, runtime),
        ExecDefinitionStmtResult::DefAbstractProp(r) => project_def_abstract_prop(r, runtime),
        ExecDefinitionStmtResult::DefStruct(r) => project_def_struct(r, runtime),
        ExecDefinitionStmtResult::DefTemplate(r) => match r {
            ExecDefTemplateStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("def_template")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "definition_facts",
                        JsonValue::Array(
                            s.definition_facts
                                .iter()
                                .map(|published| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "source_fact_id",
                                                string(published.source_fact_id.to_string()),
                                            ),
                                            (
                                                "store_and_infer",
                                                project_store_and_infer(
                                                    &published.store_and_infer,
                                                    runtime,
                                                ),
                                            ),
                                        ],
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ],
            ),
            ExecDefTemplateStmtResult::Failed(failure) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("def_template")),
                    (
                        "failure",
                        super::template_failure::project_template_failure(failure, runtime),
                    ),
                ],
            ),
        },
        ExecDefinitionStmtResult::DefAlgoByCases(r) => project_success_failed_shell(
            "def_algo_by_cases",
            !r.is_failed(),
            match r {
                ExecDefAlgoByCasesStmtResult::Success(s) => Some(s.statement.readable_string()),
                _ => None,
            },
            None,
            runtime,
        ),
        ExecDefinitionStmtResult::DefAlgoByInduc(r) => project_induc_algo(r, runtime),
        ExecDefinitionStmtResult::DefThm(r) => project_def_thm(r, runtime),
        ExecDefinitionStmtResult::Axiom(r) => project_axiom(r, runtime),
        ExecDefinitionStmtResult::DefStrategy(r) => project_def_strategy(r, runtime),
    }
}

fn project_def_thm(result: &ExecDefThmStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecDefThmStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("def_thm")),
                (
                    "goal_well_defined",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                (
                    "proof_steps",
                    JsonValue::Array(
                        s.proof_steps
                            .iter()
                            .map(|step| project_stmt_detailed(step, runtime))
                            .collect(),
                    ),
                ),
                (
                    "conclusion_proofs",
                    project_verify_facts(&s.conclusion_proofs, runtime),
                ),
                (
                    "store_and_infer",
                    project_store_and_infer(&s.stored, runtime),
                ),
            ],
        ),
        ExecDefThmStmtResult::Failed(f) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("def_thm")),
                (
                    "failure",
                    super::theorem::project_def_thm_failure(f, runtime),
                ),
            ],
        ),
    }
}

fn project_def_struct(result: &ExecDefStructStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecDefStructStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("def_struct")),
                ("statement", string(s.statement.readable_string())),
                (
                    "definition_facts",
                    JsonValue::Array(
                        s.definition_facts
                            .iter()
                            .map(|published| {
                                object_for(
                                    runtime,
                                    vec![
                                        (
                                            "source_fact_id",
                                            string(published.source_fact_id.to_string()),
                                        ),
                                        (
                                            "fact_id",
                                            string(
                                                published
                                                    .store_and_infer
                                                    .store
                                                    .primary_fact_id()
                                                    .to_string(),
                                            ),
                                        ),
                                        (
                                            "facts",
                                            JsonValue::Array(
                                                crate::json_output::helper::store_fact_texts(
                                                    &published.store_and_infer.store,
                                                )
                                                .into_iter()
                                                .map(string)
                                                .collect(),
                                            ),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
                (
                    "fields",
                    JsonValue::Array(
                        s.field_scope
                            .fields
                            .iter()
                            .zip(&s.statement.fields)
                            .map(|(proof, field)| {
                                object_for(
                                    runtime,
                                    vec![
                                        ("name", string(&field.binding.name)),
                                        (
                                            "well_defined",
                                            project_obj_wd_proof(&proof.well_defined, runtime),
                                        ),
                                        (
                                            "local_definition",
                                            project_have_store_ids(
                                                &proof.defined.stored_fact_ids,
                                                runtime,
                                            ),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
                (
                    "equivalent_facts",
                    JsonValue::Array(
                        s.field_scope
                            .equivalent_facts
                            .iter()
                            .zip(&s.statement.equivalent_facts)
                            .map(|(proof, fact)| {
                                object_for(
                                    runtime,
                                    vec![
                                        (
                                            "well_defined",
                                            project_fact_wd_proof(&proof.well_defined, runtime),
                                        ),
                                        (
                                            "local_store",
                                            object_for(
                                                runtime,
                                                vec![
                                                    (
                                                        "fact_id",
                                                        string(
                                                            proof
                                                                .store
                                                                .primary_fact_id()
                                                                .to_string(),
                                                        ),
                                                    ),
                                                    ("fact", string(fact.readable_string())),
                                                ],
                                            ),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
            ],
        ),
        ExecDefStructStmtResult::Failed(_) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("def_struct")),
            ],
        ),
    }
}

fn project_axiom(result: &ExecAxiomStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecAxiomStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("axiom")),
                (
                    "goal_well_defined",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                (
                    "store_and_infer",
                    project_store_and_infer(&s.stored, runtime),
                ),
            ],
        ),
        ExecAxiomStmtResult::Failed(_) => object_for(
            runtime,
            vec![("success", bool_value(false)), ("kind", string("axiom"))],
        ),
    }
}

fn project_def_strategy(result: &ExecDefStrategyStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecDefStrategyStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("def_strategy")),
                (
                    "goal_well_defined",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                (
                    "conclusion_proofs",
                    project_verify_facts(&s.conclusion_proofs, runtime),
                ),
            ],
        ),
        ExecDefStrategyStmtResult::Failed(_) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("def_strategy")),
            ],
        ),
    }
}

fn project_define_obj(def: &ExecDefineObjStmtResult, runtime: &Runtime) -> JsonValue {
    match def {
        ExecDefineObjStmtResult::LetObj(r) => project_let_obj(r, runtime),
        ExecDefineObjStmtResult::HaveObjInNonemptySet(r) => {
            super::entry::project_have_in_nonempty_only(r, runtime)
        }
        ExecDefineObjStmtResult::HaveObjEqual(r) => {
            super::entry::project_have_equal_only(r, runtime)
        }
        ExecDefineObjStmtResult::HaveObjByExistFacts(r) => match r {
            ExecHaveObjByExistFactsStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("have_obj_by_exist_facts")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecHaveObjByExistFactsStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("have_obj_by_exist_facts")),
                ],
            ),
        },
        ExecDefineObjStmtResult::ObtainObjFromExistFact(r) => match r {
            ExecObtainObjFromExistFactStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("obtain_obj_from_exist_fact")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecObtainObjFromExistFactStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("obtain_obj_from_exist_fact")),
                ],
            ),
        },
        ExecDefineObjStmtResult::ObtainObjFromAtomicFact(r) => match r {
            ExecObtainObjFromAtomicFactStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("obtain_obj_from_atomic_fact")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecObtainObjFromAtomicFactStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("obtain_obj_from_atomic_fact")),
                ],
            ),
        },
        ExecDefineObjStmtResult::HaveByFnPreimage(r) => match r {
            ExecHaveByFnPreimageStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("have_by_fn_preimage")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecHaveByFnPreimageStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("have_by_fn_preimage")),
                ],
            ),
        },
        ExecDefineObjStmtResult::HaveByReplacementAxiom(r) => match r {
            ExecHaveByReplacementAxiomStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("have_by_replacement_axiom")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "store_and_infer",
                        project_have_store_ids(&s.stored_fact_ids, runtime),
                    ),
                ],
            ),
            ExecHaveByReplacementAxiomStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("have_by_replacement_axiom")),
                ],
            ),
        },
    }
}

fn project_let_obj(result: &ExecLetObjStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecLetObjStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("let_obj")),
                ("statement", string(s.statement.readable_string())),
                (
                    "value_well_defined",
                    project_verify_obj_wd(&s.value_well_defined, runtime),
                ),
                (
                    "store_and_infer",
                    project_have_store_ids(&s.stored_fact_ids, runtime),
                ),
            ],
        ),
        ExecLetObjStmtResult::Failed(wd) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("let_obj")),
                ("value_well_defined", project_verify_obj_wd(wd, runtime)),
            ],
        ),
    }
}

fn project_def_prop(result: &ExecDefPropStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecDefPropStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("def_prop")),
                ("statement", string(s.statement.readable_string())),
                (
                    "param_type_well_defined",
                    JsonValue::Array(
                        s.param_type_well_defined
                            .iter()
                            .map(|p| project_param_type_wd(p, runtime))
                            .collect(),
                    ),
                ),
                (
                    "defined_params",
                    project_have_store_ids(&s.defined_params.stored_fact_ids, runtime),
                ),
                (
                    "iff_fact_well_defined",
                    JsonValue::Array(
                        s.iff_fact_well_defined
                            .iter()
                            .map(|p| project_fact_wd_proof(p, runtime))
                            .collect(),
                    ),
                ),
            ],
        ),
        ExecDefPropStmtResult::Failed(failed) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("def_prop")),
                ("failure", project_def_prop_failure(failed, runtime)),
            ],
        ),
    }
}

pub(in crate::json_output) fn project_def_prop_failure(
    failed: &crate::execute::execute_def_prop_stmt::ExecDefPropStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_def_prop_stmt::ExecDefPropStmtFailed;
    let (phase, failure) = match failed {
        ExecDefPropStmtFailed::ParamType(wd) => {
            ("parameter_type", project_verify_obj_wd(wd, runtime))
        }
        ExecDefPropStmtFailed::AutoOpenStructLayer(failed) => (
            "auto_open_struct_layer",
            object_for(
                runtime,
                vec![
                    ("obj", string(failed.obj.readable_string())),
                    ("struct_obj", string(failed.struct_obj.readable_string())),
                    ("reason", string(&failed.reason)),
                ],
            ),
        ),
        ExecDefPropStmtFailed::IffFactWellDefined(wd) => (
            "iff_fact_well_defined",
            super::wd_failure::project_fact_wd_failure(wd, runtime),
        ),
    };
    object_for(
        runtime,
        vec![("phase", string(phase)), ("failure", failure)],
    )
}

fn project_def_abstract_prop(
    result: &ExecDefAbstractPropStmtSuccessResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("success", bool_value(true)),
            ("kind", string("def_abstract_prop")),
            ("statement", string(result.statement.readable_string())),
        ],
    )
}

fn project_witness(result: &ExecWitnessStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecWitnessStmtResult::WitnessExistFact(r) => match r {
            crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtResult::Success(s) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(true)),
                        ("kind", string("witness_exist_fact")),
                        ("statement", string(s.statement.readable_string())),
                        (
                            "exist_fact_well_defined",
                            project_fact_wd_proof(&s.ambient.exist_fact_well_defined, runtime),
                        ),
                        (
                            "witness_obj_well_defined",
                            JsonValue::Array(
                                s.ambient
                                    .witness_obj_well_defined
                                    .iter()
                                    .map(|wd| project_verify_obj_wd(wd, runtime))
                                    .collect(),
                            ),
                        ),
                        (
                            "witness_type_checks",
                            project_verify_facts(&s.ambient.witness_type_checks, runtime),
                        ),
                        ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                        (
                            "body_checks",
                            project_verify_facts(&s.obligations.body_checks, runtime),
                        ),
                        (
                            "uniqueness_check",
                            s.obligations
                                .uniqueness_check
                                .as_ref()
                                .map(|check| project_verify_fact(check, runtime))
                                .unwrap_or(JsonValue::Null),
                        ),
                        (
                            "store_and_infer",
                            project_store_and_infer(&s.store_and_infer_result, runtime),
                        ),
                    ],
                )
            }
            crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtResult::Failed(f) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(false)),
                        ("kind", string("witness_exist_fact")),
                        (
                            "failure",
                            super::witness_failure::project_witness_exist_failure(f, runtime),
                        ),
                    ],
                )
            }
        },
        ExecWitnessStmtResult::WitnessAtomicFact(r) => match r {
            crate::execute::execute_witness_stmt::ExecWitnessAtomicFactStmtResult::Success(s) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(true)),
                        ("kind", string("witness_atomic_fact")),
                        ("statement", string(s.statement.readable_string())),
                        (
                            "prop_argument_type_checks",
                            project_verify_facts(&s.prop_argument_type_checks, runtime),
                        ),
                        (
                            "projected_exist",
                            string(crate::ast::fact::exist_shaped_fact_to_fact(
                                &s.projected_exist,
                            ).readable_string()),
                        ),
                        (
                            "exist_fact_well_defined",
                            project_fact_wd_proof(&s.ambient.exist_fact_well_defined, runtime),
                        ),
                        (
                            "witness_obj_well_defined",
                            JsonValue::Array(
                                s.ambient
                                    .witness_obj_well_defined
                                    .iter()
                                    .map(|wd| project_verify_obj_wd(wd, runtime))
                                    .collect(),
                            ),
                        ),
                        (
                            "witness_type_checks",
                            project_verify_facts(&s.ambient.witness_type_checks, runtime),
                        ),
                        ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                        (
                            "body_checks",
                            project_verify_facts(&s.obligations.body_checks, runtime),
                        ),
                        (
                            "uniqueness_check",
                            s.obligations
                                .uniqueness_check
                                .as_ref()
                                .map(|check| project_verify_fact(check, runtime))
                                .unwrap_or(JsonValue::Null),
                        ),
                        (
                            "store_and_infer",
                            project_store_and_infer(&s.store_and_infer_result, runtime),
                        ),
                    ],
                )
            }
            crate::execute::execute_witness_stmt::ExecWitnessAtomicFactStmtResult::Failed(f) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(false)),
                        ("kind", string("witness_atomic_fact")),
                        (
                            "failure",
                            super::witness_failure::project_witness_atomic_failure(f, runtime),
                        ),
                    ],
                )
            }
        },
        ExecWitnessStmtResult::WitnessNonemptySet(r) => match r {
            crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult::Success(s) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(true)),
                        ("kind", string("witness_nonempty_set")),
                        ("statement", string(s.statement.readable_string())),
                        (
                            "obj_well_defined",
                            project_verify_obj_wd(&s.obj_well_defined, runtime),
                        ),
                        (
                            "set_well_defined",
                            project_verify_obj_wd(&s.set_well_defined, runtime),
                        ),
                        ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                        (
                            "membership_check",
                            project_verify_fact(&s.membership_check, runtime),
                        ),
                        (
                            "store_and_infer",
                            project_store_and_infer(&s.store_and_infer_result, runtime),
                        ),
                    ],
                )
            }
            crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult::Failed(f) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(false)),
                        ("kind", string("witness_nonempty_set")),
                        (
                            "failure",
                            super::witness_failure::project_witness_nonempty_failure(f, runtime),
                        ),
                    ],
                )
            }
        },
    }
}

fn project_trust(result: &ExecTrustBoundaryStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecTrustBoundaryStmtResult::TrustStmt(r) => match r {
            crate::execute::execute_unsafe_stmt::ExecTrustStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("trust")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "facts_well_defined",
                        JsonValue::Array(
                            s.facts_well_defined
                                .iter()
                                .map(|p| project_fact_wd_proof(p, runtime))
                                .collect(),
                        ),
                    ),
                    (
                        "store_and_infer_results",
                        JsonValue::Array(
                            s.store_and_infer_results
                                .iter()
                                .map(|n| project_store_and_infer(n, runtime))
                                .collect(),
                        ),
                    ),
                ],
            ),
            crate::execute::execute_unsafe_stmt::ExecTrustStmtResult::Failed(_) => object_for(
                runtime,
                vec![("success", bool_value(false)), ("kind", string("trust"))],
            ),
        },
        ExecTrustBoundaryStmtResult::TrustHaveStmt(r) => match r {
            crate::execute::execute_unsafe_stmt::ExecTrustHaveStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("trust_have")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "defined_param_store_and_infer",
                        project_have_store_ids(
                            &s.defined_param_store_and_infer.stored_fact_ids,
                            runtime,
                        ),
                    ),
                    (
                        "body_facts_well_defined",
                        JsonValue::Array(
                            s.body_facts_well_defined
                                .iter()
                                .map(|p| project_fact_wd_proof(p, runtime))
                                .collect(),
                        ),
                    ),
                    (
                        "body_store_and_infer_results",
                        JsonValue::Array(
                            s.body_store_and_infer_results
                                .iter()
                                .map(|n| project_store_and_infer(n, runtime))
                                .collect(),
                        ),
                    ),
                ],
            ),
            crate::execute::execute_unsafe_stmt::ExecTrustHaveStmtResult::Failed(_) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("trust_have")),
                ],
            ),
        },
    }
}

fn project_by(result: &ExecByStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByStmtResult::Cases(r) => project_by_cases(r, runtime),
        ExecByStmtResult::Contra(r) => project_by_contra(r, runtime),
        ExecByStmtResult::Def(r) => project_by_def(r, runtime),
        ExecByStmtResult::Extension(r) => project_by_extension(r, runtime),
        ExecByStmtResult::FnExtension(r) => project_by_fn_extension(r, runtime),
        ExecByStmtResult::EnumerateFiniteSet(r) => project_by_enumerate(r, runtime),
        ExecByStmtResult::For(r) => project_by_for(r, runtime),
        ExecByStmtResult::Thm(r) => project_by_thm(r, runtime),
        ExecByStmtResult::Induc(r) => project_by_induc("by_induc", r, runtime),
        ExecByStmtResult::StrongInduc(r) => project_by_strong_induc(r, runtime),
    }
}

fn project_stmt_steps(steps: &[ExecStmtResult], runtime: &Runtime) -> JsonValue {
    JsonValue::Array(
        steps
            .iter()
            .map(|step| project_stmt_detailed(step, runtime))
            .collect(),
    )
}

fn project_by_extension(result: &ExecByExtensionStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByExtensionStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_extension")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                (
                    "left_to_right",
                    project_verify_fact(&s.left_to_right, runtime),
                ),
                (
                    "right_to_left",
                    project_verify_fact(&s.right_to_left, runtime),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByExtensionStmtResult::Failed(failure) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_extension")),
                (
                    "failure",
                    super::proof_block_failure::project_extension_failure(failure, runtime),
                ),
            ],
        ),
    }
}

fn project_by_fn_extension(result: &ExecByFnExtensionStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByFnExtensionStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_fn_extension")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                (
                    "carrier",
                    string(crate::display_and_ir::readable_string_from_ir_text(
                        s.carrier.ir().as_str(),
                    )),
                ),
                ("right_domain", super::function_domain::project_source(&s.right_domain, runtime)),
                ("function_domain", super::function_domain::project_function_domain(&s.domain_match, runtime)),
                ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                (
                    "pointwise_proof",
                    project_verify_fact(&s.pointwise_proof, runtime),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByFnExtensionStmtResult::Failed(failed) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_fn_extension")),
                ("failure", match failed {
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::GoalWd(result) => object_for(runtime, vec![
                        ("phase", string("goal_well_defined")), ("result", project_verify_fact_wd_result(result, runtime)),
                    ]),
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::NoCompatibleFnSet => object_for(runtime, vec![("phase", string("function_space_unavailable"))]),
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::DomainMatch(candidates) => object_for(runtime, vec![
                        ("phase", string("function_domain")),
                        ("candidates", JsonValue::Array(candidates.iter().map(|candidate| object_for(runtime, vec![
                            ("right_domain", super::function_domain::project_source(&candidate.right_source, runtime)),
                            ("result", super::function_domain::project_function_domain_failure(&candidate.result, runtime)),
                        ])).collect())),
                    ]),
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::ProofBody(f) => object_for(runtime, vec![
                        ("phase", string("proof_body")), ("index", JsonValue::Number(f.step_index as f64)),
                        ("result", project_stmt_detailed(&f.result, runtime)),
                    ]),
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::Pointwise(result) => object_for(runtime, vec![
                        ("phase", string("pointwise")), ("result", project_verify_fact(result, runtime)),
                    ]),
                    crate::execute::execute_by_stmt::ExecByFnExtensionStmtFailed::Store(message) => object_for(runtime, vec![
                        ("phase", string("store")), ("message", string(message.clone())),
                    ]),
                }),
            ],
        ),
    }
}

fn project_by_contra(result: &ExecByContraStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByContraStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_contra")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                ("goal", string(s.goal.readable_string())),
                (
                    "reverse_assumption",
                    string(s.reverse_assumption.readable_string()),
                ),
                (
                    "reverse_assumption_fact_id",
                    string(s.reverse_assumption_fact_id.to_string()),
                ),
                (
                    "negation_assumed",
                    project_store_and_infer(&s.negation_assumed, runtime),
                ),
                ("proof_steps", project_stmt_steps(&s.proof_steps, runtime)),
                (
                    "closing",
                    object_for(
                        runtime,
                        vec![
                            ("fact", string(s.closing.impossible_fact.readable_string())),
                            (
                                "impossible",
                                project_verify_fact(&s.closing.impossible, runtime),
                            ),
                            (
                                "negated_impossible",
                                project_verify_fact(&s.closing.negated_impossible, runtime),
                            ),
                        ],
                    ),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByContraStmtResult::Failed(failed) => {
            let mut entries = vec![
                ("success", bool_value(false)),
                ("kind", string("by_contra")),
                (
                    "failure",
                    super::proof_block_failure::project_contra_failure(failed, runtime),
                ),
            ];
            if let ExecByContraStmtFailed::Closing(closing) = failed {
                let failure = match closing {
                    ByContradictionClosingFailed::Impossible(proof) => object_for(
                        runtime,
                        vec![
                            ("phase", string("impossible")),
                            ("verification", project_verify_fact(proof, runtime)),
                        ],
                    ),
                    ByContradictionClosingFailed::NegateImpossibleUnsupported(message) => {
                        object_for(
                            runtime,
                            vec![
                                ("phase", string("negate_impossible")),
                                ("message", string(message)),
                            ],
                        )
                    }
                    ByContradictionClosingFailed::NegatedImpossible(proof) => object_for(
                        runtime,
                        vec![
                            ("phase", string("negated_impossible")),
                            ("verification", project_verify_fact(proof, runtime)),
                        ],
                    ),
                };
                entries.push(("closing", failure));
            }
            object_for(runtime, entries)
        }
    }
}

fn project_by_cases(result: &ExecByCasesStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByCasesStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_cases")),
                (
                    "then_facts_wd",
                    JsonValue::Array(
                        s.then_facts_wd
                            .iter()
                            .map(|w| project_verify_fact_wd_result(w, runtime))
                            .collect(),
                    ),
                ),
                ("coverage", project_verify_fact(&s.coverage, runtime)),
                (
                    "stored",
                    JsonValue::Array(
                        s.stored
                            .iter()
                            .map(|n| project_store_and_infer(n, runtime))
                            .collect(),
                    ),
                ),
            ],
        ),
        ExecByCasesStmtResult::Failed(failure) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_cases")),
                (
                    "failure",
                    super::proof_block_failure::project_cases_failure(failure, runtime),
                ),
            ],
        ),
    }
}

fn project_by_def(result: &ExecByDefStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByDefStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_def")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                ("proof", project_verify_fact(&s.proof, runtime)),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByDefStmtResult::Failed(_) => object_for(
            runtime,
            vec![("success", bool_value(false)), ("kind", string("by_def"))],
        ),
    }
}

fn project_by_thm(result: &ExecByThmStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByThmStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_thm")),
                ("thm_name", string(s.call.name.local_name().to_string())),
                ("call", super::theorem::project_theorem_call(&s.call, runtime)),
                (
                    "builtin",
                    super::theorem::project_builtin_application(&s.builtin, runtime),
                ),
                (
                    "conclusions_wd",
                    super::theorem::project_conclusions_wd(&s.conclusions_wd, runtime),
                ),
                ("type_proofs", project_verify_facts(&s.type_proofs, runtime)),
                ("function_domain", s.function_domain.as_ref().map(|p| super::theorem::project_builtin_function_domain(p, runtime)).unwrap_or(JsonValue::Null)),
                ("dom_proofs", project_verify_facts(&s.dom_proofs, runtime)),
                (
                    "selected_proof",
                    project_verify_fact(&s.selected_proof, runtime),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByThmStmtResult::Failed(f) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_thm")),
                (
                    "failure",
                    super::theorem::project_by_thm_failure(f, runtime),
                ),
            ],
        ),
    }
}

fn project_by_enumerate(
    result: &ExecByEnumerateFiniteSetStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    match result {
        ExecByEnumerateFiniteSetStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_enumerate_finite_set")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                (
                    "assignments",
                    project_enumeration_assignments(&s.assignments, runtime),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByEnumerateFiniteSetStmtResult::Failed(_) => object_for(
            runtime,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_enumerate_finite_set")),
            ],
        ),
    }
}

fn project_by_for(result: &ExecByForStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecByForStmtResult::Success(s) => object_for(
            runtime,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_for")),
                (
                    "goal_wd",
                    project_verify_fact_wd_result(&s.goal_wd, runtime),
                ),
                (
                    "assignments",
                    project_enumeration_assignments(&s.assignments, runtime),
                ),
                ("stored", project_store_and_infer(&s.stored, runtime)),
            ],
        ),
        ExecByForStmtResult::Failed(_) => object_for(
            runtime,
            vec![("success", bool_value(false)), ("kind", string("by_for"))],
        ),
    }
}

fn project_enumeration_assignments(
    assignments: &[crate::execute::execute_by_stmt::EnumerateAssignmentSuccess],
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_by_stmt::EnumerateAssignmentOutcome;
    JsonValue::Array(
        assignments
            .iter()
            .map(|assignment| {
                let (premises, outcome) = match &assignment.outcome {
                    EnumerateAssignmentOutcome::Skipped {
                        premise_assumptions,
                        premise_index,
                        negated_premise,
                    } => (
                        premise_assumptions,
                        object_for(
                            runtime,
                            vec![
                                ("kind", string("skipped_false_premise")),
                                ("premise_index", string(premise_index.to_string())),
                                (
                                    "negated_premise",
                                    project_verify_fact(negated_premise, runtime),
                                ),
                            ],
                        ),
                    ),
                    EnumerateAssignmentOutcome::Proved {
                        premise_assumptions,
                        proof_steps,
                        then_proofs,
                    } => (
                        premise_assumptions,
                        object_for(
                            runtime,
                            vec![
                                ("kind", string("proved")),
                                ("proof_steps", project_stmt_steps(proof_steps, runtime)),
                                (
                                    "then_proofs",
                                    JsonValue::Array(
                                        then_proofs
                                            .iter()
                                            .map(|proof| {
                                                object_for(
                                                    runtime,
                                                    vec![
                                                        (
                                                            "verify_result",
                                                            project_verify_fact(
                                                                &proof.verify_result,
                                                                runtime,
                                                            ),
                                                        ),
                                                        (
                                                            "store_and_infer",
                                                            project_store_and_infer(
                                                                &proof.store_and_infer,
                                                                runtime,
                                                            ),
                                                        ),
                                                    ],
                                                )
                                            })
                                            .collect(),
                                    ),
                                ),
                            ],
                        ),
                    ),
                };
                let project_assumptions =
                    |facts: &[crate::execute::execute_fact_stmt::AssumeDomFactResult]| {
                        JsonValue::Array(
                            facts
                                .iter()
                                .map(|fact| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "well_defined",
                                                project_fact_wd_proof(&fact.well_defined, runtime),
                                            ),
                                            (
                                                "store_and_infer",
                                                project_store_and_infer(
                                                    &fact.store_and_infer,
                                                    runtime,
                                                ),
                                            ),
                                        ],
                                    )
                                })
                                .collect(),
                        )
                    };
                object_for(
                    runtime,
                    vec![
                        (
                            "param_type_well_defined",
                            JsonValue::Array(
                                assignment
                                    .introduced_params
                                    .param_type_well_defined
                                    .iter()
                                    .map(|proof| project_param_type_wd(proof, runtime))
                                    .collect(),
                            ),
                        ),
                        (
                            "binding_assumptions",
                            project_assumptions(&assignment.binding_assumptions),
                        ),
                        ("premise_assumptions", project_assumptions(premises)),
                        ("outcome", outcome),
                    ],
                )
            })
            .collect(),
    )
}

fn project_release_and_expand(
    result: &ExecReleaseAndExpandStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    if let ExecReleaseAndExpandStmtResult::TupleDef(result) = result {
        return project_release_tuple_def(result, runtime);
    }
    if let ExecReleaseAndExpandStmtResult::CartDef(result) = result {
        return project_release_cart_def(result, runtime);
    }
    if let ExecReleaseAndExpandStmtResult::Thm(result) = result {
        return super::theorem::project_release_thm(result, runtime);
    }
    let kind = match result {
        ExecReleaseAndExpandStmtResult::Thm(_) => "release_thm",
        ExecReleaseAndExpandStmtResult::StructDef(_) => "release_struct_def",
        ExecReleaseAndExpandStmtResult::ObjDef(_) => "release_obj_def",
        ExecReleaseAndExpandStmtResult::CartDef(_) => "release_cart_def",
        ExecReleaseAndExpandStmtResult::TupleDef(_) => "release_tuple_def",
        ExecReleaseAndExpandStmtResult::ExpandRange(_) => "expand_range",
        ExecReleaseAndExpandStmtResult::ZornLemma(_) => "release_zorn_lemma",
        ExecReleaseAndExpandStmtResult::AxiomOfChoice(_) => "release_axiom_of_choice",
        ExecReleaseAndExpandStmtResult::RegularityAxiom(_) => "release_regularity_axiom",
    };
    object_for(
        runtime,
        vec![
            ("success", bool_value(!result.is_failed())),
            ("kind", string(kind)),
        ],
    )
}

fn project_proof_block(result: &ExecProofBlockStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecProofBlockStmtResult::Claim(r) => match r {
            ExecClaimStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("claim")),
                    (
                        "goal_wd",
                        project_verify_fact_wd_result(&s.goal_wd, runtime),
                    ),
                    (
                        "proof_steps",
                        JsonValue::Array(
                            s.proof_steps
                                .iter()
                                .map(|step| project_stmt_detailed(step, runtime))
                                .collect(),
                        ),
                    ),
                    (
                        "conclusion_proofs",
                        project_verify_facts(&s.conclusion_proofs, runtime),
                    ),
                    ("stored", project_store_and_infer(&s.stored, runtime)),
                ],
            ),
            ExecClaimStmtResult::Failed(failure) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("claim")),
                    (
                        "failure",
                        super::proof_block_failure::project_claim_failure(failure, runtime),
                    ),
                ],
            ),
        },
        ExecProofBlockStmtResult::Sketch(r) => match r {
            ExecSketchStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("sketch")),
                    (
                        "proof_steps",
                        JsonValue::Array(
                            s.proof_steps
                                .iter()
                                .map(|step| project_stmt_detailed(step, runtime))
                                .collect(),
                        ),
                    ),
                ],
            ),
            ExecSketchStmtResult::Failed(failure) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("sketch")),
                    (
                        "failure",
                        super::proof_block_failure::project_sketch_failure(failure, runtime),
                    ),
                ],
            ),
        },
    }
}

fn project_command(result: &ExecCommandStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecCommandStmtResult::Eval(r) => match r {
            ExecEvalStmtResult::Success(s) => object_for(
                runtime,
                vec![
                    ("success", bool_value(true)),
                    ("kind", string("eval")),
                    ("statement", string(s.statement.readable_string())),
                    (
                        "aggregate_evaluations",
                        super::aggregate_evaluation::project_aggregate_evaluations(
                            &s.aggregate_evaluations,
                            runtime,
                        ),
                    ),
                    (
                        "function_evaluations",
                        super::aggregate_evaluation::project_function_evaluations(
                            &s.function_evaluations,
                            runtime,
                        ),
                    ),
                    (
                        "algo_evaluations",
                        super::aggregate_evaluation::project_algo_evaluations(
                            &s.algo_evaluations,
                            runtime,
                        ),
                    ),
                    ("source_object", string(s.source_object.readable_string())),
                    ("cite", super::aggregate_evaluation::cites(&s.cited_equal_fact_ids)),
                    (
                        "source_well_defined",
                        project_obj_wd_proof(&s.source_well_defined, runtime),
                    ),
                    (
                        "rewritten_object",
                        string(s.rewritten_object.readable_string()),
                    ),
                    (
                        "evaluated_object",
                        string(s.evaluated_object.readable_string()),
                    ),
                    ("fact", string(crate::ast::fact::Fact::from(s.evaluated_equal_fact.clone()).readable_string())),
                    ("fact_id", string(s.evaluated_equal_fact.fact_id.to_string())),
                    ("well_defined", object_for(runtime, vec![
                        ("left", project_obj_wd_proof(&s.evaluated_equal_well_defined.left, runtime)),
                        ("right", project_obj_wd_proof(&s.evaluated_equal_well_defined.right, runtime)),
                    ])),
                    ("store_and_infer", project_store_and_infer(&s.store_and_infer_result, runtime)),
                ],
            ),
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::WellDefined(failed)) => {
                object_for(
                    runtime,
                    vec![
                        ("success", bool_value(false)),
                        ("kind", string("eval")),
                        (
                            "source_well_defined",
                            project_verify_obj_wd(failed, runtime),
                        ),
                    ],
                )
            }
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::AlgorithmEquation(proof)) => object_for(
                runtime, vec![("success", bool_value(false)), ("kind", string("eval")),
                    ("verify", super::verify::project_verify_fact(proof, runtime))],
            ),
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::EvaluatedEqualityWellDefined(wd)) => object_for(
                runtime, vec![("success", bool_value(false)), ("kind", string("eval")),
                    ("well_defined", super::wd::project_verify_equal_wd(wd, runtime))],
            ),
            ExecEvalStmtResult::Failed(
                crate::execute::ExecEvalStmtFailed::AggregateBudgetExceeded,
            ) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("eval")),
                    ("cause", string("aggregate_budget_exceeded")),
                ],
            ),
            ExecEvalStmtResult::Failed(
                crate::execute::ExecEvalStmtFailed::AggregateRangeOverflow,
            ) => object_for(
                runtime,
                vec![
                    ("success", bool_value(false)),
                    ("kind", string("eval")),
                    ("cause", string("aggregate_range_overflow")),
                ],
            ),
            ExecEvalStmtResult::Failed(_) => object_for(
                runtime,
                vec![("success", bool_value(false)), ("kind", string("eval"))],
            ),
        },
    }
}

fn project_success_failed_shell(
    kind: &str,
    success: bool,
    statement: Option<String>,
    store: Option<JsonValue>,
    runtime: &Runtime,
) -> JsonValue {
    let mut entries = vec![("success", bool_value(success)), ("kind", string(kind))];
    if let Some(stmt) = statement {
        entries.push(("statement", string(stmt)));
    }
    if let Some(store) = store {
        entries.push(("store_and_infer", store));
    }
    object_for(runtime, entries)
}

#[allow(dead_code)]
fn project_param_type_fact_check(check: &ParamTypeFactCheckResult, runtime: &Runtime) -> JsonValue {
    match check {
        ParamTypeFactCheckResult::Set => object_for(runtime, vec![("type", string("set"))]),
        ParamTypeFactCheckResult::NonemptySet => {
            object_for(runtime, vec![("type", string("nonempty_set"))])
        }
        ParamTypeFactCheckResult::FiniteSet => {
            object_for(runtime, vec![("type", string("finite_set"))])
        }
        ParamTypeFactCheckResult::Obj(v) => object_for(
            runtime,
            vec![
                ("type", string("obj")),
                ("verify", project_verify_fact(v, runtime)),
            ],
        ),
    }
}

/// Failure payloads already produced by the cases executor, shared by both profiles.
pub(in crate::json_output) fn project_cases_definition_failure(
    failure: &crate::execute::ExecHaveFnEqualCaseByCaseStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::ExecHaveFnEqualCaseByCaseStmtFailed as F;
    let (phase, mut details) = match failure {
        F::CaseCountMismatch => ("case_count", vec![]),
        F::EmptyCases => ("empty_cases", vec![]),
        F::FnSetWellDefined(wd) => (
            "fn_set_well_defined",
            vec![("well_defined", project_verify_obj_wd(wd, runtime))],
        ),
        F::Coverage(proof) => (
            "coverage",
            vec![("verification", project_verify_fact(proof, runtime))],
        ),
        F::Disjoint { i, j } => (
            "disjoint",
            vec![
                ("case_index", JsonValue::Number((i + 1) as f64)),
                ("other_case_index", JsonValue::Number((j + 1) as f64)),
            ],
        ),
        F::CaseBodyWellDefined(i, wd) => (
            "case_body_well_defined",
            vec![
                ("case_index", JsonValue::Number((i + 1) as f64)),
                ("well_defined", project_verify_obj_wd(wd, runtime)),
            ],
        ),
        F::CaseBodyInRetSet(i, proof) => (
            "case_body_in_return_set",
            vec![
                ("case_index", JsonValue::Number((i + 1) as f64)),
                ("verification", project_verify_fact(proof, runtime)),
            ],
        ),
    };
    details.insert(0, ("phase", string(phase)));
    object_for(runtime, details)
}

pub(in crate::json_output) fn project_release_cart_def(
    result: &crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::VerifyEqualityFailed;
    match result {
        ExecReleaseCartDefStmtResult::Success(s) => object_for(runtime, vec![
            ("success", bool_value(true)), ("kind", string("release_cart_def")),
            ("statement", string(s.statement.readable_string())),
            ("fact", string(crate::ast::fact::Fact::from(s.verification.fact.clone()).readable_string())),
            ("fact_id", string(s.verification.fact.fact_id.to_string())),
            ("well_defined", super::wd::project_equal_wd_proof(&s.verification.well_defined_proof, runtime)),
            ("searched_proof", super::searched::project_equal_searched(&s.verification.searched_proof, runtime)),
            ("store_and_infer", super::store::project_store_and_infer(&s.store_and_infer, runtime)),
        ]),
        ExecReleaseCartDefStmtResult::Failed(reason) => {
            let (phase, details) = match reason {
                VerifyEqualityFailed::FailToVerifyWellDefined(f) => ("well_defined", super::wd_failure::project_obj_wd_failure(&f.reason, runtime)),
                VerifyEqualityFailed::FailToSearchProof { fact, well_defined_proof } => ("search_proof", object_for(runtime, vec![
                    ("fact", string(crate::ast::fact::Fact::from(fact.clone()).readable_string())),
                    ("well_defined", super::wd::project_equal_wd_proof(well_defined_proof, runtime)),
                ])),
            };
            object_for(runtime, vec![("success", bool_value(false)), ("kind", string("release_cart_def")), ("phase", string(phase)), ("failure", details)])
        }
    }
}


pub(in crate::json_output) fn project_release_tuple_def(
    result: &crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_release_tuple_def_stmt::{ExecReleaseTupleDefStmtResult as R, ExecReleaseTupleDefStmtFailed as F};
    match result {
        R::Success(s) => object_for(runtime, vec![
            ("success", bool_value(true)), ("kind", string("release_tuple_def")),
            ("statement", string(s.statement.readable_string())),
            ("shape", super::function_domain::project_finite_function_source(&s.shape, runtime)),
            ("complete_domain", super::function_domain::project_function_domain(&s.domain, runtime)),
            ("membership_rule", super::theorem::project_builtin_application_value(&s.membership_rule, runtime)),
            ("return_proofs", project_verify_facts(&s.return_proofs, runtime)),
            ("membership_well_defined", project_fact_wd_proof(&s.membership_wd, runtime)),
            ("coordinate_proofs", project_verify_facts(&s.coordinate_proofs, runtime)),
            ("stored", JsonValue::Array(s.stored.iter().map(|store| project_store_and_infer(store, runtime)).collect())),
        ]),
        R::Failed(failure) => {
            let (phase, details) = match failure {
                F::Shape => ("shape", object_for(runtime, vec![("reason", string("no_checked_tuple_shape"))])),
                F::Domain(f) => ("complete_domain", super::function_domain::project_function_domain_failure(f, runtime)),
                F::Requirements(message) => ("return_requirements", object_for(runtime, vec![("message", string(message))])),
                F::Return { fact, result } => ("return_bound", object_for(runtime, vec![("fact", string(fact.readable_string())), ("verification", project_verify_fact(result, runtime))])),
                F::MembershipWd(result) => ("membership_well_defined", project_verify_fact_wd_result(result, runtime)),
                F::Coordinate { fact, result } => ("coordinate", object_for(runtime, vec![("fact", string(fact.readable_string())), ("verification", project_verify_fact(result, runtime))])),
            };
            object_for(runtime, vec![("success", bool_value(false)), ("kind", string("release_tuple_def")), ("phase", string(phase)), ("failure", details)])
        }
    }
}
