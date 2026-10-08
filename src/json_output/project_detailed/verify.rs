//! VerifyFactResult detailed projection.

use super::searched::{
    project_atomic_except_searched, project_equal_searched, project_exist_searched,
    project_or_searched,
};
use super::store::{project_store_and_infer, project_verify_facts};
use super::wd::{
    project_atomic_wd_proof, project_equal_wd_proof, project_fact_wd_proof, project_param_type_wd,
};
use crate::ast::fact::{AtomicFact, ExistShapedFact, Fact};
use crate::execute::execute_fact_stmt::verify_and_fact::{
    VerifyAndFactFailed, VerifyAndFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    VerifyAtomicExceptEqualityFactFailed, VerifyAtomicExceptEqualityFactResult,
    VerifyEqualityFailed, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_chain_fact::{
    VerifyChainFactFailed, VerifyChainFactResult,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyExistUniqueFactResult,
    VerifyNotExistFactResult, VerifyPlainExistFactResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    AssumeDomFactResult, ProveAndStoreThenFactResult, VerifyForallFactFailed,
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    VerifyForallFactWithIffFailed, VerifyForallFactWithIffResult,
};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::{
    VerifyNotForallFactFailed, VerifyNotForallFactResult,
};
use crate::execute::execute_fact_stmt::verify_or_fact::{VerifyOrFactFailed, VerifyOrFactResult};
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::execute::IntroduceTypedParametersResult;
use crate::json_output::helper::{bool_value, object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(in crate::json_output) fn project_verify_fact(
    verify: &VerifyFactResult,
    runtime: &Runtime,
) -> JsonValue {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => project_atomic_except(r, runtime),
        VerifyFactResult::Equality(r) => project_equality(r, runtime),
        VerifyFactResult::AndFact(r) => project_and(r, runtime),
        VerifyFactResult::ChainFact(r) => project_chain(r, runtime),
        VerifyFactResult::OrFact(r) => project_or(r, runtime),
        VerifyFactResult::ExistShapedFact(r) => project_exist_shaped(r, runtime),
        VerifyFactResult::ForallFact(r) => project_forall(r, runtime),
        VerifyFactResult::ForallFactWithIff(r) => project_forall_iff(r, runtime),
        VerifyFactResult::NotForall(r) => project_not_forall(r, runtime),
    }
}

pub(super) fn project_atomic_except_success(
    s: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactSuccess,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("type", string("atomic_except_equality")),
            ("success", bool_value(true)),
            ("fact", string(s.fact.readable_string())),
            (
                "well_defined",
                project_atomic_wd_proof(&s.well_defined_proof, runtime),
            ),
            (
                "searched_proof",
                project_atomic_except_searched(&s.searched_proof, runtime),
            ),
        ],
    )
}

fn project_atomic_except(
    result: &VerifyAtomicExceptEqualityFactResult,
    runtime: &Runtime,
) -> JsonValue {
    match result {
        VerifyAtomicExceptEqualityFactResult::Success(s) => {
            project_atomic_except_success(s, runtime)
        }
        VerifyAtomicExceptEqualityFactResult::Failed(
            VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(f),
        ) => object_for(
            runtime,
            vec![
                ("type", string("atomic_except_equality")),
                ("success", bool_value(false)),
                ("phase", string("well_defined")),
                (
                    "failure",
                    super::wd_failure::project_atomic_wd_failure(f, runtime),
                ),
            ],
        ),
        VerifyAtomicExceptEqualityFactResult::Failed(
            VerifyAtomicExceptEqualityFactFailed::FailToSearchProof {
                fact,
                well_defined_proof,
            },
        ) => object_for(
            runtime,
            vec![
                ("type", string("atomic_except_equality")),
                ("success", bool_value(false)),
                ("phase", string("search_proof")),
                ("fact", string(fact.readable_string())),
                (
                    "well_defined",
                    project_atomic_wd_proof(well_defined_proof, runtime),
                ),
            ],
        ),
    }
}

fn project_equality(result: &VerifyEqualityResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyEqualityResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("equality")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(AtomicFact::EqualFact(s.fact.clone()).readable_string()),
                ),
                (
                    "well_defined",
                    project_equal_wd_proof(&s.well_defined_proof, runtime),
                ),
                (
                    "searched_proof",
                    project_equal_searched(&s.searched_proof, runtime),
                ),
            ],
        ),
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(f)) => {
            object_for(
                runtime,
                vec![
                    ("type", string("equality")),
                    ("success", bool_value(false)),
                    ("phase", string("well_defined")),
                    (
                        "failure",
                        super::wd_failure::project_obj_wd_failure(&f.reason, runtime),
                    ),
                ],
            )
        }
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
            fact,
            well_defined_proof,
        }) => object_for(
            runtime,
            vec![
                ("type", string("equality")),
                ("success", bool_value(false)),
                ("phase", string("search_proof")),
                (
                    "fact",
                    string(AtomicFact::EqualFact(fact.clone()).readable_string()),
                ),
                (
                    "well_defined",
                    project_equal_wd_proof(well_defined_proof, runtime),
                ),
            ],
        ),
    }
}

fn project_and(result: &VerifyAndFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyAndFactResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("and")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::AndFact(s.fact.clone()).readable_string()),
                ),
                ("components", project_verify_facts(&s.components, runtime)),
            ],
        ),
        VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToVerifyWellDefined {
            fact,
            failed_index,
            succeeded_components,
            failed_component,
        })
        | VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToSearchProof {
            fact,
            failed_index,
            succeeded_components,
            failed_component,
        }) => {
            let phase = if matches!(
                result,
                VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToVerifyWellDefined { .. })
            ) {
                "well_defined"
            } else {
                "search_proof"
            };
            object_for(
                runtime,
                vec![
                    ("type", string("and")),
                    ("success", bool_value(false)),
                    ("phase", string(phase)),
                    (
                        "fact",
                        string(Fact::AndFact(fact.clone()).readable_string()),
                    ),
                    ("failed_index", JsonValue::Number(*failed_index as f64)),
                    (
                        "succeeded_components",
                        project_verify_facts(succeeded_components, runtime),
                    ),
                    (
                        "failed_component",
                        project_verify_fact(failed_component, runtime),
                    ),
                ],
            )
        }
    }
}

fn project_chain(result: &VerifyChainFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyChainFactResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("chain")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::ChainFact(s.fact.clone()).readable_string()),
                ),
                ("adjacent", project_verify_facts(&s.adjacent, runtime)),
            ],
        ),
        VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToVerifyWellDefined {
            fact,
            failed_index,
            succeeded_adjacent,
            failed_adjacent,
        })
        | VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToSearchProof {
            fact,
            failed_index,
            succeeded_adjacent,
            failed_adjacent,
        }) => {
            let phase = if matches!(
                result,
                VerifyChainFactResult::Failed(
                    VerifyChainFactFailed::FailToVerifyWellDefined { .. }
                )
            ) {
                "well_defined"
            } else {
                "search_proof"
            };
            object_for(
                runtime,
                vec![
                    ("type", string("chain")),
                    ("success", bool_value(false)),
                    ("phase", string(phase)),
                    (
                        "fact",
                        string(Fact::ChainFact(fact.clone()).readable_string()),
                    ),
                    ("failed_index", JsonValue::Number(*failed_index as f64)),
                    (
                        "succeeded_adjacent",
                        project_verify_facts(succeeded_adjacent, runtime),
                    ),
                    (
                        "failed_adjacent",
                        project_verify_fact(failed_adjacent, runtime),
                    ),
                ],
            )
        }
    }
}

fn project_or(result: &VerifyOrFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyOrFactResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("or")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::OrFact(s.fact.clone()).readable_string()),
                ),
                (
                    "well_defined",
                    super::wd::project_or_wd_proof(&s.well_defined_proof, runtime),
                ),
                (
                    "searched_proof",
                    project_or_searched(&s.searched_proof, runtime),
                ),
            ],
        ),
        VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToVerifyWellDefined(_)) => object_for(
            runtime,
            vec![
                ("type", string("or")),
                ("success", bool_value(false)),
                ("phase", string("well_defined")),
            ],
        ),
        VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToSearchProof {
            fact,
            well_defined_proof,
        }) => object_for(
            runtime,
            vec![
                ("type", string("or")),
                ("success", bool_value(false)),
                ("phase", string("search_proof")),
                ("fact", string(Fact::OrFact(fact.clone()).readable_string())),
                (
                    "well_defined",
                    super::wd::project_or_wd_proof(well_defined_proof, runtime),
                ),
            ],
        ),
    }
}

fn project_exist_shaped(result: &VerifyExistShapedFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyExistShapedFactResult::PlainExistFact(r) => match r {
            VerifyPlainExistFactResult::Success(s) => project_exist_success(
                "exist",
                s.fact.clone(),
                &s.well_defined_proof,
                &s.searched_proof,
                runtime,
            ),
            VerifyPlainExistFactResult::Failed(f) => project_exist_failed("exist", f, runtime),
        },
        VerifyExistShapedFactResult::ExistUniqueFact(r) => match r {
            VerifyExistUniqueFactResult::Success(s) => project_exist_success(
                "exist_unique",
                s.fact.clone(),
                &s.well_defined_proof,
                &s.searched_proof,
                runtime,
            ),
            VerifyExistUniqueFactResult::Failed(f) => {
                project_exist_failed("exist_unique", f, runtime)
            }
        },
        VerifyExistShapedFactResult::NotExistFact(r) => match r {
            VerifyNotExistFactResult::Success(s) => project_exist_success(
                "not_exist",
                s.fact.clone(),
                &s.well_defined_proof,
                &s.searched_proof,
                runtime,
            ),
            VerifyNotExistFactResult::Failed(f) => project_exist_failed("not_exist", f, runtime),
        },
    }
}

fn exist_fact_display(fact: &ExistShapedFact) -> String {
    match fact {
        ExistShapedFact::Exist(p) => Fact::ExistFact(p.clone()).readable_string(),
        ExistShapedFact::ExistUnique(p) => Fact::ExistUniqueFact(p.clone()).readable_string(),
        ExistShapedFact::NotExist(p) => Fact::NotExistFact(p.clone()).readable_string(),
    }
}

fn project_exist_success(
    kind: &str,
    fact: ExistShapedFact,
    wd: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof,
    searched: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("type", string(kind)),
            ("success", bool_value(true)),
            ("fact", string(exist_fact_display(&fact))),
            (
                "well_defined",
                super::wd::project_exist_wd_proof(wd, runtime),
            ),
            ("searched_proof", project_exist_searched(searched, runtime)),
        ],
    )
}

pub(super) fn project_exist_failed(
    kind: &str,
    failed: &VerifyExistShapedFactFailed,
    runtime: &Runtime,
) -> JsonValue {
    match failed {
        VerifyExistShapedFactFailed::FailToVerifyWellDefined(failure) => object_for(
            runtime,
            vec![
                ("type", string(kind)),
                ("success", bool_value(false)),
                ("phase", string("well_defined")),
                (
                    "failure",
                    super::wd_failure::project_exist_wd_failure(failure, runtime),
                ),
            ],
        ),
        VerifyExistShapedFactFailed::FailToSearchProof {
            fact,
            well_defined_proof,
        } => object_for(
            runtime,
            vec![
                ("type", string(kind)),
                ("success", bool_value(false)),
                ("phase", string("search_proof")),
                ("fact", string(exist_fact_display(fact))),
                (
                    "well_defined",
                    super::wd::project_exist_wd_proof(well_defined_proof, runtime),
                ),
            ],
        ),
    }
}

fn project_forall(result: &VerifyForallFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(s)) => {
            object_for(
                runtime,
                vec![
                    ("type", string("forall")),
                    ("success", bool_value(true)),
                    (
                        "fact",
                        string(Fact::ForallFact(s.fact.clone()).readable_string()),
                    ),
                    (
                        "searched_proof",
                        object_for(
                            runtime,
                            vec![
                                ("type", string("empty_parameter_domain")),
                                (
                                    "parameter_group_index",
                                    JsonValue::Number(s.parameter_group_index as f64),
                                ),
                                ("empty_carrier", string(s.empty_carrier.readable_string())),
                                (
                                    "empty_carrier_proof",
                                    project_verify_fact(&s.empty_carrier_proof, runtime),
                                ),
                                (
                                    "empty_carrier_store",
                                    super::store::project_store_and_infer(
                                        &s.empty_carrier_store,
                                        runtime,
                                    ),
                                ),
                                (
                                    "well_defined",
                                    super::wd::project_forall_wd(&s.well_defined, runtime),
                                ),
                            ],
                        ),
                    ),
                ],
            )
        }
        VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(s)) => {
            object_for(
                runtime,
                vec![
                    ("type", string("forall")),
                    ("success", bool_value(true)),
                    (
                        "fact",
                        string(Fact::ForallFact(s.fact.clone()).readable_string()),
                    ),
                    (
                        "introduced_params",
                        project_introduced_params(&s.introduced_params, runtime),
                    ),
                    (
                        "assumed_dom_facts",
                        JsonValue::Array(
                            s.assumed_dom_facts
                                .iter()
                                .map(|a| project_assume_dom(a, runtime))
                                .collect(),
                        ),
                    ),
                    (
                        "proved_then_facts",
                        JsonValue::Array(
                            s.proved_then_facts
                                .iter()
                                .map(|p| project_prove_then(p, runtime))
                                .collect(),
                        ),
                    ),
                ],
            )
        }
        VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(s)) => object_for(
            runtime,
            vec![
                ("type", string("forall")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::ForallFact(s.fact.clone()).readable_string()),
                ),
                (
                    "searched_proof",
                    object_for(
                        runtime,
                        vec![
                            ("type", string("by_known_forall_fact")),
                            ("cite_fact_id", string(s.cite_fact_id.to_string())),
                            (
                                "parameter_renamings",
                                JsonValue::Array(
                                    s.parameter_renamings
                                        .iter()
                                        .map(|r| {
                                            object_for(
                                                runtime,
                                                vec![
                                                    ("source", string(r.source.to_string())),
                                                    ("target", string(r.target.to_string())),
                                                ],
                                            )
                                        })
                                        .collect(),
                                ),
                            ),
                        ],
                    ),
                ),
                (
                    "well_defined",
                    super::wd::project_forall_wd(&s.well_defined, runtime),
                ),
            ],
        ),
        VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(reason)) => {
            object_for(
                runtime,
                vec![
                    ("type", string("forall")),
                    ("success", bool_value(false)),
                    ("phase", string("well_defined")),
                    (
                        "failure",
                        super::wd_failure::project_forall_wd_failure(reason, runtime),
                    ),
                ],
            )
        }
        VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
            fact,
            introduced_params,
            assumed_dom_facts,
            proved_then_facts,
            failed_then_index,
            failed_then,
            local_env: _,
        }) => object_for(
            runtime,
            vec![
                ("type", string("forall")),
                ("success", bool_value(false)),
                ("phase", string("search_proof")),
                (
                    "fact",
                    string(Fact::ForallFact(fact.clone()).readable_string()),
                ),
                (
                    "introduced_params",
                    project_introduced_params(introduced_params, runtime),
                ),
                (
                    "assumed_dom_facts",
                    JsonValue::Array(
                        assumed_dom_facts
                            .iter()
                            .map(|a| project_assume_dom(a, runtime))
                            .collect(),
                    ),
                ),
                (
                    "proved_then_facts",
                    JsonValue::Array(
                        proved_then_facts
                            .iter()
                            .map(|p| project_prove_then(p, runtime))
                            .collect(),
                    ),
                ),
                (
                    "failed_then_index",
                    JsonValue::Number(*failed_then_index as f64),
                ),
                ("failed_then", project_verify_fact(failed_then, runtime)),
            ],
        ),
    }
}

pub(super) fn project_introduced_params(
    introduced: &IntroduceTypedParametersResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "param_type_well_defined",
                JsonValue::Array(
                    introduced
                        .param_type_well_defined
                        .iter()
                        .map(|p| project_param_type_wd(p, runtime))
                        .collect(),
                ),
            ),
            (
                "defined_params",
                super::store::project_have_store_and_infer(&introduced.defined_params, runtime),
            ),
            (
                "auto_opened_struct_layers",
                JsonValue::Array(
                    introduced
                        .auto_opened_struct_layers
                        .iter()
                        .flatten()
                        .map(|opened| {
                            object_for(
                                runtime,
                                vec![
                                    ("obj", string(opened.obj.readable_string())),
                                    ("struct_obj", string(opened.struct_obj.readable_string())),
                                    (
                                        "store_and_infer",
                                        JsonValue::Array(
                                            opened
                                                .store_and_infer
                                                .iter()
                                                .map(|stored| {
                                                    project_store_and_infer(stored, runtime)
                                                })
                                                .collect(),
                                        ),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
        ],
    )
}

pub(super) fn project_assume_dom(assumed: &AssumeDomFactResult, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "well_defined",
                project_fact_wd_proof(&assumed.well_defined, runtime),
            ),
            (
                "store_and_infer",
                project_store_and_infer(&assumed.store_and_infer, runtime),
            ),
        ],
    )
}

fn project_prove_then(proved: &ProveAndStoreThenFactResult, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "verify_result",
                project_verify_fact(&proved.verify_result, runtime),
            ),
            (
                "store_and_infer",
                project_store_and_infer(&proved.store_and_infer, runtime),
            ),
        ],
    )
}

fn project_forall_iff(result: &VerifyForallFactWithIffResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyForallFactWithIffResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("forall_iff")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::ForallFactWithIff(s.fact.clone()).readable_string()),
                ),
                (
                    "then_implies_iff",
                    project_verify_fact(&s.then_implies_iff, runtime),
                ),
                (
                    "iff_implies_then",
                    project_verify_fact(&s.iff_implies_then, runtime),
                ),
            ],
        ),
        VerifyForallFactWithIffResult::Failed(
            VerifyForallFactWithIffFailed::FailThenImpliesIff {
                fact,
                then_implies_iff,
            },
        ) => object_for(
            runtime,
            vec![
                ("type", string("forall_iff")),
                ("success", bool_value(false)),
                ("phase", string("then_implies_iff")),
                (
                    "fact",
                    string(Fact::ForallFactWithIff(fact.clone()).readable_string()),
                ),
                (
                    "then_implies_iff",
                    project_verify_fact(then_implies_iff, runtime),
                ),
            ],
        ),
        VerifyForallFactWithIffResult::Failed(
            VerifyForallFactWithIffFailed::FailIffImpliesThen {
                fact,
                then_implies_iff,
                iff_implies_then,
            },
        ) => object_for(
            runtime,
            vec![
                ("type", string("forall_iff")),
                ("success", bool_value(false)),
                ("phase", string("iff_implies_then")),
                (
                    "fact",
                    string(Fact::ForallFactWithIff(fact.clone()).readable_string()),
                ),
                (
                    "then_implies_iff",
                    project_verify_fact(then_implies_iff, runtime),
                ),
                (
                    "iff_implies_then",
                    project_verify_fact(iff_implies_then, runtime),
                ),
            ],
        ),
    }
}

fn project_not_forall(result: &VerifyNotForallFactResult, runtime: &Runtime) -> JsonValue {
    match result {
        VerifyNotForallFactResult::Success(s) => object_for(
            runtime,
            vec![
                ("type", string("not_forall")),
                ("success", bool_value(true)),
                (
                    "fact",
                    string(Fact::NotForall(s.fact.clone()).readable_string()),
                ),
                (
                    "derived_exist",
                    string(exist_fact_display(&s.derived_exist)),
                ),
                (
                    "prove_derived_exist",
                    project_verify_fact(&s.prove_derived_exist, runtime),
                ),
            ],
        ),
        VerifyNotForallFactResult::Failed(VerifyNotForallFactFailed::UnsupportedNegation {
            fact,
        }) => object_for(
            runtime,
            vec![
                ("type", string("not_forall")),
                ("success", bool_value(false)),
                ("phase", string("unsupported_negation")),
                (
                    "fact",
                    string(Fact::NotForall(fact.clone()).readable_string()),
                ),
            ],
        ),
        VerifyNotForallFactResult::Failed(VerifyNotForallFactFailed::FailToProveDerivedExist {
            fact,
            derived_exist,
            prove_derived_exist,
        }) => object_for(
            runtime,
            vec![
                ("type", string("not_forall")),
                ("success", bool_value(false)),
                ("phase", string("prove_derived_exist")),
                (
                    "fact",
                    string(Fact::NotForall(fact.clone()).readable_string()),
                ),
                ("derived_exist", string(exist_fact_display(derived_exist))),
                (
                    "prove_derived_exist",
                    project_verify_fact(prove_derived_exist, runtime),
                ),
            ],
        ),
    }
}
