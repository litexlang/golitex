use super::store::{project_have_store_and_infer, project_have_store_ids, project_store_and_infer};
use super::verify::project_verify_fact;
use super::wd::project_verify_obj_wd;
use crate::json_output::helper::{object_for, statement_result_value, string};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;

pub(super) fn project_have_fn_cases(
    result: &ExecHaveFnEqualCaseByCaseStmtSuccessResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("statement_result", statement_result_value(true)),
            ("kind", string("have_fn_equal_case_by_case")),
            ("statement", string(result.statement.readable_string())),
            (
                "fn_set_well_defined",
                project_verify_obj_wd(&result.fn_set_well_defined, runtime),
            ),
            (
                "coverage",
                object_for(
                    runtime,
                    vec![
                        (
                            "binder_introduction",
                            project_binder_introduction(
                                &result.coverage.binder_introduction,
                                runtime,
                            ),
                        ),
                        (
                            "coverage_check",
                            project_verify_fact(&result.coverage.coverage_check, runtime),
                        ),
                    ],
                ),
            ),
            (
                "disjoint",
                JsonValue::Array(
                    result
                        .disjoint
                        .iter()
                        .map(|pair| {
                            object_for(
                                runtime,
                                vec![
                                    ("left_case_index", JsonValue::Number(pair.i as f64)),
                                    ("right_case_index", JsonValue::Number(pair.j as f64)),
                                    (
                                        "binder_introduction",
                                        project_binder_introduction(
                                            &pair.binder_introduction,
                                            runtime,
                                        ),
                                    ),
                                    (
                                        "assumption_stored",
                                        project_store_and_infer(&pair.assumption_stored, runtime),
                                    ),
                                    (
                                        "negated_component",
                                        project_verify_fact(&pair.negated_component, runtime),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            (
                "case_return_checks",
                JsonValue::Array(
                    result
                        .case_return_checks
                        .iter()
                        .map(|case| {
                            object_for(
                                runtime,
                                vec![
                                    ("case_index", JsonValue::Number(case.case_index as f64)),
                                    (
                                        "binder_introduction",
                                        project_binder_introduction(
                                            &case.binder_introduction,
                                            runtime,
                                        ),
                                    ),
                                    (
                                        "assumption_stored",
                                        project_store_and_infer(&case.assumption_stored, runtime),
                                    ),
                                    (
                                        "body_well_defined",
                                        project_verify_obj_wd(&case.body_well_defined, runtime),
                                    ),
                                    (
                                        "body_in_ret_set",
                                        project_verify_fact(&case.body_in_ret_set, runtime),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            (
                "store_and_infer",
                project_have_store_ids(&result.store_and_infer_result.stored_fact_ids, runtime),
            ),
            (
                "membership_store",
                project_store_and_infer(&result.store_and_infer_result.membership, runtime),
            ),
            (
                "case_defining_stores",
                JsonValue::Array(
                    result
                        .store_and_infer_result
                        .case_defining
                        .iter()
                        .map(|store| project_store_and_infer(store, runtime))
                        .collect(),
                ),
            ),
        ],
    )
}

fn project_binder_introduction(
    result: &IntroduceFnSetClauseBindersResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "defined_params",
                project_have_store_and_infer(&result.defined_params, runtime),
            ),
            (
                "assumed_dom_facts",
                JsonValue::Array(
                    result
                        .assumed_dom_facts
                        .iter()
                        .map(|store| project_store_and_infer(store, runtime))
                        .collect(),
                ),
            ),
        ],
    )
}
