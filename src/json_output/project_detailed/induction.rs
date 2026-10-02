//! Induction result projection preserves stages, recursive cases, and proof bodies.

use super::store::{project_have_store_ids, project_store_and_infer};
use super::verify::project_verify_fact;
use super::wd::{project_verify_fact_wd_result, project_verify_obj_wd};
use crate::execute::execute_by_stmt::{
    ByInducBodySuccess, ByInducCaseFailed, ByInducCaseSuccess, ExecByInducStmtFailed,
    ExecByInducStmtResult, ExecByStrongInducStmtFailed, ExecByStrongInducStmtResult,
};
use crate::execute::{
    ExecDefAlgoByInducStmtFailed, ExecDefAlgoByInducStmtResult, ExecHaveFnByInducStmtFailed,
    ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult, InducCaseBodySuccess,
    InducCaseListSuccess,
};
use crate::json_output::helper::{bool_value, object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_by_induc(
    kind: &str,
    result: &ExecByInducStmtResult,
    rt: &Runtime,
) -> JsonValue {
    match result {
        ExecByInducStmtResult::Success(s) => object_for(
            rt,
            vec![
                ("success", bool_value(true)),
                ("kind", string(kind)),
                ("from_in_z", project_verify_fact(&s.from_in_z, rt)),
                (
                    "goal_domain_stored",
                    project_store_and_infer(&s.goal_domain_stored, rt),
                ),
                (
                    "goals_wd",
                    JsonValue::Array(
                        s.goals_wd
                            .iter()
                            .map(|w| project_verify_fact_wd_result(w, rt))
                            .collect(),
                    ),
                ),
                ("body", project_induc_body(&s.body, rt)),
                ("stored", project_store_and_infer(&s.stored, rt)),
            ],
        ),
        ExecByInducStmtResult::Failed(f) => object_for(
            rt,
            vec![
                ("success", bool_value(false)),
                ("kind", string(kind)),
                ("failure", project_induc_failure(f, rt)),
            ],
        ),
    }
}

pub(super) fn project_by_strong_induc(
    result: &ExecByStrongInducStmtResult,
    rt: &Runtime,
) -> JsonValue {
    match result {
        ExecByStrongInducStmtResult::Success(s) => object_for(
            rt,
            vec![
                ("success", bool_value(true)),
                ("kind", string("by_strong_induc")),
                ("from_in_z", project_verify_fact(&s.from_in_z, rt)),
                (
                    "goal_domain_stored",
                    project_store_and_infer(&s.goal_domain_stored, rt),
                ),
                (
                    "goals_wd",
                    JsonValue::Array(
                        s.goals_wd
                            .iter()
                            .map(|w| project_verify_fact_wd_result(w, rt))
                            .collect(),
                    ),
                ),
                ("body", project_induc_body(&s.body, rt)),
                ("stored", project_store_and_infer(&s.stored, rt)),
            ],
        ),
        ExecByStrongInducStmtResult::Failed(f) => object_for(
            rt,
            vec![
                ("success", bool_value(false)),
                ("kind", string("by_strong_induc")),
                ("failure", project_strong_induc_failure(f, rt)),
            ],
        ),
    }
}

pub(in crate::json_output) fn project_induc_failure(
    f: &ExecByInducStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match f {
        ExecByInducStmtFailed::FromNotInteger(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("from_in_z", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecByInducStmtFailed::GoalDomain(msg) => phase_message("goal_domain", msg, rt),
        ExecByInducStmtFailed::GoalWd { index, result } => object_for(
            rt,
            vec![
                ("phase", induction_phase("goal_wd", rt)),
                ("goal_index", JsonValue::Number(*index as f64)),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        ),
        ExecByInducStmtFailed::BodyShape(msg) => phase_message("body_shape", msg, rt),
        ExecByInducStmtFailed::BaseCase(f) => project_case_failure("base", f, rt),
        ExecByInducStmtFailed::StepCase(f) => project_case_failure("step", f, rt),
        ExecByInducStmtFailed::Store(msg) => phase_message("store", msg, rt),
        ExecByInducStmtFailed::NotFullyWired(msg) => phase_message("not_fully_wired", msg, rt),
    }
}

pub(in crate::json_output) fn project_strong_induc_failure(
    f: &ExecByStrongInducStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match f {
        ExecByStrongInducStmtFailed::FromNotInteger(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("from_in_z", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecByStrongInducStmtFailed::GoalDomain(msg) => phase_message("goal_domain", msg, rt),
        ExecByStrongInducStmtFailed::GoalWd { index, result } => object_for(
            rt,
            vec![
                ("phase", induction_phase("goal_wd", rt)),
                ("goal_index", JsonValue::Number(*index as f64)),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        ),
        ExecByStrongInducStmtFailed::BodyShape(msg) => phase_message("body_shape", msg, rt),
        ExecByStrongInducStmtFailed::BaseCase(f) => project_case_failure("base", f, rt),
        ExecByStrongInducStmtFailed::StepCase(f) => project_case_failure("step", f, rt),
        ExecByStrongInducStmtFailed::Store(msg) => phase_message("store", msg, rt),
        ExecByStrongInducStmtFailed::NotFullyWired(msg) => {
            phase_message("not_fully_wired", msg, rt)
        }
    }
}

fn project_induc_body(body: &ByInducBodySuccess, rt: &Runtime) -> JsonValue {
    let (form, base, step) = match body {
        ByInducBodySuccess::Unstructured { base, step } => ("unstructured", base, step),
        ByInducBodySuccess::Structured { base, step } => ("structured", base, step),
    };
    object_for(
        rt,
        vec![
            ("form", string(form)),
            ("base", project_induc_case(base, rt)),
            ("step", project_induc_case(step, rt)),
        ],
    )
}

fn project_induc_case(case: &ByInducCaseSuccess, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            (
                "assumptions_stored",
                JsonValue::Array(
                    case.assumptions_stored
                        .iter()
                        .map(|s| project_store_and_infer(s, rt))
                        .collect(),
                ),
            ),
            (
                "proof_steps",
                JsonValue::Array(
                    case.proof_steps
                        .iter()
                        .map(|s| super::stmt::project_stmt_detailed(s, rt))
                        .collect(),
                ),
            ),
            (
                "goals_verified",
                JsonValue::Array(
                    case.goals_verified
                        .iter()
                        .map(|p| project_verify_fact(p, rt))
                        .collect(),
                ),
            ),
        ],
    )
}

fn project_case_failure(phase: &str, f: &ByInducCaseFailed, rt: &Runtime) -> JsonValue {
    let failure = match f {
        ByInducCaseFailed::Assume(msg) => phase_message("assume", msg, rt),
        ByInducCaseFailed::ProofBody(body) => object_for(
            rt,
            vec![
                ("phase", induction_phase("proof_body", rt)),
                ("step_index", JsonValue::Number(body.step_index as f64)),
                (
                    "result",
                    super::stmt::project_stmt_detailed(&body.result, rt),
                ),
            ],
        ),
        ByInducCaseFailed::Goal { index, result } => object_for(
            rt,
            vec![
                ("phase", induction_phase("goal", rt)),
                ("goal_index", JsonValue::Number(*index as f64)),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![("phase", induction_phase(phase, rt)), ("failure", failure)],
    )
}

pub(super) fn project_induc_definition(
    result: &ExecHaveFnByInducStmtResult,
    rt: &Runtime,
) -> JsonValue {
    match result {
        ExecHaveFnByInducStmtResult::Success(s) => project_induc_definition_success(s, rt),
        ExecHaveFnByInducStmtResult::Failed(f) => object_for(
            rt,
            vec![
                ("success", bool_value(false)),
                ("kind", string("have_fn_by_induc")),
                ("failure", project_induc_definition_failure(f, rt)),
            ],
        ),
    }
}

fn project_induc_definition_success(
    s: &ExecHaveFnByInducStmtSuccessResult,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("success", bool_value(true)),
            ("kind", string("have_fn_by_induc")),
            ("statement", string(s.statement.readable_string())),
            (
                "fn_set_well_defined",
                project_verify_obj_wd(&s.fn_set_well_defined, rt),
            ),
            ("measure_in_z", project_verify_fact(&s.measure_in_z, rt)),
            ("lower_in_z", project_verify_fact(&s.lower_in_z, rt)),
            (
                "measure_ge_lower",
                project_verify_fact(&s.measure_ge_lower, rt),
            ),
            ("case_checks", project_case_list(&s.case_checks, rt)),
            (
                "stored",
                project_have_store_ids(&s.store_and_infer_result.stored_fact_ids, rt),
            ),
        ],
    )
}

pub(super) fn project_induc_algo(result: &ExecDefAlgoByInducStmtResult, rt: &Runtime) -> JsonValue {
    match result {
        ExecDefAlgoByInducStmtResult::Success(s) => object_for(
            rt,
            vec![
                ("success", bool_value(true)),
                ("kind", string("def_algo_by_induc")),
                ("statement", string(s.statement.readable_string())),
                (
                    "define_fn",
                    project_induc_definition_success(&s.define_fn, rt),
                ),
            ],
        ),
        ExecDefAlgoByInducStmtResult::Failed(f) => object_for(
            rt,
            vec![
                ("success", bool_value(false)),
                ("kind", string("def_algo_by_induc")),
                (
                    "failure",
                    match f {
                        ExecDefAlgoByInducStmtFailed::DefineFn(f) => {
                            project_induc_definition_failure(f, rt)
                        }
                        ExecDefAlgoByInducStmtFailed::AlgoAlreadyDefined => phase_message(
                            "algo_already_defined",
                            "algorithm is already defined",
                            rt,
                        ),
                    },
                ),
            ],
        ),
    }
}

fn project_case_list(list: &InducCaseListSuccess, rt: &Runtime) -> JsonValue {
    let cases = list
        .cases
        .iter()
        .map(|case| {
            let body = match &case.body {
                InducCaseBodySuccess::EqualTo {
                    well_defined,
                    in_ret_set,
                } => object_for(
                    rt,
                    vec![
                        ("kind", string("equal_to")),
                        ("well_defined", project_verify_obj_wd(well_defined, rt)),
                        ("in_ret_set", project_verify_fact(in_ret_set, rt)),
                    ],
                ),
                InducCaseBodySuccess::NestedCases(nested) => project_case_list(nested, rt),
            };
            object_for(
                rt,
                vec![
                    (
                        "assumption_stored",
                        project_store_and_infer(&case.assumption_stored, rt),
                    ),
                    ("body", body),
                ],
            )
        })
        .collect();
    let disjoint = list
        .disjoint
        .iter()
        .map(|pair| {
            object_for(
                rt,
                vec![
                    ("left_case_index", JsonValue::Number(pair.i as f64)),
                    ("right_case_index", JsonValue::Number(pair.j as f64)),
                    (
                        "assumption_stored",
                        project_store_and_infer(&pair.assumption_stored, rt),
                    ),
                    (
                        "negated_component",
                        project_verify_fact(&pair.negated_component, rt),
                    ),
                ],
            )
        })
        .collect();
    object_for(
        rt,
        vec![
            ("coverage", project_verify_fact(&list.coverage, rt)),
            ("disjoint", JsonValue::Array(disjoint)),
            ("cases", JsonValue::Array(cases)),
        ],
    )
}

pub(in crate::json_output) fn project_induc_definition_failure(
    f: &ExecHaveFnByInducStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match f {
        ExecHaveFnByInducStmtFailed::EmptyCases => {
            phase_message("empty_cases", "at least one case is required", rt)
        }
        ExecHaveFnByInducStmtFailed::Shape(msg) => phase_message("shape", msg, rt),
        ExecHaveFnByInducStmtFailed::FnSetWellDefined(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("fn_set_wd", rt)),
                ("result", project_verify_obj_wd(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::MeasureWellDefined(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("measure_wd", rt)),
                ("result", project_verify_obj_wd(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::LowerBoundWellDefined(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("lower_bound_wd", rt)),
                ("result", project_verify_obj_wd(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::MeasureNotInteger(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("measure_in_z", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::LowerBoundNotInteger(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("lower_in_z", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::MeasureBelowLower(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("measure_ge_lower", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::Coverage(r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("coverage", rt)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::Disjoint { i, j } => object_for(
            rt,
            vec![
                ("phase", induction_phase("disjoint", rt)),
                ("left_case_index", JsonValue::Number(*i as f64)),
                ("right_case_index", JsonValue::Number(*j as f64)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::CaseBodyWellDefined(i, r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("case_body_wd", rt)),
                ("case_index", JsonValue::Number(*i as f64)),
                ("result", project_verify_obj_wd(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::CaseBodyInRetSet(i, r) => object_for(
            rt,
            vec![
                ("phase", induction_phase("case_body_in_ret_set", rt)),
                ("case_index", JsonValue::Number(*i as f64)),
                ("result", project_verify_fact(r, rt)),
            ],
        ),
        ExecHaveFnByInducStmtFailed::NestedCase { index, failed } => object_for(
            rt,
            vec![
                ("phase", induction_phase("nested_case", rt)),
                ("case_index", JsonValue::Number(*index as f64)),
                ("failure", project_induc_definition_failure(failed, rt)),
            ],
        ),
    }
}

fn phase_message(phase: &str, msg: &str, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("phase", induction_phase(phase, rt)),
            ("message", string(msg)),
        ],
    )
}

fn induction_phase(phase: &str, rt: &Runtime) -> JsonValue {
    if rt.launch_command.output_language() == crate::launch_command::OutputLanguage::English {
        return string(phase);
    }
    string(match phase {
        "from_in_z" => "起点整数检查",
        "goal_domain" => "归纳域假设",
        "goal_wd" => "目标良定性",
        "body_shape" => "证明体结构",
        "algo_already_defined" => "算法已定义",
        "base" => "基例",
        "step" => "归纳步",
        "store" => "存储",
        "not_fully_wired" => "尚未实现",
        "assume" => "引入假设",
        "proof_body" => "证明体",
        "goal" => "目标证明",
        "empty_cases" => "空分支列表",
        "shape" => "定义结构",
        "fn_set_wd" => "函数类型良定性",
        "measure_wd" => "度量良定性",
        "lower_bound_wd" => "下界良定性",
        "measure_in_z" => "度量整数检查",
        "lower_in_z" => "下界整数检查",
        "measure_ge_lower" => "度量下界检查",
        "coverage" => "分支覆盖",
        "disjoint" => "分支互斥",
        "case_body_wd" => "分支返回值良定性",
        "case_body_in_ret_set" => "分支返回类型",
        "nested_case" => "嵌套分支",
        other => other,
    })
}
