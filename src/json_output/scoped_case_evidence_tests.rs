use super::json_keys::localize_key;
use super::{project_stmt_detailed, project_stmt_normal};
use crate::execute::{ExecHaveFnEqualCaseByCaseStmtFailed, ExecHaveFnEqualCaseByCaseStmtResult};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;

const PRODUCT: &str = include_str!(
    "../../examples/proof_nodes/equal/by_builtin_strategy/finite_set_product_pointwise_scope.lit"
);
const CASES: &str = include_str!("../../examples/stmt_nodes/definition/have_fn_cases_evidence.lit");

#[test]
fn finite_product_scope_resolves_actual_pointwise_citations() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = rt.run_litex_code(PRODUCT).unwrap();
        assert!(run.success && run.session_error.is_none());
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &run.statement_results[0]
        else {
            panic!("fact")
        };
        let VerifyFactResult::ForallFact(forall) = &fact.verify_result else {
            panic!("forall")
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
            forall.as_ref()
        else {
            panic!("local forall")
        };
        let VerifyFactResult::Equality(equal) = &forall.proved_then_facts[0].verify_result else {
            panic!("equality")
        };
        let VerifyEqualityResult::Success(equal) = equal.as_ref() else {
            panic!("accepted equality")
        };
        let EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(proof),
        ) = &equal.searched_proof
        else {
            panic!("pointwise strategy")
        };
        assert!(!proof.set_equality.is_failed() && !proof.pointwise_equality.is_failed());
        assert!(!proof.introduced_parameter.stored_fact_ids.is_empty());
        for id in &proof.introduced_parameter.stored_fact_ids {
            assert!(proof.local_env.facts.facts_by_id.contains_key(id));
            assert!(!forall.local_env.facts.facts_by_id.contains_key(id));
            assert!(!rt.top_exec_env().facts.facts_by_id.contains_key(id));
        }
        let json = project_stmt_detailed(&run.statement_results[0], &rt);
        let strategy = find_strategy(&json, language).expect("projected strategy");
        for key in ["set_equality", "introduced_parameter", "pointwise_equality"] {
            assert!(field(&strategy, key, language).as_object().is_ok());
            assert_localized(key, language);
        }
        let mut cites = Vec::new();
        collect_cites(
            &field(&strategy, "pointwise_equality", language),
            language,
            &mut cites,
        );
        assert!(
            cites
                .iter()
                .any(|id| proof.introduced_parameter.stored_fact_ids.contains(id)),
            "actual binder fact must be used"
        );
        for id in cites {
            assert!(
                proof.local_env.facts.facts_by_id.contains_key(&id)
                    || forall.local_env.facts.facts_by_id.contains_key(&id)
                    || rt.top_exec_env().facts.facts_by_id.contains_key(&id),
                "unresolved {id}"
            );
        }
        assert_eq!(proof.local_env.definitions.identifiers.len(), 1);
        assert_eq!(forall.local_env.definitions.identifiers.len(), 1);
        assert!(rt.top_exec_env().definitions.identifiers.is_empty());
    }
    let mut rt = runtime(OutputLanguage::English);
    let run = rt
        .run_litex_code(&PRODUCT.replace("x + 0", "x + 1"))
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert!(rt.top_exec_env().facts.facts_by_id.is_empty());
    assert!(rt.top_exec_env().definitions.identifiers.is_empty());
}

#[test]
fn piecewise_checks_retain_scopes_and_project_all_stages() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = rt.run_litex_code(CASES).unwrap();
        assert!(run.success && run.session_error.is_none());
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
            ExecHaveFnEqualCaseByCaseStmtResult::Success(proof),
        )) = &run.statement_results[0]
        else {
            panic!("piecewise success")
        };
        assert_eq!(proof.disjoint.len(), 1);
        assert_eq!(proof.case_return_checks.len(), 2);
        assert_stores_local(
            &proof.coverage.binder_introduction.defined_params,
            &proof.coverage.local_env,
            &rt,
        );
        let pair = &proof.disjoint[0];
        assert_eq!((pair.i, pair.j), (0, 1));
        assert!(!pair.negated_component.is_failed());
        assert_stores_local(
            &pair.binder_introduction.defined_params,
            &pair.local_env,
            &rt,
        );
        assert!(pair
            .local_env
            .facts
            .facts_by_id
            .contains_key(&pair.assumption_stored.primary_fact_id()));
        for case in &proof.case_return_checks {
            assert!(!case.body_well_defined.is_failed() && !case.body_in_ret_set.is_failed());
            assert_stores_local(
                &case.binder_introduction.defined_params,
                &case.local_env,
                &rt,
            );
            assert!(case
                .local_env
                .facts
                .facts_by_id
                .contains_key(&case.assumption_stored.primary_fact_id()));
        }
        let json = project_stmt_detailed(&run.statement_results[0], &rt);
        for key in [
            "fn_set_well_defined",
            "coverage",
            "disjoint",
            "case_return_checks",
            "membership_store",
            "case_defining_stores",
        ] {
            field(&json, key, language);
            assert_localized(key, language);
        }
        let coverage = field(&json, "coverage", language);
        field(&coverage, "binder_introduction", language);
        field(&coverage, "coverage_check", language);
        let disjoint = field(&json, "disjoint", language);
        let pairs = disjoint.as_array().unwrap();
        assert_eq!(pairs.len(), 1);
        let mut cites = Vec::new();
        collect_cites(
            &field(&pairs[0], "negated_component", language),
            language,
            &mut cites,
        );
        assert!(!cites.is_empty(), "pair must cite its actual assumption");
        for id in cites {
            assert!(
                pair.local_env.facts.facts_by_id.contains_key(&id)
                    || rt.top_exec_env().facts.facts_by_id.contains_key(&id),
                "unresolved {id}"
            );
        }
        let checks = field(&json, "case_return_checks", language);
        for case in checks.as_array().unwrap() {
            for key in [
                "binder_introduction",
                "assumption_stored",
                "body_well_defined",
                "body_in_ret_set",
            ] {
                field(case, key, language);
                assert_localized(key, language);
            }
        }
        assert!(!json.stringify().contains("local_env"));
        let normal = project_stmt_normal(&run.statement_results[0], &rt);
        assert_eq!(
            field(&normal, "statement_result", language).as_str(),
            Ok("accepted")
        );
        assert_eq!(rt.top_exec_env().definitions.identifiers.len(), 1);
    }
}

#[test]
fn piecewise_failures_still_roll_back_and_allow_name_reuse() {
    for source in [
        "have fn choose(x R) R by cases:\n    case x <= 0: 0\n    case x >= 0: 1",
        "have fn choose(x R) R by cases:\n    case x < 0: 0",
        "have fn choose(x R) R by cases:\n    case x < 0: 1 / 0\n    case x >= 0: 1",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none());
        if source.contains("x <= 0") {
            assert!(matches!(
                &run.statement_results[0],
                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                    ExecHaveFnEqualCaseByCaseStmtResult::Failed(
                        ExecHaveFnEqualCaseByCaseStmtFailed::Disjoint { i: 0, j: 1 }
                    )
                ))
            ));
        }
        assert!(rt.top_exec_env().definitions.identifiers.is_empty());
        assert!(rt.top_exec_env().facts.facts_by_id.is_empty());
        assert!(rt.run_litex_code(CASES).unwrap().success);
    }
}

#[test]
fn algorithm_projection_includes_piecewise_definition_evidence() {
    let mut rt = runtime(OutputLanguage::English);
    let source = CASES.replace("have fn choose", "algo choose");
    let run = rt.run_litex_code(&source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = project_stmt_detailed(&run.statement_results[0], &rt);
    let inner = field(&json, "define_fn", OutputLanguage::English);
    assert_eq!(
        field(&inner, "disjoint", OutputLanguage::English)
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        field(&inner, "case_return_checks", OutputLanguage::English)
            .as_array()
            .unwrap()
            .len(),
        2
    );
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(rt);
    assert!(
        compiler.compile_run(&run, "cases_evidence").is_err(),
        "evidence retention does not add Lean support"
    );
}

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn assert_stores_local(stores: &StoreHaveObjAndInferResult, local: &ExecEnv, rt: &Runtime) {
    assert!(!stores.stored_fact_ids.is_empty());
    for id in &stores.stored_fact_ids {
        assert!(local.facts.facts_by_id.contains_key(id));
        assert!(!rt.top_exec_env().facts.facts_by_id.contains_key(id));
    }
}

fn field(value: &JsonValue, key: &str, language: OutputLanguage) -> JsonValue {
    value
        .as_object()
        .unwrap()
        .get(&localize_key(key, language))
        .unwrap_or_else(|| panic!("missing {key}: {}", value.stringify()))
        .clone()
}

fn assert_localized(key: &str, language: OutputLanguage) {
    if language != OutputLanguage::English {
        assert_ne!(localize_key(key, language), key);
    }
}

fn find_strategy(value: &JsonValue, language: OutputLanguage) -> Option<JsonValue> {
    match value {
        JsonValue::Object(map) => {
            if map
                .get(&localize_key("strategy", language))
                .and_then(|v| v.as_str().ok())
                == Some("FiniteSetProductPointwiseEquality")
            {
                return Some(value.clone());
            }
            for (_, child) in map.iter() {
                if let Some(found) = find_strategy(child, language) {
                    return Some(found);
                }
            }
        }
        JsonValue::Array(values) => {
            for child in values {
                if let Some(found) = find_strategy(child, language) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}

fn collect_cites(value: &JsonValue, language: OutputLanguage, cites: &mut Vec<FactId>) {
    match value {
        JsonValue::Object(map) => {
            if let Some(id) = map
                .get(&localize_key("cite_fact_id", language))
                .and_then(|v| v.as_str().ok())
            {
                cites.push(FactId::new(id.strip_prefix('f').unwrap().parse().unwrap()));
            }
            for (_, child) in map.iter() {
                collect_cites(child, language, cites);
            }
        }
        JsonValue::Array(values) => {
            for child in values {
                collect_cites(child, language, cites);
            }
        }
        _ => {}
    }
}
