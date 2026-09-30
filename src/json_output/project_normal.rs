//! Project ExecStmtResult → Normal JSON (see README).

use super::explain::{explain_compound_fact_why, explain_searched_proof_why};
use super::helper::{
    array_of_strings, bool_value, builtin_rule_with_optional_cite, cite_forall_from_fact_id,
    cite_from_fact_id, empty_string_array, infer_fact_texts_from_store_and_infer, object,
    output_language, store_fact_texts, string,
};
use super::project_stmt_catalog::project_non_fact_stmt;
use crate::ast::fact::{AtomicFact, Fact};
use crate::display_and_ir::readable_string_from_ir_text;
use crate::execute::{ExecFactStmtResult, ExecStmtResult};

use crate::execute::execute_fact_stmt::verify_and_fact::{
    VerifyAndFactFailed, VerifyAndFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
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
    VerifyForallFactFailed, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    VerifyForallFactWithIffFailed, VerifyForallFactWithIffResult,
};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::{
    VerifyNotForallFactFailed, VerifyNotForallFactResult,
};
use crate::execute::execute_fact_stmt::verify_or_fact::{VerifyOrFactFailed, VerifyOrFactResult};
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::knowledge_base::JsonValue;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;
use std::path::Path;

/// Output detail level. Today every emit path uses Normal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OutputDetail {
    Compact,
    Normal,
    Detailed,
}

impl OutputDetail {
    pub fn as_str(self) -> &'static str {
        match self {
            OutputDetail::Compact => "compact",
            OutputDetail::Normal => "normal",
            OutputDetail::Detailed => "detailed",
        }
    }
}

/// Project one statement result at Normal detail.
pub fn project_stmt_normal(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecStmtResult::Fact(fact) => project_fact_stmt(fact, runtime),
        other => project_non_fact_stmt(other, runtime),
    }
}

/// Build the Normal run envelope while Runtime still holds cited facts.
pub fn project_run_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let lang = output_language(runtime);
    let statement_results: Vec<JsonValue> = run
        .statement_results
        .iter()
        .map(|stmt| project_stmt_normal(stmt, runtime))
        .collect();
    let path_value = match path {
        Some(p) => string(p.display().to_string()),
        None => JsonValue::Null,
    };
    let session_error = match &run.session_error {
        None => JsonValue::Null,
        Some(err) => string(format!("{err:?}")),
    };
    object(lang, vec![
        ("kind", string("run")),
        ("success", bool_value(run.success)),
        ("target", string(target)),
        ("path", path_value),
        ("detail", string(OutputDetail::Normal.as_str())),
        (
            "language",
            string(runtime.launch_command.output_language().as_str()),
        ),
        ("statement_results", JsonValue::Array(statement_results)),
        ("session_error", session_error),
    ])
}

fn project_fact_stmt(fact: &ExecFactStmtResult, runtime: &Runtime) -> JsonValue {
    let lang = output_language(runtime);
    match fact {
        ExecFactStmtResult::Success(success) => {
            let statement = verify_goal_display(&success.verify_result);
            let why = why_verified(&success.verify_result, runtime);
            let stores = store_fact_texts(&success.store_and_infer_result.store);
            let infers = infer_fact_texts_from_store_and_infer(
                runtime,
                &success.store_and_infer_result,
            );
            object(lang, vec![
                ("success", bool_value(true)),
                ("statement", string(statement)),
                ("why_verified", why),
                ("stores", array_of_strings(stores)),
                ("infers", array_of_strings(infers)),
            ])
        }
        ExecFactStmtResult::Failed(verify) => {
            let statement = verify_goal_display(verify);
            let why = why_failed(verify, lang);
            object(lang, vec![
                ("success", bool_value(false)),
                ("statement", string(statement)),
                ("why_failed", why),
                ("stores", empty_string_array()),
                ("infers", empty_string_array()),
            ])
        }
    }
}

fn verify_goal_display(verify: &VerifyFactResult) -> String {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(s) => s.fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToSearchProof { fact, .. },
            ) => fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(_),
            ) => "<wd_failed>".into(),
        },
        VerifyFactResult::Equality(r) => match r.as_ref() {
            VerifyEqualityResult::Success(s) => {
                AtomicFact::EqualFact(s.fact.clone()).readable_string()
            }
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof { fact, .. }) => {
                AtomicFact::EqualFact(fact.clone()).readable_string()
            }
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_)) => {
                "<wd_failed>".into()
            }
        },
        VerifyFactResult::AndFact(r) => match r.as_ref() {
            VerifyAndFactResult::Success(s) => Fact::AndFact(s.fact.clone()).readable_string(),
            VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToSearchProof { fact, .. })
            | VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToVerifyWellDefined {
                fact,
                ..
            }) => Fact::AndFact(fact.clone()).readable_string(),
        },
        VerifyFactResult::ChainFact(r) => match r.as_ref() {
            VerifyChainFactResult::Success(s) => Fact::ChainFact(s.fact.clone()).readable_string(),
            VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToSearchProof { fact, .. })
            | VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToVerifyWellDefined {
                fact,
                ..
            }) => Fact::ChainFact(fact.clone()).readable_string(),
        },
        VerifyFactResult::OrFact(r) => match r.as_ref() {
            VerifyOrFactResult::Success(s) => Fact::OrFact(s.fact.clone()).readable_string(),
            VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToSearchProof { fact, .. }) => {
                Fact::OrFact(fact.clone()).readable_string()
            }
            VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToVerifyWellDefined(_)) => {
                "<wd_failed>".into()
            }
        },
        VerifyFactResult::ExistShapedFact(r) => exist_shaped_goal_display(r),
        VerifyFactResult::ForallFact(r) => match r.as_ref() {
            VerifyForallFactResult::Success(s) => {
                Fact::ForallFact(s.fact.clone()).readable_string()
            }
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                fact, ..
            }) => Fact::ForallFact(fact.clone()).readable_string(),
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(_)) => {
                "<wd_failed>".into()
            }
        },
        VerifyFactResult::ForallFactWithIff(r) => match r.as_ref() {
            VerifyForallFactWithIffResult::Success(s) => {
                Fact::ForallFactWithIff(s.fact.clone()).readable_string()
            }
            VerifyForallFactWithIffResult::Failed(
                VerifyForallFactWithIffFailed::FailThenImpliesIff { fact, .. },
            )
            | VerifyForallFactWithIffResult::Failed(
                VerifyForallFactWithIffFailed::FailIffImpliesThen { fact, .. },
            ) => Fact::ForallFactWithIff(fact.clone()).readable_string(),
        },
        VerifyFactResult::NotForall(r) => match r.as_ref() {
            VerifyNotForallFactResult::Success(s) => {
                Fact::NotForall(s.fact.clone()).readable_string()
            }
            VerifyNotForallFactResult::Failed(VerifyNotForallFactFailed::UnsupportedNegation {
                fact,
            })
            | VerifyNotForallFactResult::Failed(
                VerifyNotForallFactFailed::FailToProveDerivedExist { fact, .. },
            ) => Fact::NotForall(fact.clone()).readable_string(),
        },
    }
}

fn exist_shaped_goal_display(r: &VerifyExistShapedFactResult) -> String {
    let fact = match r {
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(s)) => {
            &s.fact
        }
        VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(s)) => {
            &s.fact
        }
        VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(s)) => &s.fact,
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(
            VerifyExistShapedFactFailed::FailToSearchProof { fact, .. },
        ))
        | VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(
            VerifyExistShapedFactFailed::FailToSearchProof { fact, .. },
        ))
        | VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Failed(
            VerifyExistShapedFactFailed::FailToSearchProof { fact, .. },
        )) => fact,
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
        ))
        | VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
        ))
        | VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Failed(
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
        )) => return "<wd_failed>".into(),
    };
    readable_string_from_ir_text(fact.ir().as_str())
}

fn why_verified(verify: &VerifyFactResult, runtime: &Runtime) -> JsonValue {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(s) => {
                why_from_atomic_except_searched(&s.searched_proof, runtime)
            }
            VerifyAtomicExceptEqualityFactResult::Failed(_) => {
                searched_proof_why_json(runtime, "failed")
            }
        },
        VerifyFactResult::Equality(r) => match r.as_ref() {
            VerifyEqualityResult::Success(s) => why_from_equal_searched(&s.searched_proof, runtime),
            VerifyEqualityResult::Failed(_) => searched_proof_why_json(runtime, "failed"),
        },
        VerifyFactResult::AndFact(_) => compound_why_json(runtime, "and"),
        VerifyFactResult::OrFact(_) => compound_why_json(runtime, "or"),
        VerifyFactResult::ChainFact(_) => compound_why_json(runtime, "chain"),
        VerifyFactResult::ExistShapedFact(_) => compound_why_json(runtime, "exist"),
        VerifyFactResult::ForallFact(_) | VerifyFactResult::ForallFactWithIff(_) => {
            compound_why_json(runtime, "forall")
        }
        VerifyFactResult::NotForall(_) => compound_why_json(runtime, "forall"),
    }
}

fn compound_why_json(runtime: &Runtime, kind: &str) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_compound_fact_why(kind, lang);
    object(lang, vec![
        ("type", string(text.type_tag)),
        ("rule_name", string(text.rule_name)),
        ("message", string(text.message)),
    ])
}

fn searched_proof_why_json(runtime: &Runtime, kind: &str) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_searched_proof_why(kind, lang);
    object(lang, vec![
        ("type", string(text.type_tag)),
        ("rule_name", string(text.rule_name)),
        ("message", string(text.message)),
    ])
}

fn why_failed(verify: &VerifyFactResult, lang: crate::launch_command::OutputLanguage) -> JsonValue {
    if verify.is_wd_failed() {
        return object(lang, vec![("phase", string("well_defined"))]);
    }
    let goal = verify_goal_display(verify);
    object(lang, vec![
        ("phase", string("search_proof")),
        ("goal", string(goal)),
    ])
}

fn why_from_atomic_except_searched(
    searched: &AtomicExceptEqualityFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    match searched {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
            cite_from_fact_id(runtime, p.cite_fact_id)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) => {
            cite_forall_from_fact_id(runtime, p.cite.fact_id)
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(r) => {
            why_from_atomic_builtin_rule(r, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(_) => {
            searched_proof_why_json(runtime, "builtin_strategy")
        }
        AtomicExceptEqualityFactSearchedProof::ByDefinition(_) => {
            searched_proof_why_json(runtime, "by_definition")
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(_) => {
            searched_proof_why_json(runtime, "known_strategy")
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(_) => {
            searched_proof_why_json(runtime, "builtin_rewrite")
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
            searched_proof_why_json(runtime, "known_rewrite")
        }
    }
}

fn why_from_equal_searched(searched: &EqualFactSearchedProof, runtime: &Runtime) -> JsonValue {
    match searched {
        EqualFactSearchedProof::ByBuiltinRule(r) => why_from_equal_builtin_rule(r, runtime),
        EqualFactSearchedProof::ByKnownForallFact(p) => {
            cite_forall_from_fact_id(runtime, p.cite.fact_id)
        }
        EqualFactSearchedProof::ByEquivalenceClass(_) => {
            searched_proof_why_json(runtime, "equivalence_class")
        }
        EqualFactSearchedProof::ByObjectDefinition(_) => {
            searched_proof_why_json(runtime, "object_definition")
        }
        EqualFactSearchedProof::ByBuiltinStrategy(_) => {
            searched_proof_why_json(runtime, "builtin_strategy")
        }
        EqualFactSearchedProof::ByMatchingOneArgByOne(_) => {
            searched_proof_why_json(runtime, "matching_one_arg_by_one")
        }
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => {
            searched_proof_why_json(runtime, "known_forall_via_symmetry")
        }
        EqualFactSearchedProof::ByBuiltinRewrite(_) => {
            searched_proof_why_json(runtime, "builtin_rewrite")
        }
    }
}

fn why_from_atomic_builtin_rule(
    rule: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    let lang = output_language(runtime);
    let text = rule.rule_id_and_message(lang);
    builtin_rule_with_optional_cite(runtime, &text, rule.cite_fact_id())
}

fn why_from_equal_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    let lang = output_language(runtime);
    let text = rule.rule_id_and_message(lang);
    builtin_rule_with_optional_cite(runtime, &text, rule.cite_fact_id())
}
