//! Project ExecStmtResult → Normal JSON (see README).

use super::explain::{explain_compound_fact_why, explain_searched_proof_why};
use super::helper::{
    array_of_strings, builtin_rule_with_optional_cite, cite_from_fact_id, cite_known_forall,
    empty_string_array, infer_fact_texts_from_store_and_infer, object, output_language,
    phase_value_search_proof, phase_value_well_defined, run_result_value,
    session_termination_value, statement_result_value, store_fact_texts, string,
    with_source_statement,
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
use crate::run::run_command_outcome::{RunFileResult, RunLitexCodeResult};
use crate::runtime::Runtime;
use std::path::Path;

// Preserve the existing public import path while execution owns the policy.
pub use crate::result_detail::OutputDetail;

/// Project one statement result at Normal detail.
pub fn project_stmt_normal(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecStmtResult::Fact(fact) => project_fact_stmt(fact, runtime),
        other => project_non_fact_stmt(other, runtime),
    }
}

pub(super) fn project_run_statements_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
) -> Vec<JsonValue> {
    let lang = output_language(runtime);
    let mut statements: Vec<JsonValue> = run
        .statement_results
        .iter()
        .enumerate()
        .map(|(index, stmt)| {
            with_source_statement(
                project_stmt_normal(stmt, runtime),
                run.statement_texts.get(index),
                lang,
            )
        })
        .collect();
    if let Some(input) = &run.input_error {
        statements.push(super::feedback::input_failure(input, lang));
    }
    statements
}

/// Build the Normal run envelope while Runtime still holds cited facts.
pub fn project_run_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    project_run_normal_with_turns(run, &[], runtime, target, path)
}

/// Batch plus later REPL turns as one Normal envelope (full Session snapshot).
pub fn project_run_normal_with_turns(
    run: &RunLitexCodeResult,
    turns: &[RunLitexCodeResult],
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let mut statements = project_run_statements_normal(run, runtime);
    for turn in turns {
        statements.extend(project_run_statements_normal(turn, runtime));
    }
    project_run_normal_envelope(run, statements, !turns.is_empty(), runtime, target, path)
}

/// Repository batch (all export files) plus later REPL turns as one Normal
/// envelope. Non-session `-r` keeps its compact empty-statement summary; this
/// projection is only used for the final Session snapshot.
pub fn project_run_normal_with_files_and_turns(
    run: &RunLitexCodeResult,
    files: &[RunFileResult],
    turns: &[RunLitexCodeResult],
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let mut statements = Vec::new();
    for file in files {
        statements.extend(project_run_statements_normal(&file.run, runtime));
    }
    for turn in turns {
        statements.extend(project_run_statements_normal(turn, runtime));
    }
    project_run_normal_envelope(run, statements, !turns.is_empty(), runtime, target, path)
}

fn project_run_normal_envelope(
    run: &RunLitexCodeResult,
    statements: Vec<JsonValue>,
    merged_repl_turns: bool,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    let lang = output_language(runtime);
    let (statement_results, errors) = super::feedback::summarize_statements(statements, lang);
    let path_value = match path {
        Some(p) => string(p.display().to_string()),
        None => JsonValue::Null,
    };
    let termination = match &run.session_error {
        None => JsonValue::Null,
        Some(err) => session_termination_value(err, lang),
    };
    // Only a Session snapshot with REPL turns derives its verdict from the
    // merged statements. Ordinary batches keep `run.success`, including the
    // empty-statement `-r` summary whose verdict comes from its files.
    let snapshot_success = if merged_repl_turns {
        run.session_error.is_none() && errors.is_empty()
    } else {
        run.success
    };
    object(
        lang,
        vec![
            ("kind", string("run")),
            ("run_result", run_result_value(snapshot_success)),
            ("target", string(target)),
            ("path", path_value),
            ("detail", string(OutputDetail::Normal.as_str())),
            (
                "language",
                string(runtime.launch_command.output_language().as_str()),
            ),
            ("statement_results", JsonValue::Array(statement_results)),
            ("errors", JsonValue::Array(errors)),
            (
                "session_terminated",
                JsonValue::Bool(run.session_error.is_some()),
            ),
            ("termination", termination),
        ],
    )
}

fn project_fact_stmt(fact: &ExecFactStmtResult, runtime: &Runtime) -> JsonValue {
    let lang = output_language(runtime);
    match fact {
        ExecFactStmtResult::Success(success) => {
            let statement = verify_goal_display(&success.verify_result);
            let why = build_proof_method(&success.verify_result, runtime);
            let stores = store_fact_texts(&success.store_and_infer_result.store);
            let infers =
                infer_fact_texts_from_store_and_infer(runtime, &success.store_and_infer_result);
            object(
                lang,
                vec![
                    ("statement_result", statement_result_value(true)),
                    ("statement", string(statement)),
                    ("proof_method", why),
                    ("stores", array_of_strings(stores)),
                    ("infers", array_of_strings(infers)),
                ],
            )
        }
        ExecFactStmtResult::Failed(verify) => {
            let statement = verify_goal_display(verify);
            let why = why_failed(verify, runtime);
            object(
                lang,
                vec![
                    ("statement_result", statement_result_value(false)),
                    ("statement", string(statement)),
                    ("why_failed", why),
                    ("stores", empty_string_array()),
                    ("infers", empty_string_array()),
                ],
            )
        }
    }
}

pub(super) fn verify_goal_display(verify: &VerifyFactResult) -> String {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(s) => s.fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToSearchProof { fact, .. },
            ) => fact.readable_string(),
            VerifyAtomicExceptEqualityFactResult::Failed(
                VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(failed),
            ) => failed.fact().readable_string(),
        },
        VerifyFactResult::Equality(r) => match r.as_ref() {
            VerifyEqualityResult::Success(s) => {
                AtomicFact::EqualFact(s.fact.clone()).readable_string()
            }
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
                fact, ..
            }) => AtomicFact::EqualFact(fact.clone()).readable_string(),
            VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(failed)) => {
                AtomicFact::EqualFact(failed.fact.clone()).readable_string()
            }
        },
        VerifyFactResult::AndFact(r) => match r.as_ref() {
            VerifyAndFactResult::Success(s) => Fact::AndFact(s.fact.clone()).readable_string(),
            VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToSearchProof {
                fact, ..
            })
            | VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToVerifyWellDefined {
                fact,
                ..
            }) => Fact::AndFact(fact.clone()).readable_string(),
        },
        VerifyFactResult::ChainFact(r) => match r.as_ref() {
            VerifyChainFactResult::Success(s) => Fact::ChainFact(s.fact.clone()).readable_string(),
            VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToSearchProof {
                fact,
                ..
            })
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
            VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToVerifyWellDefined(failed)) => {
                Fact::OrFact(failed.fact.clone()).readable_string()
            }
        },
        VerifyFactResult::ExistShapedFact(r) => exist_shaped_goal_display(r),
        VerifyFactResult::ForallFact(r) => match r.as_ref() {
            VerifyForallFactResult::Success(s) => {
                Fact::ForallFact(s.fact().clone()).readable_string()
            }
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                fact,
                ..
            }) => Fact::ForallFact(fact.clone()).readable_string(),
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
                failed,
            )) => Fact::ForallFact(failed.fact().clone()).readable_string(),
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
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(failed),
        ))
        | VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(failed),
        ))
        | VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Failed(
            VerifyExistShapedFactFailed::FailToVerifyWellDefined(failed),
        )) => failed.fact(),
    };
    readable_string_from_ir_text(fact.ir().as_str())
}

fn build_proof_method(verify: &VerifyFactResult, runtime: &Runtime) -> JsonValue {
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
        VerifyFactResult::AndFact(result) => match result.as_ref() {
            VerifyAndFactResult::Success(proof) if proof.known_forall.is_some() => cite_known_forall(runtime, proof.known_forall.as_ref().unwrap()),
            _ => compound_why_json(runtime, "and"),
        },
        VerifyFactResult::OrFact(result) => match result.as_ref() {
            VerifyOrFactResult::Success(proof) => match &proof.searched_proof {
                crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchedProof::ByKnownForallFact(application) => cite_known_forall(runtime, application),
                _ => compound_why_json(runtime, "or"),
            },
            _ => compound_why_json(runtime, "or"),
        },
        VerifyFactResult::ChainFact(result) => match result.as_ref() {
            VerifyChainFactResult::Success(proof) if proof.known_forall.is_some() => cite_known_forall(runtime, proof.known_forall.as_ref().unwrap()),
            _ => compound_why_json(runtime, "chain"),
        },
        VerifyFactResult::ExistShapedFact(result) => {
            let searched = match result.as_ref() {
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(proof)) => Some(&proof.searched_proof),
                VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(proof)) => Some(&proof.searched_proof),
                VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(proof)) => Some(&proof.searched_proof),
                _ => None,
            };
            match searched {
                Some(crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof::ByKnownForallFact(application)) => cite_known_forall(runtime, application),
                _ => compound_why_json(runtime, "exist"),
            }
        },
        VerifyFactResult::ForallFact(_) | VerifyFactResult::ForallFactWithIff(_) => {
            compound_why_json(runtime, "forall")
        }
        VerifyFactResult::NotForall(_) => compound_why_json(runtime, "forall"),
    }
}

fn compound_why_json(runtime: &Runtime, kind: &str) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_compound_fact_why(kind, lang);
    object(
        lang,
        vec![
            ("type", string(text.type_tag)),
            ("rule_name", string(text.rule_name)),
            ("message", string(text.message)),
        ],
    )
}

fn searched_proof_why_json(runtime: &Runtime, kind: &str) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_searched_proof_why(kind, lang);
    object(
        lang,
        vec![
            ("type", string(text.type_tag)),
            ("rule_name", string(text.rule_name)),
            ("message", string(text.message)),
        ],
    )
}

fn why_failed(verify: &VerifyFactResult, runtime: &Runtime) -> JsonValue {
    let lang = output_language(runtime);
    let verification = super::project_detailed::project_verify_fact(verify, runtime);
    let mut entries = vec![
        (
            "phase",
            string(if verify.is_wd_failed() {
                phase_value_well_defined(lang)
            } else {
                phase_value_search_proof(lang)
            }),
        ),
        ("goal", string(verify_goal_display(verify))),
    ];
    // Put the concise cause before its full evidence, preserving the actual
    // failed child even when the outer execution stage was proof search.
    if let Some(diagnostic) = verification
        .as_object()
        .unwrap()
        .get(&super::json_keys::localize_key("diagnostic", lang))
    {
        if let Some(message) = diagnostic
            .as_object()
            .unwrap()
            .get(&super::json_keys::localize_key("message", lang))
        {
            entries.push(("message", message.clone()));
        }
        entries.push(("diagnostic", diagnostic.clone()));
    }
    entries.push(("verification", verification));
    object(lang, entries)
}

fn why_from_atomic_except_searched(
    searched: &AtomicExceptEqualityFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    match searched {
        AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(_) => {
            searched_proof_why_json(runtime, "by_definition")
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownZeroRemainder(_) => {
            searched_proof_why_json(runtime, "by_definition")
        }

        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(_) => {
            searched_proof_why_json(runtime, "structural_membership")
        }
        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(_) => {
            searched_proof_why_json(runtime, "closed_calculation")
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
            cite_from_fact_id(runtime, p.cite_fact_id)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(p) => {
            let lang = output_language(runtime);
            let text = explain_searched_proof_why("known_special_property", lang);
            let mut fields = vec![
                ("type", string(text.type_tag)),
                ("rule_name", string(text.rule_name)),
                ("message", string(text.message)),
            ];
            if let Some(fact) = p
                .cite_property_fact_id()
                .and_then(|id| runtime.fact_by_id_in_stack(id))
            {
                fields.push(("cite", string(fact.readable_string())));
            }
            object(lang, fields)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) => {
            cite_known_forall(runtime, p)
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
        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(proof) => {
            super::helper::cite_known_strategy(runtime, proof)
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
        EqualFactSearchedProof::ByClosedCalculation(_) => {
            searched_proof_why_json(runtime, "closed_calculation")
        }
        EqualFactSearchedProof::ByTheyAreTheSame(_) => {
            searched_proof_why_json(runtime, "they_are_the_same")
        }
        EqualFactSearchedProof::ByKnownSpecialProperty(_) => {
            searched_proof_why_json(runtime, "known_special_property")
        }
        EqualFactSearchedProof::ByBuiltinRule(r) => why_from_equal_builtin_rule(r, runtime),
        EqualFactSearchedProof::ByKnownForallFact(p) => cite_known_forall(runtime, p),
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
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof) => {
            let mut why = searched_proof_why_json(runtime, "known_forall_via_symmetry");
            let citation = cite_known_forall(runtime, &proof.known_forall);
            if let (JsonValue::Object(why), JsonValue::Object(citation)) = (&mut why, citation) {
                let type_key = super::json_keys::localize_key("type", output_language(runtime));
                for (key, value) in citation.iter().filter(|(key, _)| *key != &type_key) {
                    why.insert(key.clone(), value.clone());
                }
            }
            why
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
    let text = rule.rule_name_and_message(lang);
    builtin_rule_with_optional_cite(runtime, &text, rule.cite_fact_id())
}

fn why_from_equal_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    let lang = output_language(runtime);
    let text = rule.rule_name_and_message(lang);
    builtin_rule_with_optional_cite(runtime, &text, rule.cite_fact_id())
}
