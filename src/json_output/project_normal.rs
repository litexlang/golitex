//! Project ExecStmtResult → Normal JSON (see README).

use super::helper::{
    array_of_strings, bool_value, builtin_rule_with_optional_cite, cite_forall_from_fact_id,
    cite_from_fact_id, empty_string_array, infer_fact_texts_from_store_and_infer, object,
    split_have_fact_id_texts, store_fact_texts, string,
};
use crate::ast::fact::AtomicFact;
use crate::execute::{
    ExecDefineObjStmtResult, ExecDefinitionStmtResult, ExecFactStmtResult,
    ExecHaveObjEqualStmtResult, ExecHaveObjInNonemptySetStmtResult, ExecStmtResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    greater_equal::GreaterEqualFactSearchProofByBuiltinRule,
    less::LessFactSearchProofByBuiltinRule,
    less_equal::LessEqualFactSearchProofByBuiltinRule,
    not_equal::NotEqualFactSearchProofByBuiltinRule,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
    VerifyAtomicExceptEqualityFactFailed, VerifyAtomicExceptEqualityFactResult,
    VerifyEqualityFailed, VerifyEqualityResult,
};
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
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(have),
        )) => project_have_in_nonempty(have, runtime),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(have),
        )) => project_have_equal(have, runtime),
        other => project_unsupported_stmt(other),
    }
}

/// Build the Normal run envelope while Runtime still holds cited facts.
pub fn project_run_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
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
    object(vec![
        ("kind", string("run")),
        ("ok", bool_value(run.success)),
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
    match fact {
        ExecFactStmtResult::Success(success) => {
            let statement = verify_goal_display(&success.verify_result);
            let why = why_verified(&success.verify_result, runtime);
            let stores = store_fact_texts(&success.store_and_infer_result.store);
            let infers = infer_fact_texts_from_store_and_infer(
                runtime,
                &success.store_and_infer_result,
            );
            object(vec![
                ("success", bool_value(true)),
                ("statement", string(statement)),
                ("why_verified", why),
                ("stores", array_of_strings(stores)),
                ("infers", array_of_strings(infers)),
            ])
        }
        ExecFactStmtResult::Failed(verify) => {
            let statement = verify_goal_display(verify);
            let why = why_failed(verify);
            object(vec![
                ("success", bool_value(false)),
                ("statement", string(statement)),
                ("why_failed", why),
                ("stores", empty_string_array()),
                ("infers", empty_string_array()),
            ])
        }
    }
}

fn project_have_in_nonempty(
    have: &ExecHaveObjInNonemptySetStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    match have {
        ExecHaveObjInNonemptySetStmtResult::Success(success) => {
            let statement = success.statement.readable_string();
            let (stores, infers) = split_have_fact_id_texts(
                runtime,
                &success.store_and_infer_result.stored_fact_ids,
            );
            object(vec![
                ("success", bool_value(true)),
                ("statement", string(statement)),
                ("why_verified", object(vec![("type", string("define_obj"))])),
                ("stores", array_of_strings(stores)),
                ("infers", array_of_strings(infers)),
            ])
        }
        ExecHaveObjInNonemptySetStmtResult::Failed(_) => object(vec![
            ("success", bool_value(false)),
            ("statement", string("have …")),
            ("why_failed", object(vec![("phase", string("have_obj"))])),
            ("stores", empty_string_array()),
            ("infers", empty_string_array()),
        ]),
    }
}

fn project_have_equal(have: &ExecHaveObjEqualStmtResult, runtime: &Runtime) -> JsonValue {
    match have {
        ExecHaveObjEqualStmtResult::Success(success) => {
            let statement = success.statement.readable_string();
            let (stores, infers) = split_have_fact_id_texts(
                runtime,
                &success.store_and_infer_result.stored_fact_ids,
            );
            object(vec![
                ("success", bool_value(true)),
                ("statement", string(statement)),
                ("why_verified", object(vec![("type", string("define_obj"))])),
                ("stores", array_of_strings(stores)),
                ("infers", array_of_strings(infers)),
            ])
        }
        ExecHaveObjEqualStmtResult::Failed(_) => object(vec![
            ("success", bool_value(false)),
            ("statement", string("have … = …")),
            (
                "why_failed",
                object(vec![("phase", string("have_obj_equal"))]),
            ),
            ("stores", empty_string_array()),
            ("infers", empty_string_array()),
        ]),
    }
}

fn project_unsupported_stmt(result: &ExecStmtResult) -> JsonValue {
    let success = !result.is_failed();
    object(vec![
        ("success", bool_value(success)),
        ("statement", string(stmt_kind_label(result))),
        (
            if success {
                "why_verified"
            } else {
                "why_failed"
            },
            object(vec![("type", string("stmt"))]),
        ),
        ("stores", empty_string_array()),
        ("infers", empty_string_array()),
    ])
}

fn stmt_kind_label(result: &ExecStmtResult) -> String {
    match result {
        ExecStmtResult::Fact(_) => "fact".into(),
        ExecStmtResult::Definition(_) => "definition".into(),
        ExecStmtResult::Witness(_) => "witness".into(),
        ExecStmtResult::Trust(_) => "trust".into(),
        ExecStmtResult::By(_) => "by".into(),
        ExecStmtResult::Register(_) => "register".into(),
        ExecStmtResult::ReleaseAndExpand(_) => "release_and_expand".into(),
        ExecStmtResult::ProofBlock(_) => "proof_block".into(),
        ExecStmtResult::Command(_) => "command".into(),
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
        VerifyFactResult::AndFact(_) => "and …".into(),
        VerifyFactResult::ChainFact(_) => "chain …".into(),
        VerifyFactResult::OrFact(_) => "or …".into(),
        VerifyFactResult::ExistShapedFact(_) => "exist …".into(),
        VerifyFactResult::ForallFact(_) => "forall …".into(),
        VerifyFactResult::ForallFactWithIff(_) => "forall … <=> …".into(),
        VerifyFactResult::NotForall(_) => "not forall …".into(),
    }
}

fn why_verified(verify: &VerifyFactResult, runtime: &Runtime) -> JsonValue {
    match verify {
        VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(s) => {
                why_from_atomic_except_searched(&s.searched_proof, runtime)
            }
            VerifyAtomicExceptEqualityFactResult::Failed(_) => {
                object(vec![("type", string("failed"))])
            }
        },
        VerifyFactResult::Equality(r) => match r.as_ref() {
            VerifyEqualityResult::Success(s) => why_from_equal_searched(&s.searched_proof, runtime),
            VerifyEqualityResult::Failed(_) => object(vec![("type", string("failed"))]),
        },
        _ => object(vec![("type", string("compound_fact"))]),
    }
}

fn why_failed(verify: &VerifyFactResult) -> JsonValue {
    if verify.is_wd_failed() {
        return object(vec![("phase", string("well_defined"))]);
    }
    let goal = verify_goal_display(verify);
    object(vec![
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
            object(vec![("type", string("builtin_strategy"))])
        }
        AtomicExceptEqualityFactSearchedProof::ByDefinition(_) => {
            object(vec![("type", string("by_definition"))])
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(_) => {
            object(vec![("type", string("known_strategy"))])
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(_) => {
            object(vec![("type", string("builtin_rewrite"))])
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
            object(vec![("type", string("known_rewrite"))])
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
            object(vec![("type", string("equivalence_class"))])
        }
        EqualFactSearchedProof::ByObjectDefinition(_) => {
            object(vec![("type", string("object_definition"))])
        }
        EqualFactSearchedProof::ByBuiltinStrategy(_) => {
            object(vec![("type", string("builtin_strategy"))])
        }
        EqualFactSearchedProof::ByMatchingOneArgByOne(_) => {
            object(vec![("type", string("matching_one_arg_by_one"))])
        }
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => {
            object(vec![("type", string("known_forall_via_symmetry"))])
        }
        EqualFactSearchedProof::ByBuiltinRewrite(_) => {
            object(vec![("type", string("builtin_rewrite"))])
        }
    }
}

fn why_from_atomic_builtin_rule(
    rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(g) => match g {
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInNatural(p) => {
                builtin_rule_with_optional_cite(runtime, "FromKnownInNatural", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "FromKnownInPositiveNatural",
                    Some(p.cite_fact_id),
                )
            }
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(p) => {
                builtin_rule_with_optional_cite(runtime, "FromKnownGreater", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "OrderFlipMulMinusOne",
                    Some(p.cite_fact_id),
                )
            }
            GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(_) => {
                builtin_rule_with_optional_cite(runtime, "OrderReflexivity", None)
            }
            GreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(_) => {
                builtin_rule_with_optional_cite(runtime, "ClosedNumericComparison", None)
            }
            _ => builtin_rule_with_optional_cite(runtime, "GreaterEqualBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(l) => match l {
            LessEqualFactSearchProofByBuiltinRule::FromKnownInNatural(p) => {
                builtin_rule_with_optional_cite(runtime, "FromKnownInNatural", Some(p.cite_fact_id))
            }
            LessEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "OrderFlipMulMinusOne",
                    Some(p.cite_fact_id),
                )
            }
            LessEqualFactSearchProofByBuiltinRule::OrderSignFromNegativeLiteralBound(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "OrderSignFromNegativeLiteralBound",
                    Some(p.cite_fact_id),
                )
            }
            _ => builtin_rule_with_optional_cite(runtime, "LessEqualBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(l) => match l {
            LessFactSearchProofByBuiltinRule::FromKnownInPositiveStandardSet(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "FromKnownInPositiveStandardSet",
                    Some(p.cite_fact_id),
                )
            }
            LessFactSearchProofByBuiltinRule::FromKnownInNegativeStandardSet(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "FromKnownInNegativeStandardSet",
                    Some(p.cite_fact_id),
                )
            }
            LessFactSearchProofByBuiltinRule::OrderSignFromPositiveLiteralBound(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "OrderSignFromPositiveLiteralBound",
                    Some(p.cite_fact_id),
                )
            }
            LessFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "OrderFlipMulMinusOne",
                    Some(p.cite_fact_id),
                )
            }
            _ => builtin_rule_with_optional_cite(runtime, "LessBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(n) => match n {
            NotEqualFactSearchProofByBuiltinRule::FromKnownInNonzeroStandardSet(p) => {
                builtin_rule_with_optional_cite(
                    runtime,
                    "FromKnownInNonzeroStandardSet",
                    Some(p.cite_fact_id),
                )
            }
            _ => builtin_rule_with_optional_cite(runtime, "NotEqualBuiltin", None),
        },
        _ => builtin_rule_with_optional_cite(runtime, "AtomicBuiltin", None),
    }
}

fn why_from_equal_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    match rule {
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(p) => {
            builtin_rule_with_optional_cite(
                runtime,
                "EqualFromKnownDifferenceZero",
                Some(p.cite_fact_id),
            )
        }
        _ => builtin_rule_with_optional_cite(runtime, "EqualityBuiltin", None),
    }
}
