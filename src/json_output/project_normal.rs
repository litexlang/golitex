//! Project ExecStmtResult → Normal JSON (see README).

use super::explain::{
    explain_atomic_rule_id, explain_compound_fact_why, explain_equality_builtin_rule,
};
use super::helper::{
    array_of_strings, bool_value, builtin_rule_with_optional_cite, cite_forall_from_fact_id,
    cite_from_fact_id, empty_string_array, infer_fact_texts_from_store_and_infer, object,
    output_language, store_fact_texts, string,
};
use super::project_stmt_catalog::project_non_fact_stmt;
use crate::ast::fact::AtomicFact;
use crate::execute::{ExecFactStmtResult, ExecStmtResult};

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
    let text = explain_compound_fact_why(kind, output_language(runtime));
    object(vec![
        ("type", string(text.type_tag)),
        ("rule_name", string(text.rule_name)),
        ("message", string(text.message)),
    ])
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
    let lang = output_language(runtime);
    let cite_text = |rule_id: &'static str, cite: Option<_>| {
        let text = explain_atomic_rule_id(rule_id, lang);
        builtin_rule_with_optional_cite(runtime, &text, cite)
    };
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(g) => match g {
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInNatural(p) => {
                cite_text("FromKnownInNatural", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(p) => {
                cite_text("FromKnownInPositiveNatural", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(p) => {
                cite_text("FromKnownGreater", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                cite_text("OrderFlipMulMinusOne", Some(p.cite_fact_id))
            }
            GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(_) => {
                cite_text("OrderReflexivity", None)
            }
            GreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(_) => {
                cite_text("ClosedNumericComparison", None)
            }
            _ => cite_text("GreaterEqualBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(l) => match l {
            LessEqualFactSearchProofByBuiltinRule::FromKnownInNatural(p) => {
                cite_text("FromKnownInNatural", Some(p.cite_fact_id))
            }
            LessEqualFactSearchProofByBuiltinRule::FromKnownInPositiveStandardSet(p) => {
                cite_text("FromKnownInPositiveStandardSet", Some(p.cite_fact_id))
            }
            LessEqualFactSearchProofByBuiltinRule::FromKnownInNegativeStandardSet(p) => {
                cite_text("FromKnownInNegativeStandardSet", Some(p.cite_fact_id))
            }
            LessEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                cite_text("OrderFlipMulMinusOne", Some(p.cite_fact_id))
            }
            LessEqualFactSearchProofByBuiltinRule::OrderSignFromNegativeLiteralBound(p) => {
                cite_text("OrderSignFromNegativeLiteralBound", Some(p.cite_fact_id))
            }
            _ => cite_text("LessEqualBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(l) => match l {
            LessFactSearchProofByBuiltinRule::FromKnownInPositiveStandardSet(p) => {
                cite_text("FromKnownInPositiveStandardSet", Some(p.cite_fact_id))
            }
            LessFactSearchProofByBuiltinRule::FromKnownInNegativeStandardSet(p) => {
                cite_text("FromKnownInNegativeStandardSet", Some(p.cite_fact_id))
            }
            LessFactSearchProofByBuiltinRule::OrderSignFromPositiveLiteralBound(p) => {
                cite_text("OrderSignFromPositiveLiteralBound", Some(p.cite_fact_id))
            }
            LessFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p) => {
                cite_text("OrderFlipMulMinusOne", Some(p.cite_fact_id))
            }
            _ => cite_text("LessBuiltin", None),
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(n) => match n {
            NotEqualFactSearchProofByBuiltinRule::FromKnownInNonzeroStandardSet(p) => {
                cite_text("FromKnownInNonzeroStandardSet", Some(p.cite_fact_id))
            }
            NotEqualFactSearchProofByBuiltinRule::NotEqualSymmetry(_) => {
                cite_text("NotEqualSymmetry", None)
            }
            _ => cite_text("NotEqualBuiltin", None),
        },
        _ => cite_text("AtomicBuiltin", None),
    }
}

fn why_from_equal_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_equality_builtin_rule(rule, lang);
    let cite = match rule {
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(p) => {
            Some(p.cite_fact_id)
        }
        _ => None,
    };
    builtin_rule_with_optional_cite(runtime, &text, cite)
}
