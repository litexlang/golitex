//! Leaf explain for atomic family group `not_subset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_subset::{
    FromKnownNotSupersetBuiltinRuleProof,
    NotSubsetFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownNotSuperset(p) => p.premise_proof.cite_fact_id(),
        }
    }
}

impl FromKnownNotSupersetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownNotSuperset",
            "From Known Not Superset",
            "Duality: known `not B $superset A` proves `not A $subset B`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownNotSuperset",
            "已知非超集",
            "目标由已知的非超集事实推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

