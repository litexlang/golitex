//! Leaf explain for atomic family group `superset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::superset::{
    StandardSetSupersetBuiltinRuleProof,
    SupersetFactSearchProofByBuiltinRule,
    SupersetReflexivityBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl SupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_id_and_message(lang),
            Self::SupersetReflexivity(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardSetSuperset(_) => None,
            Self::SupersetReflexivity(_) => None,
        }
    }
}

impl StandardSetSupersetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetSuperset",
            "Standard Set Superset",
            "Verified by the standard Set Superset builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardSetSuperset",
            "标准集超集",
            "标准数集之间的固定超集关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SupersetReflexivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SupersetReflexivity",
            "Superset Reflexivity",
            "Verified by the superset Reflexivity builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SupersetReflexivity",
            "超集自反",
            "任意集合是自身的超集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

