//! Leaf explain for atomic family group `is_finite_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::{
    ClosedRangeFiniteBuiltinRuleProof,
    FiniteSeqFromFiniteCodomainBuiltinRuleProof,
    FiniteSeqZeroLengthFiniteBuiltinRuleProof,
    IsFiniteSetFactSearchProofByBuiltinRule,
    ListSetFiniteBuiltinRuleProof,
    RangeFiniteBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsFiniteSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ListSet(p) => p.rule_id_and_message(lang),
            Self::ClosedRange(p) => p.rule_id_and_message(lang),
            Self::Range(p) => p.rule_id_and_message(lang),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message(lang),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ListSet(_) => None,
            Self::ClosedRange(_) => None,
            Self::Range(_) => None,
            Self::FiniteSeqZeroLength(_) => None,
            Self::FiniteSeqFromFiniteCodomain(_) => None,
        }
    }
}

impl ListSetFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "List Set",
            "Verified by the list Set builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "列表集有限",
            "有限列表集是有限集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ClosedRangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Closed Range",
            "Verified by the closed Range builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "闭区间有限",
            "整数闭区间是有限集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl RangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Range",
            "Range",
            "Verified by the range builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "Range",
            "区间有限",
            "整数区间是有限集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSeqZeroLengthFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Finite Seq Zero Length",
            "Length-zero finite sequence carrier is always finite (one empty sequence)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "零长度有限序列",
            "零长度有限序列载体有限",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSeqFromFiniteCodomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Finite Seq From Finite Codomain",
            "Finite codomain ⇒ finite length-n sequence carrier",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "有限陪域的有限序列",
            "有限陪域上的定长序列载体有限",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

