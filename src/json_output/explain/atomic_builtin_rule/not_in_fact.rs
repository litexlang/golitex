//! Leaf explain for atomic family group `not_in_fact`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::{
    ClosedNumericNonMembershipBuiltinRuleProof,
    ListSetExhaustiveDisequalityBuiltinRuleProof,
    NonMembershipOfIntersectFromLeftBuiltinRuleProof,
    NonMembershipOfIntersectFromRightBuiltinRuleProof,
    NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof,
    NonMembershipOfIntervalOutsideBuiltinRuleProof,
    NonMembershipOfSetMinusFromLeftBuiltinRuleProof,
    NonMembershipOfSetMinusFromRightBuiltinRuleProof,
    NonMembershipOfUnionBuiltinRuleProof,
    NotInFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotInFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message(lang),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedNumericNonMembership(_) => None,
            Self::ListSetExhaustiveDisequality(_) => None,
            Self::NonMembershipOfIntersectFromLeft(_) => None,
            Self::NonMembershipOfIntersectFromRight(_) => None,
            Self::NonMembershipOfUnion(_) => None,
            Self::NonMembershipOfSetMinusFromRight(_) => None,
            Self::NonMembershipOfSetMinusFromLeft(_) => None,
            Self::NonMembershipOfIntervalAtOpenEndpoint(_) => None,
            Self::NonMembershipOfIntervalOutside(_) => None,
        }
    }
}

impl ClosedNumericNonMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "Closed Numeric Non Membership",
            "a closed expression that evaluates to a normalized",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "封闭数值非成员",
            "封闭表达式算出的值不属于目标集合",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ListSetExhaustiveDisequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "List Set Exhaustive Disequality",
            "if `x != a_i` for every `a_i` in `{a_1, …, a_n}`,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "列表集穷举不等",
            "与每个列出元素都不等则不属于列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfIntersectFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Non Membership Of Intersect From Left",
            "`not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "由左非成员得交非成员",
            "不属于左因子则不属于交",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfIntersectFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Non Membership Of Intersect From Right",
            "`not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "由右非成员得交非成员",
            "不属于右因子则不属于交",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Non Membership Of Union",
            "`not x $in A` and `not x $in B` ⇒",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "两边非成员得并非成员",
            "两边都不属于则不属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfSetMinusFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Non Membership Of Set Minus From Right",
            "`x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "由右成员得差集非成员",
            "属于右因子则不属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfSetMinusFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Non Membership Of Set Minus From Left",
            "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "由左非成员得差集非成员",
            "不属于左因子则不属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Non Membership Of Interval At Open Endpoint",
            "if the left (resp. right) end is open and `x = a`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "开端点非成员",
            "开端点处不属于区间",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonMembershipOfIntervalOutsideBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Non Membership Of Interval Outside",
            "`x < a` or `b < x` (with closed ends using `<=` denial via strict)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "区间外非成员",
            "落在区间外则不属于",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

