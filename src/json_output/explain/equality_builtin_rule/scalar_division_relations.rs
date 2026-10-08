use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_division_relations::ScalarDivisionRelationProof;

impl ScalarDivisionRelationProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("Product from checked division", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => {
                text("Division from checked product", "b!=0, a=c*b => a/b=c")
            }
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("已知商转乘积", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("已知乘积转商", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("已知商转乘积", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("已知乘积转商", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::ProductFromDivision(_) => text("a/b=c => a=c*b", "a/b=c => a=c*b"),
            Self::DivisionFromProduct(_) => text("b!=0, a=c*b => a/b=c", "b!=0, a=c*b => a/b=c"),
        }
    }
}
