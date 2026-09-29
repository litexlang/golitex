//! Localized copy for frequent atomic (non-equality) builtin rule ids.
//! Dedicate files per rule later; this covers the Normal-path hot set first.

use super::fallback::{fallback_builtin_rule_text, BuiltinRuleText};
use crate::launch_command::OutputLanguage;

pub fn explain_atomic_rule_id(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    let pair = match (rule_id, lang) {
        ("FromKnownInNatural", OutputLanguage::English) => Some((
            "From known in N",
            "The goal follows from a known natural-number membership",
        )),
        ("FromKnownInNatural", OutputLanguage::Chinese) => {
            Some(("已知属于自然数", "目标由已知的自然数成员关系推出"))
        }
        ("FromKnownInPositiveNatural", OutputLanguage::English) => Some((
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
        )),
        ("FromKnownInPositiveNatural", OutputLanguage::Chinese) => {
            Some(("已知属于正自然数", "目标由已知的正自然数成员关系推出"))
        }
        ("FromKnownGreater", OutputLanguage::English) => Some((
            "From known greater",
            "The weak order follows from a known strict greater fact",
        )),
        ("FromKnownGreater", OutputLanguage::Chinese) => {
            Some(("已知严格大于", "弱序目标由已知的严格大于推出"))
        }
        ("OrderReflexivity", OutputLanguage::English) => {
            Some(("Order reflexivity", "A quantity is less-or-equal to itself"))
        }
        ("OrderReflexivity", OutputLanguage::Chinese) => {
            Some(("序的自反性", "任何量都不大于也不小于自己（≤ 自身）"))
        }
        ("ClosedNumericComparison", OutputLanguage::English) => Some((
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
        )),
        ("ClosedNumericComparison", OutputLanguage::Chinese) => {
            Some(("封闭数值比较", "两边都是可计算的数，并满足所述比较"))
        }
        ("OrderFlipMulMinusOne", OutputLanguage::English) => Some((
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
        )),
        ("OrderFlipMulMinusOne", OutputLanguage::Chinese) => {
            Some(("乘以 -1 反转不等式", "两边同乘 -1 后不等式方向相反"))
        }
        ("FromKnownInPositiveStandardSet", OutputLanguage::English) => Some((
            "From known in positive set",
            "The goal follows from membership in a positive standard set",
        )),
        ("FromKnownInPositiveStandardSet", OutputLanguage::Chinese) => {
            Some(("已知属于正标准集", "目标由正标准集上的成员关系推出"))
        }
        ("FromKnownInNegativeStandardSet", OutputLanguage::English) => Some((
            "From known in negative set",
            "The goal follows from membership in a negative standard set",
        )),
        ("FromKnownInNegativeStandardSet", OutputLanguage::Chinese) => {
            Some(("已知属于负标准集", "目标由负标准集上的成员关系推出"))
        }
        ("FromKnownInNonzeroStandardSet", OutputLanguage::English) => Some((
            "From known nonzero",
            "Inequality follows from known nonzero / nonzero-set membership",
        )),
        ("FromKnownInNonzeroStandardSet", OutputLanguage::Chinese) => {
            Some(("已知非零", "不等关系由已知非零（或非零集成员）推出"))
        }
        ("OrderSignFromPositiveLiteralBound", OutputLanguage::English) => Some((
            "Sign from positive bound",
            "A positive literal bound forces the stated order/sign",
        )),
        ("OrderSignFromPositiveLiteralBound", OutputLanguage::Chinese) => {
            Some(("由正下界得符号", "正的字面下界推出所述序/符号关系"))
        }
        ("OrderSignFromNegativeLiteralBound", OutputLanguage::English) => Some((
            "Sign from negative bound",
            "A negative literal bound forces the stated order/sign",
        )),
        ("OrderSignFromNegativeLiteralBound", OutputLanguage::Chinese) => {
            Some(("由负上界得符号", "负的字面上界推出所述序/符号关系"))
        }
        _ => None,
    };
    match pair {
        Some((rule_name, message)) => BuiltinRuleText {
            rule_id,
            rule_name: rule_name.to_string(),
            message: message.to_string(),
        },
        None => fallback_builtin_rule_text(rule_id, lang),
    }
}
