//! Localized copy for frequent atomic (non-equality) builtin rule ids.
//! English is complete here; Chinese is filled for the hot set (others → EN).

use super::bilingual::bilingual_builtin;
use super::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

pub fn explain_atomic_rule_id(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    match rule_id {
        "FromKnownInNatural" => bilingual_builtin(
            rule_id,
            "From known in N",
            "The goal follows from a known natural-number membership",
            Some("已知属于自然数"),
            Some("目标由已知的自然数成员关系推出"),
            lang,
        ),
        "FromKnownInPositiveNatural" => bilingual_builtin(
            rule_id,
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
            Some("已知属于正自然数"),
            Some("目标由已知的正自然数成员关系推出"),
            lang,
        ),
        "FromKnownGreater" => bilingual_builtin(
            rule_id,
            "From known greater",
            "The weak order follows from a known strict greater fact",
            Some("已知严格大于"),
            Some("弱序目标由已知的严格大于推出"),
            lang,
        ),
        "OrderReflexivity" => bilingual_builtin(
            rule_id,
            "Order reflexivity",
            "A quantity is less-or-equal to itself",
            Some("序的自反性"),
            Some("任何量都不大于也不小于自己（≤ 自身）"),
            lang,
        ),
        "ClosedNumericComparison" => bilingual_builtin(
            rule_id,
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
            Some("封闭数值比较"),
            Some("两边都是可计算的数，并满足所述比较"),
            lang,
        ),
        "OrderFlipMulMinusOne" => bilingual_builtin(
            rule_id,
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
            Some("乘以 -1 反转不等式"),
            Some("两边同乘 -1 后不等式方向相反"),
            lang,
        ),
        "FromKnownInPositiveStandardSet" => bilingual_builtin(
            rule_id,
            "From known in positive set",
            "The goal follows from membership in a positive standard set",
            Some("已知属于正标准集"),
            Some("目标由正标准集上的成员关系推出"),
            lang,
        ),
        "FromKnownInNegativeStandardSet" => bilingual_builtin(
            rule_id,
            "From known in negative set",
            "The goal follows from membership in a negative standard set",
            Some("已知属于负标准集"),
            Some("目标由负标准集上的成员关系推出"),
            lang,
        ),
        "FromKnownInNonzeroStandardSet" => bilingual_builtin(
            rule_id,
            "From known nonzero",
            "Inequality follows from known nonzero / nonzero-set membership",
            Some("已知非零"),
            Some("不等关系由已知非零（或非零集成员）推出"),
            lang,
        ),
        "OrderSignFromPositiveLiteralBound" => bilingual_builtin(
            rule_id,
            "Sign from positive bound",
            "A positive literal bound forces the stated order/sign",
            Some("由正下界得符号"),
            Some("正的字面下界推出所述序/符号关系"),
            lang,
        ),
        "OrderSignFromNegativeLiteralBound" => bilingual_builtin(
            rule_id,
            "Sign from negative bound",
            "A negative literal bound forces the stated order/sign",
            Some("由负上界得符号"),
            Some("负的字面上界推出所述序/符号关系"),
            lang,
        ),
        other => {
            // English-readable fallback; Chinese intentionally reuses English for now.
            let rule_name = humanize_rule_id(other);
            let message = format!("Verified by the `{other}` builtin rule");
            BuiltinRuleText {
                rule_id: other,
                rule_name,
                message,
            }
        }
    }
}

fn humanize_rule_id(rule_id: &str) -> String {
    let mut out = String::new();
    for (i, ch) in rule_id.chars().enumerate() {
        if i > 0 && ch.is_ascii_uppercase() {
            out.push(' ');
        }
        out.push(ch);
    }
    out
}
