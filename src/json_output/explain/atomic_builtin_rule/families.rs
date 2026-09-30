//! Family-level fallback when a dedicated leaf explain module is not wired yet.
//! Still returns real rule_name + message (not a bare type tag).

use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

use super::text::text;

pub(super) fn family_text(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    match lang {
        OutputLanguage::English => family_text_en(rule_id),
        OutputLanguage::Chinese => family_text_zh(rule_id),
    }
}

fn family_text_en(rule_id: &'static str) -> BuiltinRuleText {
    match rule_id {
        "GreaterFactBuiltin" => text(
            rule_id,
            "Greater-than builtin",
            "Verified by a greater-than builtin rule",
        ),
        "IsSetFactBuiltin" => text(rule_id, "Is-set builtin", "Verified by an is-set builtin rule"),
        "IsNonemptySetFactBuiltin" => text(
            rule_id,
            "Nonempty-set builtin",
            "Verified by a nonempty-set builtin rule",
        ),
        "IsFiniteSetFactBuiltin" => text(
            rule_id,
            "Finite-set builtin",
            "Verified by a finite-set builtin rule",
        ),
        "InFactBuiltin" => text(
            rule_id,
            "Membership builtin",
            "Verified by a membership builtin rule",
        ),
        "IsCartFactBuiltin" => text(
            rule_id,
            "Cartesian-product builtin",
            "Verified by a cartesian-product shape builtin",
        ),
        "IsTupleFactBuiltin" => text(
            rule_id,
            "Tuple builtin",
            "Verified by a tuple-shape builtin rule",
        ),
        "SubsetFactBuiltin" => text(rule_id, "Subset builtin", "Verified by a subset builtin rule"),
        "SupersetFactBuiltin" => text(
            rule_id,
            "Superset builtin",
            "Verified by a superset builtin rule",
        ),
        "ProperSubsetFactBuiltin" => text(
            rule_id,
            "Proper-subset builtin",
            "Verified by a proper-subset builtin rule",
        ),
        "ProperSupersetFactBuiltin" => text(
            rule_id,
            "Proper-superset builtin",
            "Verified by a proper-superset builtin rule",
        ),
        "PrimeFactBuiltin" => text(rule_id, "Prime builtin", "Verified by a primality builtin rule"),
        "CoprimeFactBuiltin" => text(
            rule_id,
            "Coprime builtin",
            "Verified by a coprimality builtin rule",
        ),
        "DvdFactBuiltin" => text(
            rule_id,
            "Divides builtin",
            "Verified by a divisibility builtin rule",
        ),
        "InjectiveFactBuiltin" => text(
            rule_id,
            "Injective builtin",
            "Verified by an injectivity builtin rule",
        ),
        "SurjectiveFactBuiltin" => text(
            rule_id,
            "Surjective builtin",
            "Verified by a surjectivity builtin rule",
        ),
        "BijectiveFactBuiltin" => text(
            rule_id,
            "Bijective builtin",
            "Verified by a bijectivity builtin rule",
        ),
        "IsChoiceFunctionForFactBuiltin" => text(
            rule_id,
            "Choice-function builtin",
            "Verified by a choice-function builtin rule",
        ),
        "NormalAtomicFactBuiltin" => text(
            rule_id,
            "Normal atomic builtin",
            "Verified by a normal atomic-fact builtin rule",
        ),
        "NotNormalAtomicFactBuiltin" => text(
            rule_id,
            "Not-normal atomic builtin",
            "Verified by a negated normal atomic-fact builtin",
        ),
        "NotLessFactBuiltin" => text(
            rule_id,
            "Not-less builtin",
            "Verified by a not-less builtin rule",
        ),
        "NotGreaterFactBuiltin" => text(
            rule_id,
            "Not-greater builtin",
            "Verified by a not-greater builtin rule",
        ),
        "NotLessEqualFactBuiltin" => text(
            rule_id,
            "Not-less-or-equal builtin",
            "Verified by a not-≤ builtin rule",
        ),
        "NotGreaterEqualFactBuiltin" => text(
            rule_id,
            "Not-greater-or-equal builtin",
            "Verified by a not-≥ builtin rule",
        ),
        "NotIsSetFactBuiltin" => text(
            rule_id,
            "Not-is-set builtin",
            "Verified by a not-is-set builtin rule",
        ),
        "NotIsNonemptySetFactBuiltin" => text(
            rule_id,
            "Not-nonempty-set builtin",
            "Verified by a not-nonempty-set builtin rule",
        ),
        "NotIsFiniteSetFactBuiltin" => text(
            rule_id,
            "Not-finite-set builtin",
            "Verified by a not-finite-set builtin rule",
        ),
        "NotInFactBuiltin" => text(
            rule_id,
            "Not-membership builtin",
            "Verified by a not-membership builtin rule",
        ),
        "NotIsCartFactBuiltin" => text(
            rule_id,
            "Not-cartesian builtin",
            "Verified by a not-cartesian-shape builtin",
        ),
        "NotIsTupleFactBuiltin" => text(
            rule_id,
            "Not-tuple builtin",
            "Verified by a not-tuple-shape builtin",
        ),
        "NotSubsetFactBuiltin" => text(
            rule_id,
            "Not-subset builtin",
            "Verified by a not-subset builtin rule",
        ),
        "NotSupersetFactBuiltin" => text(
            rule_id,
            "Not-superset builtin",
            "Verified by a not-superset builtin rule",
        ),
        "NotProperSubsetFactBuiltin" => text(
            rule_id,
            "Not-proper-subset builtin",
            "Verified by a not-proper-subset builtin",
        ),
        "NotProperSupersetFactBuiltin" => text(
            rule_id,
            "Not-proper-superset builtin",
            "Verified by a not-proper-superset builtin",
        ),
        "NotPrimeFactBuiltin" => text(
            rule_id,
            "Not-prime builtin",
            "Verified by a not-prime builtin rule",
        ),
        "NotCoprimeFactBuiltin" => text(
            rule_id,
            "Not-coprime builtin",
            "Verified by a not-coprime builtin rule",
        ),
        "NotDvdFactBuiltin" => text(
            rule_id,
            "Not-divides builtin",
            "Verified by a not-divides builtin rule",
        ),
        "NotInjectiveFactBuiltin" => text(
            rule_id,
            "Not-injective builtin",
            "Verified by a not-injective builtin rule",
        ),
        "NotSurjectiveFactBuiltin" => text(
            rule_id,
            "Not-surjective builtin",
            "Verified by a not-surjective builtin rule",
        ),
        "NotBijectiveFactBuiltin" => text(
            rule_id,
            "Not-bijective builtin",
            "Verified by a not-bijective builtin rule",
        ),
        "NotIsChoiceFunctionForFactBuiltin" => text(
            rule_id,
            "Not-choice-function builtin",
            "Verified by a not-choice-function builtin",
        ),
        _ => text(
            rule_id,
            "Atomic builtin",
            "Verified by an atomic builtin rule",
        ),
    }
}

fn family_text_zh(rule_id: &'static str) -> BuiltinRuleText {
    match rule_id {
        "GreaterFactBuiltin" => text(rule_id, "大于内置规则", "由大于关系的内置规则验证"),
        "IsSetFactBuiltin" => text(rule_id, "是集合内置规则", "由「是集合」内置规则验证"),
        "IsNonemptySetFactBuiltin" => text(rule_id, "非空集合内置规则", "由非空集合内置规则验证"),
        "IsFiniteSetFactBuiltin" => text(rule_id, "有限集合内置规则", "由有限集合内置规则验证"),
        "InFactBuiltin" => text(rule_id, "成员关系内置规则", "由成员关系内置规则验证"),
        "IsCartFactBuiltin" => text(rule_id, "笛卡尔积内置规则", "由笛卡尔积形状内置规则验证"),
        "IsTupleFactBuiltin" => text(rule_id, "元组内置规则", "由元组形状内置规则验证"),
        "SubsetFactBuiltin" => text(rule_id, "子集内置规则", "由子集内置规则验证"),
        "SupersetFactBuiltin" => text(rule_id, "超集内置规则", "由超集内置规则验证"),
        "ProperSubsetFactBuiltin" => text(rule_id, "真子集内置规则", "由真子集内置规则验证"),
        "ProperSupersetFactBuiltin" => text(rule_id, "真超集内置规则", "由真超集内置规则验证"),
        "PrimeFactBuiltin" => text(rule_id, "素数内置规则", "由素性内置规则验证"),
        "CoprimeFactBuiltin" => text(rule_id, "互素内置规则", "由互素性内置规则验证"),
        "DvdFactBuiltin" => text(rule_id, "整除内置规则", "由整除内置规则验证"),
        "InjectiveFactBuiltin" => text(rule_id, "单射内置规则", "由单射内置规则验证"),
        "SurjectiveFactBuiltin" => text(rule_id, "满射内置规则", "由满射内置规则验证"),
        "BijectiveFactBuiltin" => text(rule_id, "双射内置规则", "由双射内置规则验证"),
        "IsChoiceFunctionForFactBuiltin" => {
            text(rule_id, "选择函数内置规则", "由选择函数内置规则验证")
        }
        "NormalAtomicFactBuiltin" => text(rule_id, "普通原子内置规则", "由普通原子事实内置规则验证"),
        "NotNormalAtomicFactBuiltin" => {
            text(rule_id, "非普通原子内置规则", "由否定普通原子事实的内置规则验证")
        }
        "NotLessFactBuiltin" => text(rule_id, "不小于内置规则", "由「不小于」内置规则验证"),
        "NotGreaterFactBuiltin" => text(rule_id, "不大于内置规则", "由「不大于」内置规则验证"),
        "NotLessEqualFactBuiltin" => text(rule_id, "不≤内置规则", "由「不≤」内置规则验证"),
        "NotGreaterEqualFactBuiltin" => text(rule_id, "不≥内置规则", "由「不≥」内置规则验证"),
        "NotIsSetFactBuiltin" => text(rule_id, "不是集合内置规则", "由「不是集合」内置规则验证"),
        "NotIsNonemptySetFactBuiltin" => {
            text(rule_id, "非非空集合内置规则", "由「非非空集合」内置规则验证")
        }
        "NotIsFiniteSetFactBuiltin" => {
            text(rule_id, "非有限集合内置规则", "由「非有限集合」内置规则验证")
        }
        "NotInFactBuiltin" => text(rule_id, "非成员关系内置规则", "由「非成员」内置规则验证"),
        "NotIsCartFactBuiltin" => {
            text(rule_id, "非笛卡尔积内置规则", "由「非笛卡尔积形状」内置规则验证")
        }
        "NotIsTupleFactBuiltin" => text(rule_id, "非元组内置规则", "由「非元组形状」内置规则验证"),
        "NotSubsetFactBuiltin" => text(rule_id, "非子集内置规则", "由「非子集」内置规则验证"),
        "NotSupersetFactBuiltin" => text(rule_id, "非超集内置规则", "由「非超集」内置规则验证"),
        "NotProperSubsetFactBuiltin" => {
            text(rule_id, "非真子集内置规则", "由「非真子集」内置规则验证")
        }
        "NotProperSupersetFactBuiltin" => {
            text(rule_id, "非真超集内置规则", "由「非真超集」内置规则验证")
        }
        "NotPrimeFactBuiltin" => text(rule_id, "非素数内置规则", "由「非素数」内置规则验证"),
        "NotCoprimeFactBuiltin" => text(rule_id, "非互素内置规则", "由「非互素」内置规则验证"),
        "NotDvdFactBuiltin" => text(rule_id, "非整除内置规则", "由「非整除」内置规则验证"),
        "NotInjectiveFactBuiltin" => text(rule_id, "非单射内置规则", "由「非单射」内置规则验证"),
        "NotSurjectiveFactBuiltin" => text(rule_id, "非满射内置规则", "由「非满射」内置规则验证"),
        "NotBijectiveFactBuiltin" => text(rule_id, "非双射内置规则", "由「非双射」内置规则验证"),
        "NotIsChoiceFunctionForFactBuiltin" => {
            text(rule_id, "非选择函数内置规则", "由「非选择函数」内置规则验证")
        }
        _ => text(rule_id, "原子内置规则", "由原子内置规则验证"),
    }
}
