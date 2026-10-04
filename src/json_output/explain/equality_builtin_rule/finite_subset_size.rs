use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_subset_size::FiniteSetEqualFromSubsetSizeBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "Equal finite subset cardinality",
            "A finite subset with the same cardinality as its containing set equals that set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "有限子集等大则相等",
            "有限子集与包含它的集合基数相等，因此两集合相等",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "有限子集等基數",
            "有限子集與包含它的集合基數相同時，兩集合相等",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
                "FiniteSetEqualFromSubsetSize",
                "Même cardinal d'un sous-ensemble fini",
                "Un sous-ensemble fini de même cardinal que l'ensemble qui le contient est égal à cet ensemble",
            )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
                "FiniteSetEqualFromSubsetSize",
                "Равная мощность конечного подмножества",
                "Конечное подмножество той же мощности, что и содержащее его множество, равно этому множеству",
            )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
                "FiniteSetEqualFromSubsetSize",
                "Igual cardinalidad de subconjunto finito",
                "Un subconjunto finito con la misma cardinalidad que el conjunto que lo contiene es igual a él",
            )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
                "FiniteSetEqualFromSubsetSize",
                "تساوي عدد عناصر المجموعة الجزئية المنتهية",
                "المجموعة الجزئية المنتهية ذات عدد العناصر نفسه للمجموعة التي تحتويها تساوي تلك المجموعة",
            )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "有限部分集合の濃度の一致",
            "有限部分集合とそれを含む集合の濃度が同じなら両集合は等しいです",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "유한 부분집합의 동일 기수",
            "유한 부분집합과 이를 포함하는 집합의 기수가 같으면 두 집합은 같습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FiniteSetEqualFromSubsetSize",
            "Cùng lực lượng của tập con hữu hạn",
            "Tập con hữu hạn có cùng lực lượng với tập chứa nó thì bằng tập đó",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}
