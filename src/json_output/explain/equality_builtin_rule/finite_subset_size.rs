use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_subset_size::FiniteSetEqualFromSubsetSizeBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetEqualFromSubsetSize",
                "Equal finite subset cardinality",
                "A finite subset with the same cardinality as its containing set equals that set",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetEqualFromSubsetSize",
                "有限子集等基數",
                "有限子集與包含它的集合基數相同時，兩集合相等",
            ),
            OutputLanguage::French => text(
                "FiniteSetEqualFromSubsetSize",
                "Même cardinal d'un sous-ensemble fini",
                "Un sous-ensemble fini de même cardinal que l'ensemble qui le contient est égal à cet ensemble",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetEqualFromSubsetSize",
                "Равная мощность конечного подмножества",
                "Конечное подмножество той же мощности, что и содержащее его множество, равно этому множеству",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetEqualFromSubsetSize",
                "Igual cardinalidad de subconjunto finito",
                "Un subconjunto finito con la misma cardinalidad que el conjunto que lo contiene es igual a él",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetEqualFromSubsetSize",
                "تساوي عدد عناصر المجموعة الجزئية المنتهية",
                "المجموعة الجزئية المنتهية ذات عدد العناصر نفسه للمجموعة التي تحتويها تساوي تلك المجموعة",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetEqualFromSubsetSize",
                "有限部分集合の濃度の一致",
                "有限部分集合とそれを含む集合の濃度が同じなら両集合は等しいです",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetEqualFromSubsetSize",
                "유한 부분집합의 동일 기수",
                "유한 부분집합과 이를 포함하는 집합의 기수가 같으면 두 집합은 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetEqualFromSubsetSize",
                "Cùng lực lượng của tập con hữu hạn",
                "Tập con hữu hạn có cùng lực lượng với tập chứa nó thì bằng tập đó",
            ),

            OutputLanguage::Chinese => text(
                "FiniteSetEqualFromSubsetSize",
                "有限子集等大则相等",
                "有限子集与包含它的集合基数相等，因此两集合相等",
            ),
        }
    }
}
