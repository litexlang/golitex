use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl FromKnownOrderComplementBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FromKnownOrderComplement",
                "Known real-order complement",
                "A known negated comparison is equivalent to its complementary real order",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FromKnownOrderComplement",
                "已知實數序補關係",
                "已知否定比較等價於互補的實數序關係",
            ),
            OutputLanguage::French => text(
                "FromKnownOrderComplement",
                "Complément d'ordre réel connu",
                "Une comparaison niée connue équivaut à son ordre réel complémentaire",
            ),
            OutputLanguage::Russian => text(
                "FromKnownOrderComplement",
                "Известное дополнение вещественного порядка",
                "Известное отрицание сравнения эквивалентно дополнительному вещественному порядку",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownOrderComplement",
                "Complemento de orden real conocido",
                "Una comparación negada conocida equivale a su orden real complementario",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownOrderComplement",
                "متمم ترتيب حقيقي معلوم",
                "المقارنة المنفية المعلومة تكافئ ترتيبها الحقيقي المتمم",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownOrderComplement",
                "既知の実数順序の補関係",
                "既知の比較の否定は補となる実数の順序関係と同値です",
            ),
            OutputLanguage::Korean => text(
                "FromKnownOrderComplement",
                "알려진 실수 순서 보완 관계",
                "알려진 부정 비교는 보완 실수 순서 관계와 동치입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownOrderComplement",
                "Quan hệ bù thứ tự thực đã biết",
                "So sánh phủ định đã biết tương đương với quan hệ thứ tự thực bù",
            ),

            OutputLanguage::Chinese => text(
                "FromKnownOrderComplement",
                "已知实数序的互补关系",
                "由已知比较事实及实数序的互补关系得到目标",
            ),
        }
    }
}
