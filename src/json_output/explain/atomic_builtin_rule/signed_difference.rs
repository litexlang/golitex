use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{LessFromNegativeDifferenceBuiltinRuleProof, NegativeDifferenceFromLessBuiltinRuleProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{LessEqualFromNonpositiveDifferenceBuiltinRuleProof, NonpositiveDifferenceFromLessEqualBuiltinRuleProof};
use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl LessFromNegativeDifferenceBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Negative difference implies strict order",
            "If a - b is negative, then a < b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("差为负推出严格大小关系", "若 a - b 为负，则 a < b。")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("差為負推出嚴格大小關係", "若 a - b 為負，則 a < b。")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Différence négative et ordre strict", "Si a - b est négatif, alors a < b.")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Отрицательная разность и строгий порядок",
            "Если a - b отрицательно, то a < b.",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Diferencia negativa y orden estricto", "Si a - b es negativo, entonces a < b.")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الفرق السالب والترتيب الصارم", "إذا كان a - b سالبًا فإن a < b.")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("負の差と厳密な順序", "a - b が負なら a < b です。")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("음의 차와 엄격한 순서", "a - b가 음수이면 a < b입니다.")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hiệu âm và thứ tự nghiêm ngặt", "Nếu a - b âm thì a < b.")
    }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NegativeDifferenceFromLessBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Strict order gives a negative difference",
            "If a < b, then a - b is negative.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("严格大小关系推出差为负", "若 a < b，则差 a - b 为负。")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("嚴格大小關係推出差為負", "若 a < b，則差 a - b 為負。")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Ordre strict et différence négative", "Si a < b, alors a - b est négatif.")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Строгий порядок и отрицательная разность",
            "Если a < b, то a - b отрицательно.",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Orden estricto y diferencia negativa", "Si a < b, entonces a - b es negativo.")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الترتيب الصارم يعطي فرقًا سالبًا", "إذا كان a < b فإن الفرق a - b سالب.")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("厳密な順序から負の差", "a < b なら差 a - b は負です。")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("엄격한 순서에서 음의 차", "a < b이면 차 a - b는 음수입니다.")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Thứ tự nghiêm ngặt cho hiệu âm", "Nếu a < b thì hiệu a - b âm.")
    }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LessEqualFromNonpositiveDifferenceBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonpositive difference implies weak order",
            "If a - b is nonpositive, then a <= b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("差非正推出非严格大小关系", "若 a - b 非正，则 a <= b。")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("差非正推出非嚴格大小關係", "若 a - b 非正，則 a <= b。")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence non positive et ordre large",
            "Si a - b est non positif, alors a <= b.",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неположительная разность и нестрогий порядок",
            "Если a - b неположительно, то a <= b.",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Diferencia no positiva y orden débil", "Si a - b no es positivo, entonces a <= b.")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الفرق غير الموجب والترتيب غير الصارم", "إذا كان a - b غير موجب فإن a <= b.")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("非正の差と弱い順序", "a - b が非正なら a <= b です。")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("양이 아닌 차와 비엄격 순서", "a - b가 양수가 아니면 a <= b입니다.")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu không dương và thứ tự không nghiêm ngặt",
            "Nếu a - b không dương thì a <= b.",
        )
    }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NonpositiveDifferenceFromLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Weak order gives a nonpositive difference",
            "If a <= b, then a - b is nonpositive.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非严格大小关系推出差非正", "若 a <= b，则差 a - b 非正。")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("非嚴格大小關係推出差非正", "若 a <= b，則差 a - b 非正。")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ordre large et différence non positive",
            "Si a <= b, alors a - b est non positif.",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогий порядок и неположительная разность",
            "Если a <= b, то a - b неположительно.",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Orden débil y diferencia no positiva", "Si a <= b, entonces a - b no es positivo.")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الترتيب غير الصارم يعطي فرقًا غير موجب",
            "إذا كان a <= b فإن الفرق a - b غير موجب.",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("弱い順序から非正の差", "a <= b なら差 a - b は非正です。")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("비엄격 순서에서 양이 아닌 차", "a <= b이면 차 a - b는 양수가 아닙니다.")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thứ tự không nghiêm ngặt cho hiệu không dương",
            "Nếu a <= b thì hiệu a - b không dương.",
        )
    }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}
