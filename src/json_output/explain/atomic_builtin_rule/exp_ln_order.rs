use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::exp_ln_order::*;
use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::launch_command::OutputLanguage;

impl ExpStrictMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "exp strict order preservation",
            "exp strict order preservation: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "exp 严格保序",
            "exp 严格保序: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "exp 嚴格保序",
            "exp 嚴格保序: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "exp préservation de l’ordre strict",
            "exp préservation de l’ordre strict: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "exp сохранение строгого порядка",
            "exp сохранение строгого порядка: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "exp preservación del orden estricto",
            "exp preservación del orden estricto: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "exp حفظ الترتيب الصارم",
            "exp حفظ الترتيب الصارم: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "exp 狭義順序の保存",
            "exp 狭義順序の保存: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "exp 엄격한 순서 보존",
            "exp 엄격한 순서 보존: a,b in R, a<b => exp(a)<exp(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "exp bảo toàn thứ tự nghiêm ngặt",
            "exp bảo toàn thứ tự nghiêm ngặt: a,b in R, a<b => exp(a)<exp(b)",
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

impl LnStrictMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ln strict order preservation",
            "ln strict order preservation: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("ln 严格保序", "ln 严格保序: a,b in R+, a<b => ln(a)<ln(b)")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("ln 嚴格保序", "ln 嚴格保序: a,b in R+, a<b => ln(a)<ln(b)")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ln préservation de l’ordre strict",
            "ln préservation de l’ordre strict: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ln сохранение строгого порядка",
            "ln сохранение строгого порядка: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ln preservación del orden estricto",
            "ln preservación del orden estricto: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ln حفظ الترتيب الصارم",
            "ln حفظ الترتيب الصارم: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ln 狭義順序の保存",
            "ln 狭義順序の保存: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ln 엄격한 순서 보존",
            "ln 엄격한 순서 보존: a,b in R+, a<b => ln(a)<ln(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ln bảo toàn thứ tự nghiêm ngặt",
            "ln bảo toàn thứ tự nghiêm ngặt: a,b in R+, a<b => ln(a)<ln(b)",
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

impl ExpStrictOrderReflectionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "exp strict order reflection",
            "exp strict order reflection: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "exp 严格顺序反推",
            "exp 严格顺序反推: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "exp 嚴格順序反推",
            "exp 嚴格順序反推: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "exp réflexion de l’ordre strict",
            "exp réflexion de l’ordre strict: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "exp отражение строгого порядка",
            "exp отражение строгого порядка: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "exp reflexión del orden estricto",
            "exp reflexión del orden estricto: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "exp عكس الترتيب الصارم",
            "exp عكس الترتيب الصارم: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "exp 狭義順序の反映",
            "exp 狭義順序の反映: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "exp 엄격한 순서 반영",
            "exp 엄격한 순서 반영: a,b in R, exp(a)<exp(b) => a<b",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "exp phản ánh thứ tự nghiêm ngặt",
            "exp phản ánh thứ tự nghiêm ngặt: a,b in R, exp(a)<exp(b) => a<b",
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

impl LnStrictOrderReflectionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ln strict order reflection",
            "ln strict order reflection: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ln 严格顺序反推",
            "ln 严格顺序反推: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ln 嚴格順序反推",
            "ln 嚴格順序反推: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ln réflexion de l’ordre strict",
            "ln réflexion de l’ordre strict: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ln отражение строгого порядка",
            "ln отражение строгого порядка: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ln reflexión del orden estricto",
            "ln reflexión del orden estricto: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ln عكس الترتيب الصارم",
            "ln عكس الترتيب الصارم: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ln 狭義順序の反映",
            "ln 狭義順序の反映: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ln 엄격한 순서 반영",
            "ln 엄격한 순서 반영: a,b in R+, ln(a)<ln(b) => a<b",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ln phản ánh thứ tự nghiêm ngặt",
            "ln phản ánh thứ tự nghiêm ngặt: a,b in R+, ln(a)<ln(b) => a<b",
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

impl ExpWeakMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "exp weak order preservation",
            "exp weak order preservation: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("exp 弱保序", "exp 弱保序: a,b in R, a<=b => exp(a)<=exp(b)")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("exp 弱保序", "exp 弱保序: a,b in R, a<=b => exp(a)<=exp(b)")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "exp préservation de l’ordre large",
            "exp préservation de l’ordre large: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "exp сохранение нестрогого порядка",
            "exp сохранение нестрогого порядка: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "exp preservación del orden débil",
            "exp preservación del orden débil: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "exp حفظ الترتيب غير الصارم",
            "exp حفظ الترتيب غير الصارم: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "exp 広義順序の保存",
            "exp 広義順序の保存: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "exp 비엄격한 순서 보존",
            "exp 비엄격한 순서 보존: a,b in R, a<=b => exp(a)<=exp(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "exp bảo toàn thứ tự không nghiêm ngặt",
            "exp bảo toàn thứ tự không nghiêm ngặt: a,b in R, a<=b => exp(a)<=exp(b)",
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

impl LnWeakMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ln weak order preservation",
            "ln weak order preservation: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("ln 弱保序", "ln 弱保序: a,b in R+, a<=b => ln(a)<=ln(b)")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("ln 弱保序", "ln 弱保序: a,b in R+, a<=b => ln(a)<=ln(b)")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ln préservation de l’ordre large",
            "ln préservation de l’ordre large: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ln сохранение нестрогого порядка",
            "ln сохранение нестрогого порядка: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ln preservación del orden débil",
            "ln preservación del orden débil: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ln حفظ الترتيب غير الصارم",
            "ln حفظ الترتيب غير الصارم: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ln 広義順序の保存",
            "ln 広義順序の保存: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ln 비엄격한 순서 보존",
            "ln 비엄격한 순서 보존: a,b in R+, a<=b => ln(a)<=ln(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ln bảo toàn thứ tự không nghiêm ngặt",
            "ln bảo toàn thứ tự không nghiêm ngặt: a,b in R+, a<=b => ln(a)<=ln(b)",
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

impl ExpWeakOrderReflectionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "exp weak order reflection",
            "exp weak order reflection: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "exp 弱顺序反推",
            "exp 弱顺序反推: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "exp 弱順序反推",
            "exp 弱順序反推: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "exp réflexion de l’ordre large",
            "exp réflexion de l’ordre large: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "exp отражение нестрогого порядка",
            "exp отражение нестрогого порядка: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "exp reflexión del orden débil",
            "exp reflexión del orden débil: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "exp عكس الترتيب غير الصارم",
            "exp عكس الترتيب غير الصارم: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "exp 広義順序の反映",
            "exp 広義順序の反映: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "exp 비엄격한 순서 반영",
            "exp 비엄격한 순서 반영: a,b in R, exp(a)<=exp(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "exp phản ánh thứ tự không nghiêm ngặt",
            "exp phản ánh thứ tự không nghiêm ngặt: a,b in R, exp(a)<=exp(b) => a<=b",
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

impl LnWeakOrderReflectionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ln weak order reflection",
            "ln weak order reflection: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ln 弱顺序反推",
            "ln 弱顺序反推: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ln 弱順序反推",
            "ln 弱順序反推: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ln réflexion de l’ordre large",
            "ln réflexion de l’ordre large: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ln отражение нестрогого порядка",
            "ln отражение нестрогого порядка: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ln reflexión del orden débil",
            "ln reflexión del orden débil: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ln عكس الترتيب غير الصارم",
            "ln عكس الترتيب غير الصارم: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ln 広義順序の反映",
            "ln 広義順序の反映: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ln 비엄격한 순서 반영",
            "ln 비엄격한 순서 반영: a,b in R+, ln(a)<=ln(b) => a<=b",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ln phản ánh thứ tự không nghiêm ngặt",
            "ln phản ánh thứ tự không nghiêm ngặt: a,b in R+, ln(a)<=ln(b) => a<=b",
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
