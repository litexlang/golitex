use crate::json_output::explain::{BuiltinRuleText, text::text};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::rounding_definition_bounds::{FloorLowerBoundProof, FloorStrictUpperBoundProof, CeilStrictLowerBoundProof, CeilUpperBoundProof};

impl FloorLowerBoundProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Floor lower defining bound",
            "Floor lower defining bound: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "向下取整的定义下界",
            "向下取整的定义下界: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "向下取整的定義下界",
            "向下取整的定義下界: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure définissant la partie entière",
            "Borne inférieure définissant la partie entière: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нижняя определяющая граница округления вниз",
            "Нижняя определяющая граница округления вниз: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior que define el suelo",
            "Cota inferior que define el suelo: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الحد السفلي المعرّف للتقريب للأسفل",
            "الحد السفلي المعرّف للتقريب للأسفل: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "床関数の定義下界",
            "床関数の定義下界: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "바닥 함수의 정의 하한",
            "바닥 함수의 정의 하한: x in R => floor(x)<=x",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới xác định hàm sàn",
            "Cận dưới xác định hàm sàn: x in R => floor(x)<=x",
        )
    }
}

impl FloorStrictUpperBoundProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Floor strict upper defining bound",
            "Floor strict upper defining bound: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "向下取整的严格定义上界",
            "向下取整的严格定义上界: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "向下取整的嚴格定義上界",
            "向下取整的嚴格定義上界: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure stricte de la partie entière",
            "Borne supérieure stricte de la partie entière: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Строгая верхняя граница округления вниз",
            "Строгая верхняя граница округления вниз: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior estricta del suelo",
            "Cota superior estricta del suelo: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الحد العلوي الصارم للتقريب للأسفل",
            "الحد العلوي الصارم للتقريب للأسفل: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "床関数の厳密な定義上界",
            "床関数の厳密な定義上界: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "바닥 함수의 엄격한 정의 상한",
            "바닥 함수의 엄격한 정의 상한: x in R => x<floor(x)+1",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên nghiêm ngặt của hàm sàn",
            "Cận trên nghiêm ngặt của hàm sàn: x in R => x<floor(x)+1",
        )
    }
}

impl CeilStrictLowerBoundProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Ceiling strict lower defining bound",
            "Ceiling strict lower defining bound: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "向上取整的严格定义下界",
            "向上取整的严格定义下界: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "向上取整的嚴格定義下界",
            "向上取整的嚴格定義下界: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure stricte du plafond",
            "Borne inférieure stricte du plafond: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Строгая нижняя граница округления вверх",
            "Строгая нижняя граница округления вверх: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior estricta del techo",
            "Cota inferior estricta del techo: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الحد السفلي الصارم للتقريب للأعلى",
            "الحد السفلي الصارم للتقريب للأعلى: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "天井関数の厳密な定義下界",
            "天井関数の厳密な定義下界: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "천장 함수의 엄격한 정의 하한",
            "천장 함수의 엄격한 정의 하한: x in R => ceil(x)-1<x",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới nghiêm ngặt của hàm trần",
            "Cận dưới nghiêm ngặt của hàm trần: x in R => ceil(x)-1<x",
        )
    }
}

impl CeilUpperBoundProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Ceiling upper defining bound",
            "Ceiling upper defining bound: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "向上取整的定义上界",
            "向上取整的定义上界: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "向上取整的定義上界",
            "向上取整的定義上界: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure définissant le plafond",
            "Borne supérieure définissant le plafond: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя определяющая граница округления вверх",
            "Верхняя определяющая граница округления вверх: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior que define el techo",
            "Cota superior que define el techo: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الحد العلوي المعرّف للتقريب للأعلى",
            "الحد العلوي المعرّف للتقريب للأعلى: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "天井関数の定義上界",
            "天井関数の定義上界: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "천장 함수의 정의 상한",
            "천장 함수의 정의 상한: x in R => x<=ceil(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên xác định hàm trần",
            "Cận trên xác định hàm trần: x in R => x<=ceil(x)",
        )
    }
}
