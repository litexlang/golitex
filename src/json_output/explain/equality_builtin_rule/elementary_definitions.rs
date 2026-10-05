use crate::json_output::explain::{BuiltinRuleText, text::text};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_definitions::{TanQuotientDefinitionProof, CotQuotientDefinitionProof, GcdEuclideanStepProof};

impl TanQuotientDefinitionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Tangent quotient definition",
            "Tangent quotient definition: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "正切的商定义",
            "正切的商定义: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正切的商定義",
            "正切的商定義: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Définition quotient de la tangente",
            "Définition quotient de la tangente: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Определение тангенса через частное",
            "Определение тангенса через частное: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Definición de tangente como cociente",
            "Definición de tangente como cociente: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تعريف الظل كنسبة",
            "تعريف الظل كنسبة: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正接の商による定義",
            "正接の商による定義: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "탄젠트의 몫 정의",
            "탄젠트의 몫 정의: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Định nghĩa tang bằng thương",
            "Định nghĩa tang bằng thương: x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        )
    }
}

impl CotQuotientDefinitionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cotangent quotient definition",
            "Cotangent quotient definition: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "余切的商定义",
            "余切的商定义: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "餘切的商定義",
            "餘切的商定義: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Définition quotient de la cotangente",
            "Définition quotient de la cotangente: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Определение котангенса через частное",
            "Определение котангенса через частное: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Definición de cotangente como cociente",
            "Definición de cotangente como cociente: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تعريف ظل التمام كنسبة",
            "تعريف ظل التمام كنسبة: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "余接の商による定義",
            "余接の商による定義: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "코탄젠트의 몫 정의",
            "코탄젠트의 몫 정의: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Định nghĩa cotang bằng thương",
            "Định nghĩa cotang bằng thương: x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        )
    }
}

impl GcdEuclideanStepProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Gcd Euclidean step",
            "Gcd Euclidean step: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最大公约数的欧几里得递推",
            "最大公约数的欧几里得递推: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最大公約數的歐幾里得遞推",
            "最大公約數的歐幾里得遞推: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Étape euclidienne du PGCD",
            "Étape euclidienne du PGCD: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Евклидов шаг для НОД",
            "Евклидов шаг для НОД: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Paso euclidiano del MCD",
            "Paso euclidiano del MCD: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "خطوة إقليدس للقاسم المشترك الأكبر",
            "خطوة إقليدس للقاسم المشترك الأكبر: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最大公約数のユークリッド再帰",
            "最大公約数のユークリッド再帰: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최대공약수의 유클리드 단계",
            "최대공약수의 유클리드 단계: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bước Euclid của ước chung lớn nhất",
            "Bước Euclid của ước chung lớn nhất: a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        )
    }
}
