use crate::json_output::explain::{BuiltinRuleText, text::text};
use crate::launch_command::OutputLanguage;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_fixed_base::{LnAsEulerLogProof, ExpAsEulerPowerProof};

impl LnAsEulerLogProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural log as base-e log",
            "Natural log as base-e log: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "自然对数连接e底对数",
            "自然对数连接e底对数: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "自然對數連接e底對數",
            "自然對數連接e底對數: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Logarithme naturel de base e",
            "Logarithme naturel de base e: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Натуральный логарифм по основанию e", "Натуральный логарифм по основанию e: x in R+, both sides well-defined => ln(x)=log(e,x)")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Logaritmo natural en base e",
            "Logaritmo natural en base e: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اللوغاريتم الطبيعي ذو الأساس e",
            "اللوغاريتم الطبيعي ذو الأساس e: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "自然対数と底eの対数",
            "自然対数と底eの対数: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "자연로그와 밑e 로그",
            "자연로그와 밑e 로그: x in R+, both sides well-defined => ln(x)=log(e,x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Logarit tự nhiên cơ số e",
            "Logarit tự nhiên cơ số e: x in R+, both sides well-defined => ln(x)=log(e,x)",
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

impl ExpAsEulerPowerProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Exponential as Euler power",
            "Exponential as Euler power: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "指数连接e底幂",
            "指数连接e底幂: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "指數連接e底冪",
            "指數連接e底冪: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Exponentielle comme puissance de e", "Exponentielle comme puissance de e: x in R, both sides well-defined => exp(x)=e^x")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Экспонента как степень e",
            "Экспонента как степень e: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Exponencial como potencia de e",
            "Exponencial como potencia de e: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الأس كقوة للعدد e",
            "الأس كقوة للعدد e: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "指数関数とeのべき",
            "指数関数とeのべき: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "지수함수와 e의 거듭제곱",
            "지수함수와 e의 거듭제곱: x in R, both sides well-defined => exp(x)=e^x",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hàm mũ và lũy thừa của e",
            "Hàm mũ và lũy thừa của e: x in R, both sides well-defined => exp(x)=e^x",
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
