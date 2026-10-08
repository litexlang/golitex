use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::launch_command::OutputLanguage;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::factorial_order::{FactorialMonotoneProof, FactorialStrictMonotoneProof};

impl FactorialMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Factorial weak monotonicity",
            "Factorial weak monotonicity: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "阶乘弱保序",
            "阶乘弱保序: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "階乘弱保序",
            "階乘弱保序: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie faible de la factorielle",
            "Monotonie faible de la factorielle: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогая монотонность факториала",
            "Нестрогая монотонность факториала: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía débil del factorial",
            "Monotonía débil del factorial: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الرتابة غير الصارمة للمضروب",
            "الرتابة غير الصارمة للمضروب: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "階乗の広義単調性",
            "階乗の広義単調性: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "팩토리얼의 비엄격 단조성",
            "팩토리얼의 비엄격 단조성: m,n in N, m<=n => factorial(m)<=factorial(n)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính đơn điệu không nghiêm ngặt của giai thừa", "Tính đơn điệu không nghiêm ngặt của giai thừa: m,n in N, m<=n => factorial(m)<=factorial(n)")
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

impl FactorialStrictMonotoneProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Factorial strict monotonicity",
            "Factorial strict monotonicity: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "阶乘严格保序",
            "阶乘严格保序: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "階乘嚴格保序",
            "階乘嚴格保序: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Monotonie stricte de la factorielle", "Monotonie stricte de la factorielle: m in N+, n in N, m<n => factorial(m)<factorial(n)")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Строгая монотонность факториала",
            "Строгая монотонность факториала: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía estricta del factorial",
            "Monotonía estricta del factorial: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الرتابة الصارمة للمضروب",
            "الرتابة الصارمة للمضروب: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "階乗の狭義単調性",
            "階乗の狭義単調性: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "팩토리얼의 엄격 단조성",
            "팩토리얼의 엄격 단조성: m in N+, n in N, m<n => factorial(m)<factorial(n)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính đơn điệu nghiêm ngặt của giai thừa", "Tính đơn điệu nghiêm ngặt của giai thừa: m in N+, n in N, m<n => factorial(m)<factorial(n)")
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
