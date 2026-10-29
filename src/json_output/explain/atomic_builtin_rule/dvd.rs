use super::super::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::dvd::DvdFactSearchProofByBuiltinRule;

impl DvdFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::Add(_) => crate::json_output::explain::text::text("Divisibility of a sum", "If d divides a and b, it divides a+b."),
            Self::Subtract(_) => crate::json_output::explain::text::text("Divisibility of a difference", "If d divides a and b, it divides a−b."),
            Self::Scale(_) => crate::json_output::explain::text::text("Divisibility of an integer multiple", "If d divides a and k is an integer, d divides k·a."),
            Self::LinearCombination(_) => crate::json_output::explain::text::text("Divisibility of a linear combination", "If d divides a and b, it divides u·a+v·b for all integers u,v."),
            Self::Zero(_) => crate::json_output::explain::text::text("Every nonzero integer divides zero", "For every nonzero integer d, 0=d·0, so d divides 0."),
            Self::One(_) => crate::json_output::explain::text::text("One divides every integer", "For any integer a, a=1·a, so 1 divides a. For example, $dvd(6, 1)."),
            Self::SelfDivisor(_) => crate::json_output::explain::text::text("A nonzero integer divides itself", "For nonzero integer a, a=a·1, so a divides itself."),
            Self::ProductFactor(_) => crate::json_output::explain::text::text("A factor divides its product", "For integers a,k with a≠0, a divides a·k."),
            Self::GcdArgument(_) => crate::json_output::explain::text::text("Greatest common divisor divides its inputs", "The nonzero greatest common divisor gcd(a,b) divides each of the integers a and b."),
            Self::LcmArgument(_) => crate::json_output::explain::text::text("Inputs divide their least common multiple", "For nonzero integers a,b, |a| and |b| each divide lcm(a,b)."),
            Self::DividendMinusRemainder(_) => crate::json_output::explain::text::text("Subtract the remainder", "For integers a,d with d≠0, a−(a mod d) is an integer multiple of d."),
            Self::GcdCommonDivisor(_) => crate::json_output::explain::text::text("A common divisor divides the greatest common divisor", "A positive integer d dividing a and b also divides gcd(a,b)."),
            Self::LcmCommonMultiple(_) => crate::json_output::explain::text::text("Least common multiple divides every common multiple", "For positive integers a,b, every common multiple m of a and b is divisible by lcm(a,b)."),
            Self::Factorial(_) => crate::json_output::explain::text::text("Divisibility of factorials", "For natural numbers m≤n, m! divides n!, since the remaining factors have an integer product."),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::Add(_) => crate::json_output::explain::text::text(
                "整除的加法封闭性",
                "若 d 整除 a 与 b，则 d 整除 a+b。",
            ),
            Self::Subtract(_) => crate::json_output::explain::text::text(
                "整除的减法封闭性",
                "若 d 整除 a 与 b，则 d 整除 a−b。",
            ),
            Self::Scale(_) => crate::json_output::explain::text::text(
                "整除保持整数倍",
                "若 d 整除 a，k 为整数，则 d 整除 k·a。",
            ),
            Self::LinearCombination(_) => crate::json_output::explain::text::text(
                "整除整数线性组合",
                "若 d 整除 a 与 b，则对任意整数 u、v，d 整除 u·a+v·b。",
            ),
            Self::Zero(_) => crate::json_output::explain::text::text(
                "非零整数整除零",
                "对任意非零整数 d，0=d·0，因此 d 整除 0。",
            ),
            Self::One(_) => crate::json_output::explain::text::text(
                "一整除任意整数",
                "对任意整数 a，a=1·a，因此 1 整除 a。例如 $dvd(6, 1)。",
            ),
            Self::SelfDivisor(_) => crate::json_output::explain::text::text(
                "非零整数整除自身",
                "对非零整数 a，a=a·1，因此 a 整除自身。",
            ),
            Self::ProductFactor(_) => crate::json_output::explain::text::text(
                "因子整除乘积",
                "对整数 a、k 且 a≠0，a 整除 a·k。",
            ),
            Self::GcdArgument(_) => crate::json_output::explain::text::text(
                "最大公约数整除两个参数",
                "非零最大公约数 gcd(a,b) 整除整数 a、b 中的每一个。",
            ),
            Self::LcmArgument(_) => crate::json_output::explain::text::text(
                "两个参数整除最小公倍数",
                "对非零整数 a、b，|a| 与 |b| 分别整除 lcm(a,b)。",
            ),
            Self::DividendMinusRemainder(_) => crate::json_output::explain::text::text(
                "被除数减去余数",
                "对整数 a、d 且 d≠0，a−(a mod d) 是 d 的整数倍。",
            ),
            Self::GcdCommonDivisor(_) => crate::json_output::explain::text::text(
                "公约数整除最大公约数",
                "正整数 d 若同时整除 a 与 b，则 d 整除 gcd(a,b)。",
            ),
            Self::LcmCommonMultiple(_) => crate::json_output::explain::text::text(
                "最小公倍数整除公倍数",
                "对正整数 a、b，它们的任意公倍数 m 都被 lcm(a,b) 整除。",
            ),
            Self::Factorial(_) => crate::json_output::explain::text::text(
                "阶乘的整除关系",
                "对自然数 m≤n，m! 整除 n!，因为剩余因子的乘积为整数。",
            ),
        }
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("整除性: {}", self.rule_id()),
            message: format!("已檢查整數整除性質及其定義域條件。 {}", self.law()),
        }
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Divisibilité: {}", self.rule_id()),
            message: format!(
                "Propriété de divisibilité entière vérifiée avec ses conditions de domaine. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Делимость: {}", self.rule_id()),
            message: format!(
                "Проверено свойство целочисленной делимости и условия области определения. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Divisibilidad: {}", self.rule_id()),
            message: format!(
                "Propiedad de divisibilidad entera comprobada con sus condiciones de dominio. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("القابلية للقسمة: {}", self.rule_id()),
            message: format!(
                "تم التحقق من خاصية قسمة الأعداد الصحيحة وشروط مجالها. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("整除性質: {}", self.rule_id()),
            message: format!("整数の整除性と定義域の条件を検証しました。 {}", self.law()),
        }
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("나눗셈 관계: {}", self.rule_id()),
            message: format!(
                "정수의 나눗셈 관계와 정의역 조건을 검증했습니다. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Tính chia hết: {}", self.rule_id()),
            message: format!(
                "Đã kiểm tra tính chia hết của số nguyên và các điều kiện miền xác định. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message(&self, language: OutputLanguage) -> BuiltinRuleText {
        match language {
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
    pub fn cite_fact_id(&self) -> Option<FactId> {
        None
    }
}
