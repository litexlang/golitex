use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::launch_command::OutputLanguage;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave5::{LcmLeftAbsDivisibilityProof, LcmRightAbsDivisibilityProof};

impl LcmLeftAbsDivisibilityProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Left absolute input divides lcm", "Left absolute input divides lcm: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("左输入绝对值整除lcm", "左输入绝对值整除lcm: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("左輸入絕對值整除lcm", "左輸入絕對值整除lcm: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Divisibilité du PPCM par la valeur absolue gauche", "Divisibilité du PPCM par la valeur absolue gauche: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Делимость НОК на модуль левого аргумента", "Делимость НОК на модуль левого аргумента: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Divisibilidad del mcm por el valor absoluto izquierdo", "Divisibilidad del mcm por el valor absoluto izquierdo: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("قسمة المضاعف المشترك الأصغر على القيمة المطلقة للمعامل الأيسر", "قسمة المضاعف المشترك الأصغر على القيمة المطلقة للمعامل الأيسر: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("最小公倍数の左引数の絶対値による整除", "最小公倍数の左引数の絶対値による整除: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("최소공배수의 왼쪽 인자 절댓값에 대한 가분성", "최소공배수의 왼쪽 인자 절댓값에 대한 가분성: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Bội chung nhỏ nhất chia hết cho trị tuyệt đối của đối số trái", "Bội chung nhỏ nhất chia hết cho trị tuyệt đối của đối số trái: a,b in Z, abs(a)!=0 => lcm(a,b)%abs(a)=0") }
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

impl LcmRightAbsDivisibilityProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Right absolute input divides lcm", "Right absolute input divides lcm: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("右输入绝对值整除lcm", "右输入绝对值整除lcm: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("右輸入絕對值整除lcm", "右輸入絕對值整除lcm: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Divisibilité du PPCM par la valeur absolue droite", "Divisibilité du PPCM par la valeur absolue droite: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Делимость НОК на модуль правого аргумента", "Делимость НОК на модуль правого аргумента: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Divisibilidad del mcm por el valor absoluto derecho", "Divisibilidad del mcm por el valor absoluto derecho: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("قسمة المضاعف المشترك الأصغر على القيمة المطلقة للمعامل الأيمن", "قسمة المضاعف المشترك الأصغر على القيمة المطلقة للمعامل الأيمن: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("最小公倍数の右引数の絶対値による整除", "最小公倍数の右引数の絶対値による整除: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("최소공배수의 오른쪽 인자 절댓값에 대한 가분성", "최소공배수의 오른쪽 인자 절댓값에 대한 가분성: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Bội chung nhỏ nhất chia hết cho trị tuyệt đối của đối số phải", "Bội chung nhỏ nhất chia hết cho trị tuyệt đối của đối số phải: a,b in Z, abs(b)!=0 => lcm(a,b)%abs(b)=0") }
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
