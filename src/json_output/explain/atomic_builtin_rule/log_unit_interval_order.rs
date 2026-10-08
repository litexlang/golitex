use crate::json_output::explain::{BuiltinRuleText, text::text};
use crate::launch_command::OutputLanguage;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::log_unit_interval_order::{LogStrictDecreasingProof, LogWeakDecreasingProof};

impl LogStrictDecreasingProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Logarithm strictly decreases below base one", "Logarithm strictly decreases below base one: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("小于1底数的对数严格反单调", "小于1底数的对数严格反单调: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("小於1底數的對數嚴格反單調", "小於1底數的對數嚴格反單調: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme strictement décroissant de base inférieure à un", "Logarithme strictement décroissant de base inférieure à un: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Строгое убывание логарифма при основании меньше единицы", "Строгое убывание логарифма при основании меньше единицы: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo estrictamente decreciente con base menor que uno", "Logaritmo estrictamente decreciente con base menor que uno: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("تناقص اللوغاريتم الصارم للأساس الأصغر من واحد", "تناقص اللوغاريتم الصارم للأساس الأصغر من واحد: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("底が1未満の対数の狭義単調減少", "底が1未満の対数の狭義単調減少: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑이 1보다 작은 로그의 엄격한 단조 감소", "밑이 1보다 작은 로그의 엄격한 단조 감소: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit giảm nghiêm ngặt khi cơ số nhỏ hơn một", "Logarit giảm nghiêm ngặt khi cơ số nhỏ hơn một: 0<a<1, 0<x, 0<y, x<y, both logs well-defined => log(a,y)<log(a,x)")
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

impl LogWeakDecreasingProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Logarithm weakly decreases below base one", "Logarithm weakly decreases below base one: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("小于1底数的对数弱反单调", "小于1底数的对数弱反单调: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("小於1底數的對數弱反單調", "小於1底數的對數弱反單調: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme décroissant au sens large de base inférieure à un", "Logarithme décroissant au sens large de base inférieure à un: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Нестрогое убывание логарифма при основании меньше единицы", "Нестрогое убывание логарифма при основании меньше единицы: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo débilmente decreciente con base menor que uno", "Logaritmo débilmente decreciente con base menor que uno: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("تناقص اللوغاريتم غير الصارم للأساس الأصغر من واحد", "تناقص اللوغاريتم غير الصارم للأساس الأصغر من واحد: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("底が1未満の対数の広義単調減少", "底が1未満の対数の広義単調減少: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑이 1보다 작은 로그의 약한 단조 감소", "밑이 1보다 작은 로그의 약한 단조 감소: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit không tăng khi cơ số nhỏ hơn một", "Logarit không tăng khi cơ số nhỏ hơn một: 0<a<1, 0<x, 0<y, x<=y, both logs well-defined => log(a,y)<=log(a,x)")
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
