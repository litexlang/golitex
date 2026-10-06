use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_additional_interval_order::{CosPositiveOnOpenHalfPiProof, SinNegativeOnOpenNegativePiProof, TanNegativeOnOpenNegativeHalfPiProof, CotNegativeOnOpenUpperHalfPiProof, SinPositiveOnFirstQuadrantProof, CosPositiveOnFirstQuadrantProof, CosStrictDecreasingOnClosedPiProof, TanStrictIncreasingOnOpenHalfPiProof, CotStrictDecreasingOnOpenPiProof, SinWeakIncreasingOnClosedHalfPiProof, CosWeakDecreasingOnClosedPiProof, TanWeakIncreasingOnOpenHalfPiProof, CotWeakDecreasingOnOpenPiProof};
use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl CosPositiveOnOpenHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi/2 < x < pi/2 => 0 < cos(x)",
            "The trigonometric law on the stated interval gives: -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi/2 < x < pi/2 => 0 < cos(x)",
            "在所述区间上，三角函数性质给出：-pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi/2 < x < pi/2 => 0 < cos(x)",
            "在所述區間上，三角函數性質給出：-pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi/2 < x < pi/2 => 0 < cos(x)",
            "La propriété trigonométrique sur cet intervalle donne : -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi/2 < x < pi/2 => 0 < cos(x)",
            "Тригонометрическое свойство на указанном интервале даёт: -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi/2 < x < pi/2 => 0 < cos(x)",
            "La propiedad trigonométrica en este intervalo da: -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi/2 < x < pi/2 => 0 < cos(x)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi/2 < x < pi/2 => 0 < cos(x)",
            "指定された区間の三角関数の性質から、次が得られる：-pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi/2 < x < pi/2 => 0 < cos(x)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi/2 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi/2 < x < pi/2 => 0 < cos(x)",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi/2 < x < pi/2 => 0 < cos(x)",
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

impl SinNegativeOnOpenNegativePiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi < x < 0 => sin(x) < 0",
            "The trigonometric law on the stated interval gives: -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi < x < 0 => sin(x) < 0",
            "在所述区间上，三角函数性质给出：-pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi < x < 0 => sin(x) < 0",
            "在所述區間上，三角函數性質給出：-pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi < x < 0 => sin(x) < 0",
            "La propriété trigonométrique sur cet intervalle donne : -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi < x < 0 => sin(x) < 0",
            "Тригонометрическое свойство на указанном интервале даёт: -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi < x < 0 => sin(x) < 0",
            "La propiedad trigonométrica en este intervalo da: -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi < x < 0 => sin(x) < 0",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi < x < 0 => sin(x) < 0",
            "指定された区間の三角関数の性質から、次が得られる：-pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi < x < 0 => sin(x) < 0",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi < x < 0 => sin(x) < 0",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi < x < 0 => sin(x) < 0",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi < x < 0 => sin(x) < 0",
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

impl TanNegativeOnOpenNegativeHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi/2 < x < 0 => tan(x) < 0",
            "The trigonometric law on the stated interval gives: -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi/2 < x < 0 => tan(x) < 0",
            "在所述区间上，三角函数性质给出：-pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi/2 < x < 0 => tan(x) < 0",
            "在所述區間上，三角函數性質給出：-pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi/2 < x < 0 => tan(x) < 0",
            "La propriété trigonométrique sur cet intervalle donne : -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi/2 < x < 0 => tan(x) < 0",
            "Тригонометрическое свойство на указанном интервале даёт: -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi/2 < x < 0 => tan(x) < 0",
            "La propiedad trigonométrica en este intervalo da: -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi/2 < x < 0 => tan(x) < 0",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi/2 < x < 0 => tan(x) < 0",
            "指定された区間の三角関数の性質から、次が得られる：-pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi/2 < x < 0 => tan(x) < 0",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi/2 < x < 0 => tan(x) < 0",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi/2 < x < 0 => tan(x) < 0",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi/2 < x < 0 => tan(x) < 0",
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

impl CotNegativeOnOpenUpperHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: pi/2 < x < pi => cot(x) < 0",
            "The trigonometric law on the stated interval gives: pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: pi/2 < x < pi => cot(x) < 0",
            "在所述区间上，三角函数性质给出：pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: pi/2 < x < pi => cot(x) < 0",
            "在所述區間上，三角函數性質給出：pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: pi/2 < x < pi => cot(x) < 0",
            "La propriété trigonométrique sur cet intervalle donne : pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: pi/2 < x < pi => cot(x) < 0",
            "Тригонометрическое свойство на указанном интервале даёт: pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: pi/2 < x < pi => cot(x) < 0",
            "La propiedad trigonométrica en este intervalo da: pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: pi/2 < x < pi => cot(x) < 0",
            "تعطي الخاصية المثلثية على الفترة المذكورة: pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: pi/2 < x < pi => cot(x) < 0",
            "指定された区間の三角関数の性質から、次が得られる：pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: pi/2 < x < pi => cot(x) < 0",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: pi/2 < x < pi => cot(x) < 0",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: pi/2 < x < pi => cot(x) < 0",
            "Tính chất lượng giác trên khoảng đã nêu cho: pi/2 < x < pi => cot(x) < 0",
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

impl SinPositiveOnFirstQuadrantProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 < x < pi/2 => 0 < sin(x)",
            "The trigonometric law on the stated interval gives: 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 < x < pi/2 => 0 < sin(x)",
            "在所述区间上，三角函数性质给出：0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 < x < pi/2 => 0 < sin(x)",
            "在所述區間上，三角函數性質給出：0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 < x < pi/2 => 0 < sin(x)",
            "La propriété trigonométrique sur cet intervalle donne : 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 < x < pi/2 => 0 < sin(x)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 < x < pi/2 => 0 < sin(x)",
            "La propiedad trigonométrica en este intervalo da: 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 < x < pi/2 => 0 < sin(x)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 < x < pi/2 => 0 < sin(x)",
            "指定された区間の三角関数の性質から、次が得られる：0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 < x < pi/2 => 0 < sin(x)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 < x < pi/2 => 0 < sin(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 < x < pi/2 => 0 < sin(x)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 < x < pi/2 => 0 < sin(x)",
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

impl CosPositiveOnFirstQuadrantProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 < x < pi/2 => 0 < cos(x)",
            "The trigonometric law on the stated interval gives: 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 < x < pi/2 => 0 < cos(x)",
            "在所述区间上，三角函数性质给出：0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 < x < pi/2 => 0 < cos(x)",
            "在所述區間上，三角函數性質給出：0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 < x < pi/2 => 0 < cos(x)",
            "La propriété trigonométrique sur cet intervalle donne : 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 < x < pi/2 => 0 < cos(x)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 < x < pi/2 => 0 < cos(x)",
            "La propiedad trigonométrica en este intervalo da: 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 < x < pi/2 => 0 < cos(x)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 < x < pi/2 => 0 < cos(x)",
            "指定された区間の三角関数の性質から、次が得られる：0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 < x < pi/2 => 0 < cos(x)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 < x < pi/2 => 0 < cos(x)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 < x < pi/2 => 0 < cos(x)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 < x < pi/2 => 0 < cos(x)",
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

impl CosStrictDecreasingOnClosedPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 <= a < b <= pi => cos(b) < cos(a)",
            "The trigonometric law on the stated interval gives: 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 <= a < b <= pi => cos(b) < cos(a)",
            "在所述区间上，三角函数性质给出：0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 <= a < b <= pi => cos(b) < cos(a)",
            "在所述區間上，三角函數性質給出：0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 <= a < b <= pi => cos(b) < cos(a)",
            "La propriété trigonométrique sur cet intervalle donne : 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 <= a < b <= pi => cos(b) < cos(a)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 <= a < b <= pi => cos(b) < cos(a)",
            "La propiedad trigonométrica en este intervalo da: 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 <= a < b <= pi => cos(b) < cos(a)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 <= a < b <= pi => cos(b) < cos(a)",
            "指定された区間の三角関数の性質から、次が得られる：0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 <= a < b <= pi => cos(b) < cos(a)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 <= a < b <= pi => cos(b) < cos(a)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 <= a < b <= pi => cos(b) < cos(a)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 <= a < b <= pi => cos(b) < cos(a)",
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

impl TanStrictIncreasingOnOpenHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "The trigonometric law on the stated interval gives: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "在所述区间上，三角函数性质给出：-pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "在所述區間上，三角函數性質給出：-pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "La propriété trigonométrique sur cet intervalle donne : -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "Тригонометрическое свойство на указанном интервале даёт: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "La propiedad trigonométrica en este intervalo da: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "指定された区間の三角関数の性質から、次が得られる：-pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi/2 < a < b < pi/2 => tan(a) < tan(b)",
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

impl CotStrictDecreasingOnOpenPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 < a < b < pi => cot(b) < cot(a)",
            "The trigonometric law on the stated interval gives: 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 < a < b < pi => cot(b) < cot(a)",
            "在所述区间上，三角函数性质给出：0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 < a < b < pi => cot(b) < cot(a)",
            "在所述區間上，三角函數性質給出：0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 < a < b < pi => cot(b) < cot(a)",
            "La propriété trigonométrique sur cet intervalle donne : 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 < a < b < pi => cot(b) < cot(a)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 < a < b < pi => cot(b) < cot(a)",
            "La propiedad trigonométrica en este intervalo da: 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 < a < b < pi => cot(b) < cot(a)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 < a < b < pi => cot(b) < cot(a)",
            "指定された区間の三角関数の性質から、次が得られる：0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 < a < b < pi => cot(b) < cot(a)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 < a < b < pi => cot(b) < cot(a)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 < a < b < pi => cot(b) < cot(a)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 < a < b < pi => cot(b) < cot(a)",
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

impl SinWeakIncreasingOnClosedHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "The trigonometric law on the stated interval gives: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "在所述区间上，三角函数性质给出：-pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "在所述區間上，三角函數性質給出：-pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "La propriété trigonométrique sur cet intervalle donne : -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "Тригонометрическое свойство на указанном интервале даёт: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "La propiedad trigonométrica en este intervalo da: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "指定された区間の三角関数の性質から、次が得られる：-pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b)",
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

impl CosWeakDecreasingOnClosedPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "The trigonometric law on the stated interval gives: 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "在所述区间上，三角函数性质给出：0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "在所述區間上，三角函數性質給出：0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "La propriété trigonométrique sur cet intervalle donne : 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "La propiedad trigonométrica en este intervalo da: 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "指定された区間の三角関数の性質から、次が得られる：0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 <= a <= b <= pi => cos(b) <= cos(a)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 <= a <= b <= pi => cos(b) <= cos(a)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 <= a <= b <= pi => cos(b) <= cos(a)",
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

impl TanWeakIncreasingOnOpenHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "The trigonometric law on the stated interval gives: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "在所述区间上，三角函数性质给出：-pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "在所述區間上，三角函數性質給出：-pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "La propriété trigonométrique sur cet intervalle donne : -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "Тригонометрическое свойство на указанном интервале даёт: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "La propiedad trigonométrica en este intervalo da: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "指定された区間の三角関数の性質から、次が得られる：-pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
            "Tính chất lượng giác trên khoảng đã nêu cho: -pi/2 < a <= b < pi/2 => tan(a) <= tan(b)",
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

impl CotWeakDecreasingOnOpenPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Trigonometric interval law: 0 < a <= b < pi => cot(b) <= cot(a)",
            "The trigonometric law on the stated interval gives: 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "三角函数区间规律: 0 < a <= b < pi => cot(b) <= cot(a)",
            "在所述区间上，三角函数性质给出：0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "三角函數區間規律: 0 < a <= b < pi => cot(b) <= cot(a)",
            "在所述區間上，三角函數性質給出：0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi trigonométrique sur un intervalle: 0 < a <= b < pi => cot(b) <= cot(a)",
            "La propriété trigonométrique sur cet intervalle donne : 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Тригонометрический закон на интервале: 0 < a <= b < pi => cot(b) <= cot(a)",
            "Тригонометрическое свойство на указанном интервале даёт: 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley trigonométrica en un intervalo: 0 < a <= b < pi => cot(b) <= cot(a)",
            "La propiedad trigonométrica en este intervalo da: 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون مثلثي على فترة: 0 < a <= b < pi => cot(b) <= cot(a)",
            "تعطي الخاصية المثلثية على الفترة المذكورة: 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "三角関数の区間法則: 0 < a <= b < pi => cot(b) <= cot(a)",
            "指定された区間の三角関数の性質から、次が得られる：0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "삼각함수 구간 법칙: 0 < a <= b < pi => cot(b) <= cot(a)",
            "주어진 구간의 삼각함수 성질로 다음을 얻습니다: 0 < a <= b < pi => cot(b) <= cot(a)",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quy luật lượng giác trên khoảng: 0 < a <= b < pi => cot(b) <= cot(a)",
            "Tính chất lượng giác trên khoảng đã nêu cho: 0 < a <= b < pi => cot(b) <= cot(a)",
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
