use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::finite_sum_triangle::FiniteSetSumTriangleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Finite sum triangle inequality", "The absolute value of a finite real sum is bounded by the sum of the same pointwise absolute values.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("有限和三角不等式", "有限实数和的绝对值不超过同一逐项绝对值的和。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("有限和三角不等式", "有限實數和的絕對值不超過同一逐項絕對值的和。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Inégalité triangulaire d’une somme finie", "La valeur absolue d’une somme réelle finie est majorée par la somme des valeurs absolues de ses termes.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Неравенство треугольника для конечной суммы", "Модуль конечной вещественной суммы не превосходит суммы модулей тех же слагаемых.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Desigualdad triangular de una suma finita", "El valor absoluto de una suma real finita no supera la suma de los valores absolutos de sus términos.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("متباينة المثلث للمجموع المنتهي", "القيمة المطلقة لمجموع حقيقي منته لا تتجاوز مجموع القيم المطلقة لحدوده نفسها.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("有限和の三角不等式", "有限実数和の絶対値は、同じ各項の絶対値の和以下です。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("유한 합의 삼각 부등식", "유한 실수 합의 절댓값은 같은 각 항의 절댓값의 합 이하입니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Bất đẳng thức tam giác cho tổng hữu hạn", "Giá trị tuyệt đối của tổng thực hữu hạn không vượt quá tổng các giá trị tuyệt đối của cùng các số hạng.") }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText { match lang {
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
    }}
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::finite_index_union::FiniteIndexUnionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Finite indexed union", "The checked finite index set and the cited universal finiteness certificate for its fibres make the indexed union finite.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("有限索引并集", "已检索引集有限，并引用逐项有限的全称证书，推出索引并集有限。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("有限索引聯集", "已檢索引集有限，並引用逐項有限的全稱證書，推出索引聯集有限。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Union indexée finie", "L’ensemble d’indices fini vérifié et le certificat universel cité de finitude des fibres rendent l’union indexée finie.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Конечное индексированное объединение", "Проверенная конечность множества индексов и цитируемый универсальный сертификат конечности слоёв дают конечность объединения.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Unión indexada finita", "El conjunto de índices finito verificado y el certificado universal citado de finitud de las fibras hacen finita la unión.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("اتحاد مفهرس منته", "مجموعة الفهارس المنتهية المثبتة والشهادة الكلية المستشهد بها لانتهاء كل ليف تجعل الاتحاد المفهرس منتهيا.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("有限な添字付き和集合", "検証済みの有限添字集合と、各集合が有限であることの引用済み全称証明により、和集合は有限です。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("유한 지표 합집합", "검증된 유한 지표 집합과 각 집합의 유한성을 나타내는 인용된 전칭 증명으로 합집합의 유한성을 증명합니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Hợp có chỉ số hữu hạn", "Tập chỉ số hữu hạn đã kiểm chứng cùng chứng chỉ phổ quát được trích dẫn về tính hữu hạn của từng tập con chứng minh hợp hữu hạn.") }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText { match lang {
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
    }}
}
