use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_set_product_reindex::FiniteSetProductReindexProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Finite product reindexing", "A checked bijection reindexes the finite product with the same pulled-back factors.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("有限乘积换指标", "已验证的双射重新编号有限乘积，保留逐项复合函数。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("有限乘積換指標", "已驗證的雙射重新編號有限乘積，保留逐項複合函數。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Réindexation du produit fini", "Une bijection vérifiée réindexe le produit fini en conservant les facteurs composés.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Замена индексов конечного произведения", "Проверенная биекция меняет индексы конечного произведения, сохраняя композицию факторов.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Reindexación del producto finito", "Una biyección verificada reindexa el producto finito conservando los factores compuestos.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("إعادة فهرسة الجداء المنتهي", "تقابل مثبت يعيد فهرسة الجداء المنتهي مع الحفاظ على عوامل الدالة المركبة.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("有限積の添字変換", "検証済みの全単射で有限積の添字を変換し、合成された各因子を保ちます。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("유한 곱의 지표 변환", "검증된 전단사로 유한 곱의 지표를 바꾸고 합성된 각 인자를 유지합니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Đổi chỉ số tích hữu hạn", "Song ánh đã kiểm chứng đổi chỉ số của tích hữu hạn và giữ nguyên các thừa số hợp thành.") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_set_reduce_reindex::FiniteSetReduceReindexProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Finite fold reindexing", "A checked bijection reindexes the associative commutative finite fold, preserving its operation and seed.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("有限归约换指标", "已验证的双射重排满足结合律与交换律的有限归约，保留运算及初始值。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("有限歸約換指標", "已驗證的雙射重排滿足結合律與交換律的有限歸約，保留運算及初始值。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Réindexation du pli fini", "Une bijection vérifiée réindexe le pli fini associatif et commutatif en conservant opération et valeur initiale.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Замена индексов конечной свёртки", "Проверенная биекция меняет индексы ассоциативной коммутативной свёртки, сохраняя операцию и начальное значение.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Reindexación de la reducción finita", "Una biyección verificada reindexa la reducción finita asociativa y conmutativa, preservando la operación y el valor inicial.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("إعادة فهرسة الاختزال المنتهي", "تقابل مثبت يعيد فهرسة الاختزال التجميعي والتبادلي المنتهي ويحفظ العملية والقيمة الابتدائية.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("有限畳み込みの添字変換", "検証済みの全単射で結合則と交換則を満たす有限畳み込みの添字を変換し、演算と初期値を保ちます。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("유한 접기의 지표 변환", "검증된 전단사로 결합법칙과 교환법칙을 만족하는 유한 접기의 지표를 바꾸며 연산과 초기값을 유지합니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Đổi chỉ số phép gộp hữu hạn", "Song ánh đã kiểm chứng đổi chỉ số phép gộp hữu hạn kết hợp và giao hoán, giữ nguyên phép toán và giá trị đầu.") }
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
