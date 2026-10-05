use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::FiniteSetSumDisjointUnionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Split a finite sum over a disjoint union", "The two checked disjoint finite parts partition the domain, with certified agreement of each restricted callback.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("不交并的有限和拆分", "已验证两个有限部分构成不交并，并保留各限制函数的一致性证据。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("不交聯集的有限和分拆", "已驗證兩個有限部分構成不交聯集，並保留各限制函數的一致性證據。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Somme finie sur une union disjointe", "Les deux parties finies disjointes vérifiées partitionnent le domaine, avec un certificat d’accord de chaque fonction restreinte.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Разбиение конечной суммы по непересекающемуся объединению", "Проверенные непересекающиеся конечные части разбивают область; согласованность каждой ограниченной функции подтверждена.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Suma finita sobre una unión disjunta", "Las dos partes finitas disjuntas verificadas forman el dominio, con un certificado de coincidencia para cada función restringida.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("تفكيك مجموع منته على اتحاد متباين", "الجزآن المنتهيان المتباينان المثبتان يقسمان المجال، مع شهادة توافق كل دالة مقيدة.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("互いに素な和集合上の有限和の分割", "検証済みの互いに素な有限部分が定義域を分割し、各制限関数の一致の証拠を保ちます。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("서로소 합집합의 유한 합 분할", "검증된 서로소 유한 부분들이 정의역을 분할하며 각 제한 함수의 일치 증거를 유지합니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Tách tổng hữu hạn trên hợp rời nhau", "Hai phần hữu hạn rời nhau đã kiểm chứng phân hoạch miền, giữ chứng chỉ trùng khớp của từng hàm hạn chế.") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::FiniteSetProductDisjointUnionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Split a finite product over a disjoint union", "The two checked disjoint finite parts partition the domain, with certified agreement of each restricted callback.") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("不交并的有限乘积拆分", "已验证两个有限部分构成不交并，并保留各限制函数的一致性证据。") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("不交聯集的有限乘積分拆", "已驗證兩個有限部分構成不交聯集，並保留各限制函數的一致性證據。") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Produit fini sur une union disjointe", "Les deux parties finies disjointes vérifiées partitionnent le domaine, avec un certificat d’accord de chaque fonction restreinte.") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Разбиение конечного произведения по непересекающемуся объединению", "Проверенные непересекающиеся конечные части разбивают область; согласованность каждой ограниченной функции подтверждена.") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Producto finito sobre una unión disjunta", "Las dos partes finitas disjuntas verificadas forman el dominio, con un certificado de coincidencia para cada función restringida.") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("تفكيك جداء منته على اتحاد متباين", "الجزآن المنتهيان المتباينان المثبتان يقسمان المجال، مع شهادة توافق كل دالة مقيدة.") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("互いに素な和集合上の有限積の分割", "検証済みの互いに素な有限部分が定義域を分割し、各制限関数の一致の証拠を保ちます。") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("서로소 합집합의 유한 곱 분할", "검증된 서로소 유한 부분들이 정의역을 분할하며 각 제한 함수의 일치 증거를 유지합니다.") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Tách tích hữu hạn trên hợp rời nhau", "Hai phần hữu hạn rời nhau đã kiểm chứng phân hoạch miền, giữ chứng chỉ trùng khớp của từng hàm hạn chế.") }
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
