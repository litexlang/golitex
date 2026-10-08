use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_range_size::RangeSizeProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Ordered half-open range cardinality","Ordered half-open range cardinality: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("有序半开区间基数","有序半开区间基数: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("有序半開區間基數","有序半開區間基數: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Cardinal d’un intervalle semi-ouvert","Cardinal d’un intervalle semi-ouvert: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Мощность полуоткрытого интервала","Мощность полуоткрытого интервала: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Cardinal de intervalo semiabierto","Cardinal de intervalo semiabierto: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("عدد عناصر فترة نصف مفتوحة","عدد عناصر فترة نصف مفتوحة: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("半開区間の濃度","半開区間の濃度: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("반열린 구간의 크기","반열린 구간의 크기: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Lực lượng khoảng nửa mở","Lực lượng khoảng nửa mở: a,b in N; a<=b => |range(a,b)|=b-a") }
    pub fn rule_name_and_message(&self,lang:OutputLanguage)->BuiltinRuleText { match lang {
        OutputLanguage::English=>self.rule_name_and_message_en(),
        OutputLanguage::Chinese=>self.rule_name_and_message_zh(),
        OutputLanguage::ChineseTraditional=>self.rule_name_and_message_zh_hant(),
        OutputLanguage::French=>self.rule_name_and_message_fr(),
        OutputLanguage::Russian=>self.rule_name_and_message_ru(),
        OutputLanguage::Spanish=>self.rule_name_and_message_es(),
        OutputLanguage::Arabic=>self.rule_name_and_message_ar(),
        OutputLanguage::Japanese=>self.rule_name_and_message_ja(),
        OutputLanguage::Korean=>self.rule_name_and_message_ko(),
        OutputLanguage::Vietnamese=>self.rule_name_and_message_vi(),
    }}
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_range_size::ClosedRangeSizeProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Ordered closed range cardinality","Ordered closed range cardinality: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("有序闭区间基数","有序闭区间基数: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("有序閉區間基數","有序閉區間基數: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Cardinal d’un intervalle fermé","Cardinal d’un intervalle fermé: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Мощность замкнутого интервала","Мощность замкнутого интервала: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Cardinal de intervalo cerrado","Cardinal de intervalo cerrado: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("عدد عناصر فترة مغلقة","عدد عناصر فترة مغلقة: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("閉区間の濃度","閉区間の濃度: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("닫힌 구간의 크기","닫힌 구간의 크기: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Lực lượng khoảng đóng","Lực lượng khoảng đóng: a,b in N; a<=b => |closed_range(a,b)|=b-a+1") }
    pub fn rule_name_and_message(&self,lang:OutputLanguage)->BuiltinRuleText { match lang {
        OutputLanguage::English=>self.rule_name_and_message_en(),
        OutputLanguage::Chinese=>self.rule_name_and_message_zh(),
        OutputLanguage::ChineseTraditional=>self.rule_name_and_message_zh_hant(),
        OutputLanguage::French=>self.rule_name_and_message_fr(),
        OutputLanguage::Russian=>self.rule_name_and_message_ru(),
        OutputLanguage::Spanish=>self.rule_name_and_message_es(),
        OutputLanguage::Arabic=>self.rule_name_and_message_ar(),
        OutputLanguage::Japanese=>self.rule_name_and_message_ja(),
        OutputLanguage::Korean=>self.rule_name_and_message_ko(),
        OutputLanguage::Vietnamese=>self.rule_name_and_message_vi(),
    }}
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_euclidean_remainder::EuclideanRemainderProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Unique bounded remainder","Unique bounded remainder: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("有界余数唯一性","有界余数唯一性: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("有界餘數唯一性","有界餘數唯一性: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Unicité du reste borné","Unicité du reste borné: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Единственность ограниченного остатка","Единственность ограниченного остатка: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Unicidad del resto acotado","Unicidad del resto acotado: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("وحدانية الباقي المحدود","وحدانية الباقي المحدود: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("有界剰余の一意性","有界剰余の一意性: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("유계 나머지의 유일성","유계 나머지의 유일성: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Tính duy nhất của số dư bị chặn","Tính duy nhất của số dư bị chặn: a=m*q+r; a,q in Z; m in N+; r in N; r<m => a%m=r") }
    pub fn rule_name_and_message(&self,lang:OutputLanguage)->BuiltinRuleText { match lang {
        OutputLanguage::English=>self.rule_name_and_message_en(),
        OutputLanguage::Chinese=>self.rule_name_and_message_zh(),
        OutputLanguage::ChineseTraditional=>self.rule_name_and_message_zh_hant(),
        OutputLanguage::French=>self.rule_name_and_message_fr(),
        OutputLanguage::Russian=>self.rule_name_and_message_ru(),
        OutputLanguage::Spanish=>self.rule_name_and_message_es(),
        OutputLanguage::Arabic=>self.rule_name_and_message_ar(),
        OutputLanguage::Japanese=>self.rule_name_and_message_ja(),
        OutputLanguage::Korean=>self.rule_name_and_message_ko(),
        OutputLanguage::Vietnamese=>self.rule_name_and_message_vi(),
    }}
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_factorial_divisibility::FactorialDivisibilityProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Factorial divisibility","Factorial divisibility: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("阶乘整除","阶乘整除: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("階乘整除","階乘整除: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Divisibilité des factorielles","Divisibilité des factorielles: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Делимость факториалов","Делимость факториалов: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Divisibilidad de factoriales","Divisibilidad de factoriales: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("قسمة المضروبات","قسمة المضروبات: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("階乗の整除","階乗の整除: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("계승의 나눗셈","계승의 나눗셈: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Tính chia hết của giai thừa","Tính chia hết của giai thừa: m,n in N; m<=n => factorial(n)%factorial(m)=0") }
    pub fn rule_name_and_message(&self,lang:OutputLanguage)->BuiltinRuleText { match lang {
        OutputLanguage::English=>self.rule_name_and_message_en(),
        OutputLanguage::Chinese=>self.rule_name_and_message_zh(),
        OutputLanguage::ChineseTraditional=>self.rule_name_and_message_zh_hant(),
        OutputLanguage::French=>self.rule_name_and_message_fr(),
        OutputLanguage::Russian=>self.rule_name_and_message_ru(),
        OutputLanguage::Spanish=>self.rule_name_and_message_es(),
        OutputLanguage::Arabic=>self.rule_name_and_message_ar(),
        OutputLanguage::Japanese=>self.rule_name_and_message_ja(),
        OutputLanguage::Korean=>self.rule_name_and_message_ko(),
        OutputLanguage::Vietnamese=>self.rule_name_and_message_vi(),
    }}
}
