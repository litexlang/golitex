use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::rounding_order::FloorMonotoneProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Floor weak monotonicity","Floor weak monotonicity: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("向下取整保持弱序","向下取整保持弱序: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("向下取整保持弱序","向下取整保持弱序: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Monotonie de la partie entière inférieure","Monotonie de la partie entière inférieure: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Монотонность округления вниз","Монотонность округления вниз: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Monotonía del suelo","Monotonía del suelo: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("رتابة التقريب لأسفل","رتابة التقريب لأسفل: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("床関数の単調性","床関数の単調性: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("바닥 함수의 단조성","바닥 함수의 단조성: x,y in R; x<=y => floor(x)<=floor(y)") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Tính đơn điệu của hàm sàn","Tính đơn điệu của hàm sàn: x,y in R; x<=y => floor(x)<=floor(y)") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::rounding_order::CeilMonotoneProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Ceiling weak monotonicity","Ceiling weak monotonicity: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("向上取整保持弱序","向上取整保持弱序: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("向上取整保持弱序","向上取整保持弱序: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Monotonie de la partie entière supérieure","Monotonie de la partie entière supérieure: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Монотонность округления вверх","Монотонность округления вверх: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Monotonía del techo","Monotonía del techo: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("رتابة التقريب لأعلى","رتابة التقريب لأعلى: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("天井関数の単調性","天井関数の単調性: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("천장 함수의 단조성","천장 함수의 단조성: x,y in R; x<=y => ceil(x)<=ceil(y)") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Tính đơn điệu của hàm trần","Tính đơn điệu của hàm trần: x,y in R; x<=y => ceil(x)<=ceil(y)") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::complex_triangle::ComplexTriangleProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Complex triangle inequality","Complex triangle inequality: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("复数模三角不等式","复数模三角不等式: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("複數模三角不等式","複數模三角不等式: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Inégalité triangulaire complexe","Inégalité triangulaire complexe: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Комплексное неравенство треугольника","Комплексное неравенство треугольника: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Desigualdad triangular compleja","Desigualdad triangular compleja: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("متباينة المثلث المركبة","متباينة المثلث المركبة: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("複素数の三角不等式","複素数の三角不等式: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("복소수 삼각 부등식","복소수 삼각 부등식: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Bất đẳng thức tam giác phức","Bất đẳng thức tam giác phức: z,w in C => C_abs(z+w)<=C_abs(z)+C_abs(w)") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::complex_triangle::ComplexReverseTriangleProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Complex reverse triangle inequality","Complex reverse triangle inequality: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("复数模反三角不等式","复数模反三角不等式: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("複數模反三角不等式","複數模反三角不等式: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Inégalité triangulaire inverse complexe","Inégalité triangulaire inverse complexe: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Обратное комплексное неравенство треугольника","Обратное комплексное неравенство треугольника: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Desigualdad triangular inversa compleja","Desigualdad triangular inversa compleja: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("متباينة المثلث العكسية المركبة","متباينة المثلث العكسية المركبة: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("複素数の逆三角不等式","複素数の逆三角不等式: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("복소수 역삼각 부등식","복소수 역삼각 부등식: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Bất đẳng thức tam giác ngược phức","Bất đẳng thức tam giác ngược phức: z,w in C => abs(C_abs(z)-C_abs(w))<=C_abs(z-w)") }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::lcm_order::LcmCommonMultipleBoundProof {
    pub fn rule_name_and_message_en(&self)->BuiltinRuleText { text("Positive common multiple bounds lcm","Positive common multiple bounds lcm: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_zh(&self)->BuiltinRuleText { text("正公共倍数给出lcm上界","正公共倍数给出lcm上界: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_zh_hant(&self)->BuiltinRuleText { text("正公倍數給出lcm上界","正公倍數給出lcm上界: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_fr(&self)->BuiltinRuleText { text("Un multiple commun positif borne le ppcm","Un multiple commun positif borne le ppcm: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_ru(&self)->BuiltinRuleText { text("Положительное общее кратное ограничивает НОК","Положительное общее кратное ограничивает НОК: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_es(&self)->BuiltinRuleText { text("Un múltiplo común positivo acota el mcm","Un múltiplo común positivo acota el mcm: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_ar(&self)->BuiltinRuleText { text("المضاعف المشترك الموجب يحد المضاعف الأصغر","المضاعف المشترك الموجب يحد المضاعف الأصغر: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_ja(&self)->BuiltinRuleText { text("正の公倍数による最小公倍数の上界","正の公倍数による最小公倍数の上界: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_ko(&self)->BuiltinRuleText { text("양의 공배수로 최소공배수의 상한","양의 공배수로 최소공배수의 상한: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
    pub fn rule_name_and_message_vi(&self)->BuiltinRuleText { text("Bội chung dương chặn bội chung nhỏ nhất","Bội chung dương chặn bội chung nhỏ nhất: a,b in Z*; m in N+; m%abs(a)=m%abs(b)=0 => lcm(a,b)<=m") }
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
