use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_gcd_lcm_universal_divisibility::GcdCommonDivisorProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Common divisor divides gcd", "Common divisor divides gcd: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("公约数整除 gcd", "公约数整除 gcd: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("公約數整除 gcd", "公約數整除 gcd: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Un diviseur commun divise le pgcd", "Un diviseur commun divise le pgcd: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Общий делитель делит НОД", "Общий делитель делит НОД: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Un divisor común divide el MCD", "Un divisor común divide el MCD: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("القاسم المشترك يقسم القاسم الأكبر", "القاسم المشترك يقسم القاسم الأكبر: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("公約数は最大公約数を割り切る", "公約数は最大公約数を割り切る: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("공약수는 최대공약수를 나눔", "공약수는 최대공약수를 나눔: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Ước chung chia hết ước chung lớn nhất", "Ước chung chia hết ước chung lớn nhất: d in N+; a%d=0; b%d=0 => gcd(a,b)%d=0") }
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_gcd_lcm_universal_divisibility::LcmCommonMultipleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Lcm divides common multiples", "Lcm divides common multiples: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("lcm 整除公倍数", "lcm 整除公倍数: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("lcm 整除公倍數", "lcm 整除公倍數: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Le ppcm divise les multiples communs", "Le ppcm divise les multiples communs: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("НОК делит общие кратные", "НОК делит общие кратные: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("El MCM divide los múltiplos comunes", "El MCM divide los múltiplos comunes: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("المضاعف الأصغر يقسم المضاعفات المشتركة", "المضاعف الأصغر يقسم المضاعفات المشتركة: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("最小公倍数は公倍数を割り切る", "最小公倍数は公倍数を割り切る: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("최소공배수는 공배수를 나눔", "최소공배수는 공배수를 나눔: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Bội chung chia hết cho bội chung nhỏ nhất", "Bội chung chia hết cho bội chung nhỏ nhất: a,b in N+; m%a=0; m%b=0 => m%lcm(a,b)=0") }
}
