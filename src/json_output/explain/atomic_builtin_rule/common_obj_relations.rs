use crate::json_output::explain::text::text;
use crate::json_output::explain::BuiltinRuleText;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_interval_order::SinPositiveOnOpenPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Sine is positive on (0,pi)", "Sine is positive on (0,pi): 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("正弦在 (0,pi) 为正", "正弦在 (0,pi) 为正: 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("正弦在 (0,pi) 為正", "正弦在 (0,pi) 為正: 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Sinus positif sur (0,pi)", "Sinus positif sur (0,pi): 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Синус положителен на (0,pi)", "Синус положителен на (0,pi): 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Seno positivo en (0,pi)", "Seno positivo en (0,pi): 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("الجيب موجب على (0,pi)", "الجيب موجب على (0,pi): 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("(0,pi) で正弦は正", "(0,pi) で正弦は正: 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("(0,pi)에서 사인은 양수", "(0,pi)에서 사인은 양수: 0<x<pi => 0<sin(x)") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Sin dương trên (0,pi)", "Sin dương trên (0,pi): 0<x<pi => 0<sin(x)") }
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_interval_order::SinStrictMonotoneOnHalfPiProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Sine is strictly increasing on its principal interval", "Sine is strictly increasing on its principal interval: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("正弦在主区间严格递增", "正弦在主区间严格递增: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("正弦在主區間嚴格遞增", "正弦在主區間嚴格遞增: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Sinus strictement croissant sur son intervalle principal", "Sinus strictement croissant sur son intervalle principal: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Синус строго возрастает на главном интервале", "Синус строго возрастает на главном интервале: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Seno estrictamente creciente en su intervalo principal", "Seno estrictamente creciente en su intervalo principal: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("الجيب متزايد تمامًا على مجاله الرئيسي", "الجيب متزايد تمامًا على مجاله الرئيسي: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("主区間で正弦は狭義単調増加", "主区間で正弦は狭義単調増加: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("주구간에서 사인은 엄격히 증가", "주구간에서 사인은 엄격히 증가: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Sin tăng nghiêm ngặt trên khoảng chính", "Sin tăng nghiêm ngặt trên khoảng chính: -pi/2<=a<b<=pi/2 => sin(a)<sin(b)") }
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::common_relation_nonzero::LcmNonzeroFromNonzeroOperandsProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Lcm of nonzero integers is nonzero", "Lcm of nonzero integers is nonzero: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("非零整数的 lcm 非零", "非零整数的 lcm 非零: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("非零整數的 lcm 非零", "非零整數的 lcm 非零: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Le ppcm d’entiers non nuls est non nul", "Le ppcm d’entiers non nuls est non nul: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("НОК ненулевых целых чисел ненулевой", "НОК ненулевых целых чисел ненулевой: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("El MCM de enteros no nulos es no nulo", "El MCM de enteros no nulos es no nulo: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("المضاعف الأصغر لعددين صحيحين غير صفريين غير صفري", "المضاعف الأصغر لعددين صحيحين غير صفريين غير صفري: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("非零整数の最小公倍数は非零", "非零整数の最小公倍数は非零: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("영이 아닌 정수의 최소공배수는 영이 아님", "영이 아닌 정수의 최소공배수는 영이 아님: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Bội chung nhỏ nhất của các số nguyên khác không cũng khác không", "Bội chung nhỏ nhất của các số nguyên khác không cũng khác không: a,b in Z; a!=0; b!=0 => lcm(a,b)!=0") }
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::common_relation_nonzero::LogNonzeroFromNonunitArgumentProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Logarithm is nonzero away from argument one", "Logarithm is nonzero away from argument one: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("真数不为 1 时对数非零", "真数不为 1 时对数非零: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("真數不為 1 時對數非零", "真數不為 1 時對數非零: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Logarithme non nul si l’argument diffère de un", "Logarithme non nul si l’argument diffère de un: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Логарифм ненулевой при аргументе не равном единице", "Логарифм ненулевой при аргументе не равном единице: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Logaritmo no nulo con argumento distinto de uno", "Logaritmo no nulo con argumento distinto de uno: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("اللوغاريتم غير صفري عندما تختلف الحجة عن واحد", "اللوغاريتم غير صفري عندما تختلف الحجة عن واحد: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("真数が一でなければ対数は非零", "真数が一でなければ対数は非零: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("진수가 일이 아니면 로그는 영이 아님", "진수가 일이 아니면 로그는 영이 아님: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Logarit khác không khi đối số khác một", "Logarit khác không khi đối số khác một: b>0; b!=1; x>0; x!=1 => log(b,x)!=0") }
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::common_relation_nonzero::PositiveNonunitIntegerPowerProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText { text("Nonzero integer power of a positive nonunit is nonunit", "Nonzero integer power of a positive nonunit is nonunit: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText { text("正非单位底数的非零整数幂不为 1", "正非单位底数的非零整数幂不为 1: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText { text("正非單位底數的非零整數冪不為 1", "正非單位底數的非零整數冪不為 1: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText { text("Puissance entière non nulle d’une base positive différente de un", "Puissance entière non nulle d’une base positive différente de un: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText { text("Ненулевая целая степень положительного числа не равного единице", "Ненулевая целая степень положительного числа не равного единице: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText { text("Potencia entera no nula de una base positiva distinta de uno", "Potencia entera no nula de una base positiva distinta de uno: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText { text("قوة صحيحة غير صفرية لأساس موجب مختلف عن واحد", "قوة صحيحة غير صفرية لأساس موجب مختلف عن واحد: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText { text("一以外の正の底の非零整数乗は一ではない", "一以外の正の底の非零整数乗は一ではない: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText { text("일이 아닌 양수의 영이 아닌 정수 거듭제곱은 일이 아님", "일이 아닌 양수의 영이 아닌 정수 거듭제곱은 일이 아님: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText { text("Lũy thừa nguyên khác không của cơ số dương khác một khác một", "Lũy thừa nguyên khác không của cơ số dương khác một khác một: b>0; b!=1; n in Z; n!=0 => b^n!=1") }
}
