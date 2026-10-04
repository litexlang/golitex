//! Leaf explain for atomic family group `in_fact`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
    AddInNaturalBuiltinRuleProof,
    CartMembershipBuiltinRuleProof,
    ClosedNumericMembershipBuiltinRuleProof,
    ComplexArithmeticClosureBuiltinRuleProof,
    ComplexCoordinateInComplexBuiltinRuleProof,
    ComplexCoordinateInRealBuiltinRuleProof,
    FamilyUnionMembershipFromMemberBuiltinRuleProof,
    FiniteSetSubsetMembershipBuiltinRuleProof,
    AnonymousFnApplicationInFnRangeBuiltinRuleProof,
    InFactSearchProofByBuiltinRule,
    IndexUnionMembershipFromIndexBuiltinRuleProof,
    IntersectMembershipBuiltinRuleProof,
    IntervalMembershipBuiltinRuleProof,
    ListSetElementMembershipBuiltinRuleProof,
    MulInNaturalBuiltinRuleProof,
    NativeConstantMembershipBuiltinRuleProof,
    NativeScalarCodomainBuiltinRuleProof,
    FiniteSetMaxMemberBuiltinRuleProof,
    FiniteSetMinMemberBuiltinRuleProof,
    PositiveIntegerInNPosBuiltinRuleProof,
    CartDimInNaturalBuiltinRuleProof,
    TupleDimInNaturalBuiltinRuleProof,
    AnonymousFnInDeclaredFnSetBuiltinRuleProof,
    OneSideInfinityIntervalMembershipBuiltinRuleProof,
    PowerSetMembershipBuiltinRuleProof,
    PredecessorInNaturalBuiltinRuleProof,
    PredecessorFromPositiveNaturalBuiltinRuleProof,
    PredecessorFromNaturalAboveZeroBuiltinRuleProof,
    RealArithmeticClosureBuiltinRuleProof,
    RealTrigClosureBuiltinRuleProof,
    RealTrigInComplexBuiltinRuleProof,
    SetBuilderMembershipBuiltinRuleProof,
    SetMinusMembershipBuiltinRuleProof,
    StandardSetSubsetMembershipBuiltinRuleProof,
    StructObjMembershipBuiltinRuleProof,
    UnionMembershipFromLeftBuiltinRuleProof,
    UnionMembershipFromRightBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl InFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericMembership(p) => p.rule_id_and_message(lang),
            Self::ComplexArithmeticClosure(p) => p.rule_id_and_message(lang),
            Self::RealTrigClosure(p) => p.rule_id_and_message(lang),
            Self::RealTrigInComplex(p) => p.rule_id_and_message(lang),
            Self::ComplexCoordinateInReal(p) => p.rule_id_and_message(lang),
            Self::ComplexCoordinateInComplex(p) => p.rule_id_and_message(lang),
            Self::RealArithmeticClosure(p) => p.rule_id_and_message(lang),
            Self::RealOperandArithmeticClosure(_) => match lang {
                OutputLanguage::English => text("RealOperandArithmeticClosure", "Real arithmetic from checked operands", "Checked real operands remain real under field arithmetic; division also has its checked WD domain"),
                OutputLanguage::ChineseTraditional => text("RealOperandArithmeticClosure", "由已檢查運算元得實數運算", "經檢查的實數在體運算下仍為實數；除法亦有已檢查的良定域"),
                OutputLanguage::French => text("RealOperandArithmeticClosure", "Arithmétique réelle depuis les opérandes vérifiés", "Les opérandes réels vérifiés restent réels sous les opérations de corps ; la division a aussi son domaine vérifié"),
                OutputLanguage::Russian => text("RealOperandArithmeticClosure", "Вещественная арифметика из проверенных операндов", "Проверенные вещественные остаются вещественными при операциях поля; область корректности деления также проверена"),
                OutputLanguage::Spanish => text("RealOperandArithmeticClosure", "Aritmética real desde operandos comprobados", "Los reales comprobados siguen siendo reales bajo operaciones de cuerpo; la división tiene también su dominio comprobado"),
                OutputLanguage::Arabic => text("RealOperandArithmeticClosure", "حساب حقيقي من معاملات متحقق منها", "المعاملات الحقيقية المتحقق منها تبقى حقيقية تحت عمليات الحقل؛ وللقسمة مجال حسن تعريف متحقق منه"),
                OutputLanguage::Japanese => text("RealOperandArithmeticClosure", "検査済みの被演算子から実数演算", "検査済みの実数は体演算でも実数であり、除算の定義域も検査済みです"),
                OutputLanguage::Korean => text("RealOperandArithmeticClosure", "검사된 피연산자로 실수 산술", "검사된 실수는 체 연산에서 실수로 유지되며 나눗셈의 정의 영역도 검사됩니다"),
                OutputLanguage::Vietnamese => text("RealOperandArithmeticClosure", "Số học thực từ toán hạng đã kiểm tra", "Các toán hạng thực đã kiểm tra vẫn thực qua phép toán trường; phép chia cũng có miền xác định tốt đã kiểm tra"),

                OutputLanguage::Chinese => text("RealOperandArithmeticClosure", "由实数操作数得实数运算结果", "已验证的实数操作数经四则运算仍为实数；除法另有已验证的定义域条件"),
            },
            Self::RealIntegerPower(_) => match lang {
                OutputLanguage::English => text("RealIntegerPower", "Real integer power", "The base is checked real and the enclosing power WD certificate establishes an integer exponent and required nonzero domain"),
                OutputLanguage::ChineseTraditional => text("RealIntegerPower", "實數整數次方", "底數已驗證為實數，冪的良定證書確立整數指數與所需非零域"),
                OutputLanguage::French => text("RealIntegerPower", "Puissance entière réelle", "La base est vérifiée réelle et le certificat de bonne définition de puissance établit l'exposant entier et le domaine non nul requis"),
                OutputLanguage::Russian => text("RealIntegerPower", "Вещественная целая степень", "Основание проверено как вещественное, а сертификат корректности степени устанавливает целый показатель и необходимую ненулевую область"),
                OutputLanguage::Spanish => text("RealIntegerPower", "Potencia entera real", "La base está comprobada real y el certificado de buena definición de potencia establece exponente entero y dominio no nulo requerido"),
                OutputLanguage::Arabic => text("RealIntegerPower", "قوة صحيحة حقيقية", "تم التحقق من أن الأساس حقيقي وشهادة حسن تعريف القوة تثبت الأس الصحيح والمجال غير الصفري المطلوب"),
                OutputLanguage::Japanese => text("RealIntegerPower", "実数の整数乗", "底は実数と検査済みで、冪の定義の証明書が整数指数と必要な非ゼロ領域を確立します"),
                OutputLanguage::Korean => text("RealIntegerPower", "실수의 정수 거듭제곱", "밑은 실수로 검사되었으며 거듭제곱 정의 인증서가 정수 지수와 필요한 비영 영역을 확립합니다"),
                OutputLanguage::Vietnamese => text("RealIntegerPower", "Lũy thừa nguyên của số thực", "Cơ số đã kiểm tra là thực và chứng nhận xác định tốt của lũy thừa xác lập số mũ nguyên và miền khác không cần thiết"),

                OutputLanguage::Chinese => text("RealIntegerPower", "实数的整数幂", "底数已验证为实数；幂的定义良好证据验证整数指数及所需非零条件"),
            },
            Self::ClosedExactScalarMembership(_) => match lang {
                OutputLanguage::English => text("ClosedExactScalarMembership", "Exact scalar membership", "Exact real and imaginary coordinates satisfy the target scalar carrier"),
                OutputLanguage::ChineseTraditional => text("ClosedExactScalarMembership", "精確純量成員關係", "精確實部與虛部符合目標純量載體"),
                OutputLanguage::French => text("ClosedExactScalarMembership", "Appartenance scalaire exacte", "Les coordonnées réelles et imaginaires exactes satisfont l'ensemble porteur scalaire cible"),
                OutputLanguage::Russian => text("ClosedExactScalarMembership", "Точная скалярная принадлежность", "Точные действительные и мнимые координаты удовлетворяют целевому скалярному носителю"),
                OutputLanguage::Spanish => text("ClosedExactScalarMembership", "Pertenencia escalar exacta", "Las coordenadas reales e imaginarias exactas satisfacen el portador escalar objetivo"),
                OutputLanguage::Arabic => text("ClosedExactScalarMembership", "انتماء قياسي دقيق", "الإحداثيان الحقيقي والتخيلي الدقيقان يحققان المجموعة الحاملة القياسية الهدف"),
                OutputLanguage::Japanese => text("ClosedExactScalarMembership", "正確なスカラー所属", "正確な実部と虚部は対象スカラー台集合を満たします"),
                OutputLanguage::Korean => text("ClosedExactScalarMembership", "정확한 스칼라 소속", "정확한 실수부와 허수부 좌표는 대상 스칼라 바탕 집합을 만족합니다"),
                OutputLanguage::Vietnamese => text("ClosedExactScalarMembership", "Thuộc về vô hướng chính xác", "Tọa độ thực và ảo chính xác thỏa tập nền vô hướng mục tiêu"),

                OutputLanguage::Chinese => text("ClosedExactScalarMembership", "精确数值载体", "精确的实部和虚部满足目标数值集合的条件"),
            },
            Self::IntegerArithmeticClosure(_) => match lang {
                OutputLanguage::English => text("IntegerArithmeticClosure", "Integer arithmetic closure", "Checked integer operands remain integers under negation, absolute value, addition, subtraction, multiplication and natural powers"),
                OutputLanguage::ChineseTraditional => text("IntegerArithmeticClosure", "整數運算封閉", "經檢查的整數在取負、絕對值、加減乘及自然數次方下仍為整數"),
                OutputLanguage::French => text("IntegerArithmeticClosure", "Clôture arithmétique entière", "Les opérandes entiers vérifiés restent entiers sous opposé, valeur absolue, addition, soustraction, multiplication et puissances naturelles"),
                OutputLanguage::Russian => text("IntegerArithmeticClosure", "Замкнутость целочисленной арифметики", "Проверенные целые остаются целыми при отрицании, модуле, сложении, вычитании, умножении и натуральных степенях"),
                OutputLanguage::Spanish => text("IntegerArithmeticClosure", "Clausura aritmética entera", "Los enteros comprobados siguen siendo enteros bajo negación, valor absoluto, suma, resta, multiplicación y potencias naturales"),
                OutputLanguage::Arabic => text("IntegerArithmeticClosure", "انغلاق الحساب الصحيح", "المعاملات الصحيحة المتحقق منها تبقى صحيحة تحت السالب والقيمة المطلقة والجمع والطرح والضرب والقوى الطبيعية"),
                OutputLanguage::Japanese => text("IntegerArithmeticClosure", "整数演算の閉性", "検査済みの整数は符号反転、絶対値、加減乗算、自然数乗でも整数です"),
                OutputLanguage::Korean => text("IntegerArithmeticClosure", "정수 산술 닫힘", "검사된 정수는 부호 반전, 절댓값, 덧셈, 뺄셈, 곱셈 및 자연수 거듭제곱에서 정수로 유지됩니다"),
                OutputLanguage::Vietnamese => text("IntegerArithmeticClosure", "Đóng của số học nguyên", "Các toán hạng nguyên đã kiểm tra vẫn nguyên qua đổi dấu, trị tuyệt đối, cộng, trừ, nhân và lũy thừa tự nhiên"),

                OutputLanguage::Chinese => text("IntegerArithmeticClosure", "整数运算封闭", "已验证的整数操作数经取负、绝对值、加减乘及自然数幂仍为整数"),
            },
            Self::FiniteSetMaxMember(p) => p.rule_id_and_message(lang),
            Self::FiniteSetMinMember(p) => p.rule_id_and_message(lang),
            Self::NativeScalarCodomain(p) => p.rule_id_and_message(lang),
            Self::PositiveIntegerInNPos(p) => p.rule_id_and_message(lang),
            Self::FoldScalarCodomain(_) => match lang {
                OutputLanguage::English => text("FoldScalarCodomain", "Fold carrier", "The checked homogeneous operation and seed preserve the fold carrier"),
                OutputLanguage::ChineseTraditional => text("FoldScalarCodomain", "折疊載體", "已檢查的同質運算與初值保持折疊載體"),
                OutputLanguage::French => text("FoldScalarCodomain", "Ensemble porteur du pli", "L'opération homogène et la valeur initiale vérifiées préservent l'ensemble porteur du pli"),
                OutputLanguage::Russian => text("FoldScalarCodomain", "Носитель свёртки", "Проверенная однородная операция и начальное значение сохраняют носитель свёртки"),
                OutputLanguage::Spanish => text("FoldScalarCodomain", "Portador del pliegue", "La operación homogénea y semilla comprobadas conservan el portador del pliegue"),
                OutputLanguage::Arabic => text("FoldScalarCodomain", "مجموعة حاملة للطي", "العملية المتجانسة والقيمة الابتدائية المتحقق منهما تحفظان المجموعة الحاملة للطي"),
                OutputLanguage::Japanese => text("FoldScalarCodomain", "畳み込みの台集合", "検査済みの同型演算と初期値は畳み込みの台集合を保ちます"),
                OutputLanguage::Korean => text("FoldScalarCodomain", "접기 바탕 집합", "검사된 동종 연산과 초깃값은 접기의 바탕 집합을 보존합니다"),
                OutputLanguage::Vietnamese => text("FoldScalarCodomain", "Tập nền phép gấp", "Phép toán đồng nhất và giá trị khởi tạo đã kiểm tra bảo toàn tập nền của phép gấp"),

                OutputLanguage::Chinese => text("FoldScalarCodomain", "Fold 的载体", "已验证的齐次运算与初值保持 fold 的载体"),
            },
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = match lang {
                    OutputLanguage::English => ("Finite aggregate scalar carrier", "Checked summands or factors close the declared scalar carrier; empty sums include zero"),
                    OutputLanguage::ChineseTraditional => ("有限聚合純量載體", "已檢查的加數或因子保持宣告的純量載體封閉；空和包含零"),
                    OutputLanguage::French => ("Ensemble porteur scalaire d'agrégat fini", "Les termes ou facteurs vérifiés ferment l'ensemble porteur scalaire déclaré ; les sommes vides incluent zéro"),
                    OutputLanguage::Russian => ("Скалярный носитель конечного агрегата", "Проверенные слагаемые или множители сохраняют объявленный скалярный носитель; пустые суммы включают ноль"),
                    OutputLanguage::Spanish => ("Portador escalar de agregado finito", "Los sumandos o factores comprobados mantienen cerrado el portador escalar declarado; las sumas vacías incluyen cero"),
                    OutputLanguage::Arabic => ("مجموعة حاملة قياسية لتجميع منتهٍ", "الحدود أو العوامل المتحقق منها تحفظ المجموعة الحاملة القياسية المعلنة؛ والمجاميع الخالية تتضمن صفرًا"),
                    OutputLanguage::Japanese => ("有限集約のスカラー台集合", "検査済みの加数または因子は宣言されたスカラー台集合を保ち、空和はゼロを含みます"),
                    OutputLanguage::Korean => ("유한 집계 스칼라 바탕 집합", "검사된 항 또는 인자는 선언된 스칼라 바탕 집합을 유지하며 빈 합은 0을 포함합니다"),
                    OutputLanguage::Vietnamese => ("Tập nền vô hướng tổng hợp hữu hạn", "Các số hạng hoặc thừa số đã kiểm tra giữ tập nền vô hướng đã khai báo đóng; tổng rỗng gồm không"),

                    OutputLanguage::Chinese => ("有限聚合的数值载体", "合法求和项或因子在声明的数值载体内封闭；空求和须包含零"),
                };
                BuiltinRuleText { rule_id: "AggregateScalarCodomain", rule_name:name.into(), message:message.into() }
            },
            Self::CartDimInNatural(p) => p.rule_id_and_message(lang),
            Self::TupleDimInNatural(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnApplicationScalarCodomain(_) => match lang {
                OutputLanguage::English => text("AnonymousFnApplicationScalarCodomain", "Anonymous function return carrier", "A checked direct application inhabits its declared static scalar codomain"),
                OutputLanguage::ChineseTraditional => text("AnonymousFnApplicationScalarCodomain", "匿名函數返回載體", "經檢查的直接函數套用屬於宣告的靜態純量陪域"),
                OutputLanguage::French => text("AnonymousFnApplicationScalarCodomain", "Ensemble porteur du retour de fonction anonyme", "Une application directe vérifiée appartient à son codomaine scalaire statique déclaré"),
                OutputLanguage::Russian => text("AnonymousFnApplicationScalarCodomain", "Носитель возврата анонимной функции", "Проверенное прямое применение принадлежит объявленной статической скалярной области значений"),
                OutputLanguage::Spanish => text("AnonymousFnApplicationScalarCodomain", "Portador de retorno de función anónima", "Una aplicación directa comprobada pertenece a su codominio escalar estático declarado"),
                OutputLanguage::Arabic => text("AnonymousFnApplicationScalarCodomain", "مجموعة حاملة لإرجاع دالة مجهولة", "تطبيق مباشر متحقق منه ينتمي إلى مجاله المقابل القياسي الساكن المعلن"),
                OutputLanguage::Japanese => text("AnonymousFnApplicationScalarCodomain", "無名関数の戻り値の台集合", "検査済みの直接適用は宣言された静的スカラー終域に属します"),
                OutputLanguage::Korean => text("AnonymousFnApplicationScalarCodomain", "익명 함수 반환 바탕 집합", "검사된 직접 적용은 선언된 정적 스칼라 공역에 속합니다"),
                OutputLanguage::Vietnamese => text("AnonymousFnApplicationScalarCodomain", "Tập nền trả về của hàm ẩn danh", "Áp dụng trực tiếp đã kiểm tra thuộc đối miền vô hướng tĩnh đã khai báo"),

                OutputLanguage::Chinese => text("AnonymousFnApplicationScalarCodomain", "匿名函数的返回载体", "已验证的直接调用属于其声明的静态数值返回载体"),
            },
            Self::StandardSetSubsetMembership(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSubsetMembership(p) => p.rule_id_and_message(lang),
            Self::SetBuilderMembership(p) => p.rule_id_and_message(lang),
            Self::NativeConstantMembership(p) => p.rule_id_and_message(lang),
            Self::ListSetElementMembership(p) => p.rule_id_and_message(lang),
            Self::CartMembership(p) => p.rule_id_and_message(lang),
            Self::PowerSetMembership(p) => p.rule_id_and_message(lang),
            Self::StructObjMembership(p) => p.rule_id_and_message(lang),
            Self::PredecessorInNatural(p) => p.rule_id_and_message(lang),
            Self::PredecessorFromPositiveNatural(p) => p.rule_id_and_message(lang),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_id_and_message(lang),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_id_and_message(lang),
            Self::UnionMembershipFromLeft(p) => p.rule_id_and_message(lang),
            Self::UnionMembershipFromRight(p) => p.rule_id_and_message(lang),
            Self::IntersectMembership(p) => p.rule_id_and_message(lang),
            Self::SetMinusMembership(p) => p.rule_id_and_message(lang),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_id_and_message(lang),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_id_and_message(lang),
            Self::IntervalMembership(p) => p.rule_id_and_message(lang),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_id_and_message(lang),
            Self::AddInNatural(p) => p.rule_id_and_message(lang),
            Self::MulInNatural(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedNumericMembership(_) => None,
            Self::ComplexArithmeticClosure(_) => None,
            Self::RealTrigClosure(_) => None,
            Self::RealTrigInComplex(_) => None,
            Self::ComplexCoordinateInReal(_) => None,
            Self::ComplexCoordinateInComplex(_) => None,
            Self::RealArithmeticClosure(_) => None,
            Self::RealOperandArithmeticClosure(_) => None,
            Self::RealIntegerPower(_) => None,
            Self::ClosedExactScalarMembership(_) => None,
            Self::IntegerArithmeticClosure(_) => None,
            Self::FiniteSetMaxMember(_) | Self::FiniteSetMinMember(_) => None,
            Self::NativeScalarCodomain(_) => None,
            Self::PositiveIntegerInNPos(_) => None,
            Self::AggregateScalarCodomain(_) => None,
            Self::FoldScalarCodomain(_) => None,
            Self::CartDimInNatural(_) => None,
            Self::TupleDimInNatural(_) => None,
            Self::AnonymousFnInDeclaredFnSet(_) => None,
            Self::AnonymousFnApplicationScalarCodomain(_) => None,
            Self::StandardSetSubsetMembership(_) => None,
            Self::FiniteSetSubsetMembership(_) => None,
            Self::SetBuilderMembership(_) => None,
            Self::NativeConstantMembership(_) => None,
            Self::ListSetElementMembership(_) => None,
            Self::CartMembership(_) => None,
            Self::PowerSetMembership(_) => None,
            Self::StructObjMembership(_) => None,
            Self::PredecessorInNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromPositiveNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromNaturalAboveZero(p) => p.in_natural_proof.cite_fact_id(),
            Self::AnonymousFnApplicationInFnRange(_) => None,
            Self::UnionMembershipFromLeft(_) => None,
            Self::UnionMembershipFromRight(_) => None,
            Self::IntersectMembership(_) => None,
            Self::SetMinusMembership(_) => None,
            Self::FamilyUnionMembershipFromMember(p) => Some(p.cite_member_set_in_family_fact_id),
            Self::IndexUnionMembershipFromIndex(p) => Some(p.cite_index_in_index_set_fact_id),
            Self::IntervalMembership(_) => None,
            Self::OneSideInfinityIntervalMembership(_) => None,
            Self::AddInNatural(_) => None,
            Self::MulInNatural(_) => None,
        }
    }
}

impl ClosedNumericMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericMembership",
            "Closed Numeric Membership",
            "a closed expression that evaluates to a normalized",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericMembership",
            "封闭数值成员",
            "封闭表达式算出的值属于目标集合",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedNumericMembership",
                "封閉數值成員",
                "封閉運算式求出的值屬於目標集合",
            ),
            OutputLanguage::French => text(
                "ClosedNumericMembership",
                "Appartenance numérique fermée",
                "La valeur évaluée d'une expression fermée appartient à l'ensemble cible",
            ),
            OutputLanguage::Russian => text(
                "ClosedNumericMembership",
                "Принадлежность замкнутого числового выражения",
                "Вычисленное значение замкнутого выражения принадлежит целевому множеству",
            ),
            OutputLanguage::Spanish => text(
                "ClosedNumericMembership",
                "Pertenencia numérica cerrada",
                "El valor evaluado de una expresión cerrada pertenece al conjunto objetivo",
            ),
            OutputLanguage::Arabic => text(
                "ClosedNumericMembership",
                "انتماء عددي مغلق",
                "قيمة التعبير المغلق المحسوبة تنتمي إلى المجموعة الهدف",
            ),
            OutputLanguage::Japanese => text(
                "ClosedNumericMembership",
                "閉じた数値式の所属",
                "閉じた式の評価値は対象集合に属します",
            ),
            OutputLanguage::Korean => text(
                "ClosedNumericMembership",
                "닫힌 수치 식의 소속",
                "닫힌 식의 평가값이 대상 집합에 속합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedNumericMembership",
                "Thuộc về của biểu thức số đóng",
                "Giá trị tính được của biểu thức đóng thuộc tập mục tiêu",
            ),
        }
    }
}

impl ComplexArithmeticClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexArithmeticClosure",
            "Complex Arithmetic Closure",
            "after child WD, `+ - * / …` over C-carriers stay in C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexArithmeticClosure",
            "复数运算封闭",
            "良定的复数运算结果属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "ComplexArithmeticClosure",
            "複數運算封閉",
            "子物件良定後，C 載體上的 `+ - * / …` 結果仍在 C",
        )
    },
            OutputLanguage::French => {
        text(
            "ComplexArithmeticClosure",
            "Clôture arithmétique complexe",
            "Après bonne définition des enfants, `+ - * / …` sur les ensembles porteurs C reste dans C",
        )
    },
            OutputLanguage::Russian => {
        text(
            "ComplexArithmeticClosure",
            "Замкнутость комплексной арифметики",
            "После корректности дочерних объектов `+ - * / …` на носителях C остаётся в C",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "ComplexArithmeticClosure",
            "Clausura aritmética compleja",
            "Tras buena definición de los hijos, `+ - * / …` en portadores C permanece en C",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "ComplexArithmeticClosure",
            "انغلاق الحساب المركب",
            "بعد حسن تعريف العناصر الفرعية تبقى `+ - * / …` على المجموعات الحاملة C في C",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "ComplexArithmeticClosure",
            "複素数演算の閉性",
            "子要素の定義の検証後、C 上の `+ - * / …` の結果は C に属します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "ComplexArithmeticClosure",
            "복소수 산술 닫힘",
            "하위 객체 정의 검증 후 C 바탕 집합의 `+ - * / …` 결과는 C에 속합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "ComplexArithmeticClosure",
            "Đóng của số học phức",
            "Sau kiểm tra xác định tốt của đối tượng con, `+ - * / …` trên tập nền C vẫn trong C",
        )
    },

        }
    }
}

impl RealTrigClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealTrigClosure",
            "Real Trig Closure",
            "after child WD, `sin`/`cos`/`tan`/`cot` and their",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealTrigClosure",
            "实三角运算封闭",
            "良定的实三角运算结果属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "RealTrigClosure",
            "實三角運算封閉",
            "子物件良定後，實三角運算結果屬於實數",
        )
    },
            OutputLanguage::French => {
        text(
            "RealTrigClosure",
            "Clôture trigonométrique réelle",
            "Après bonne définition des enfants, les résultats trigonométriques réels sont réels",
        )
    },
            OutputLanguage::Russian => {
        text(
            "RealTrigClosure",
            "Замкнутость вещественной тригонометрии",
            "После корректности дочерних объектов результаты вещественной тригонометрии вещественны",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "RealTrigClosure",
            "Clausura trigonométrica real",
            "Tras buena definición de los hijos, los resultados trigonométricos reales son reales",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "RealTrigClosure",
            "انغلاق المثلثيات الحقيقية",
            "بعد حسن تعريف العناصر الفرعية تكون نتائج المثلثيات الحقيقية حقيقية",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "RealTrigClosure",
            "実三角関数の閉性",
            "子要素の定義の検証後、実三角関数の結果は実数です",
        )
    },
            OutputLanguage::Korean => {
        text(
            "RealTrigClosure",
            "실수 삼각함수 닫힘",
            "하위 객체 정의 검증 후 실수 삼각함숫값은 실수입니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "RealTrigClosure",
            "Đóng của lượng giác thực",
            "Sau kiểm tra xác định tốt của đối tượng con, kết quả lượng giác thực là thực",
        )
    },

        }
    }
}

impl RealTrigInComplexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealTrigInComplex",
            "Real Trig In Complex",
            "sin/cos/... : R → R ⊂ C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealTrigInComplex",
            "实三角值属于复数",
            "实三角值经 R⊂C 属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "RealTrigInComplex",
                "實三角值屬於複數",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::French => text(
                "RealTrigInComplex",
                "Trigonométrie réelle dans les complexes",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Russian => text(
                "RealTrigInComplex",
                "Вещественная тригонометрия в комплексных",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Spanish => text(
                "RealTrigInComplex",
                "Trigonometría real en complejos",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Arabic => text(
                "RealTrigInComplex",
                "مثلثيات حقيقية في الأعداد المركبة",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Japanese => text(
                "RealTrigInComplex",
                "実三角関数値の複素数への所属",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Korean => text(
                "RealTrigInComplex",
                "실수 삼각함숫값의 복소수 소속",
                "sin/cos/... : R → R ⊂ C",
            ),
            OutputLanguage::Vietnamese => text(
                "RealTrigInComplex",
                "Giá trị lượng giác thực trong số phức",
                "sin/cos/... : R → R ⊂ C",
            ),
        }
    }
}

impl ComplexCoordinateInRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInReal",
            "Complex Coordinate In Real",
            "`C_abs(z)`, `re(z)`, `img(z)` are real after WD",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInReal",
            "复坐标属于实数",
            "模与实部虚部属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "ComplexCoordinateInReal",
            "複數座標屬於實數",
            "良定驗證後 `C_abs(z)`、`re(z)`、`img(z)` 為實數",
        )
    },
            OutputLanguage::French => {
        text(
            "ComplexCoordinateInReal",
            "Coordonnée complexe dans les réels",
            "Après vérification de bonne définition, `C_abs(z)`, `re(z)` et `img(z)` sont réels",
        )
    },
            OutputLanguage::Russian => {
        text(
            "ComplexCoordinateInReal",
            "Комплексная координата в вещественных",
            "После проверки корректности `C_abs(z)`, `re(z)`, `img(z)` вещественны",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "ComplexCoordinateInReal",
            "Coordenada compleja en reales",
            "Tras verificar buena definición, `C_abs(z)`, `re(z)` e `img(z)` son reales",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "ComplexCoordinateInReal",
            "إحداثي مركب في الأعداد الحقيقية",
            "بعد التحقق من حسن التعريف تكون `C_abs(z)` و`re(z)` و`img(z)` حقيقية",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "ComplexCoordinateInReal",
            "複素座標の実数への所属",
            "定義の検証後、`C_abs(z)`、`re(z)`、`img(z)` は実数です",
        )
    },
            OutputLanguage::Korean => {
        text(
            "ComplexCoordinateInReal",
            "복소수 좌표의 실수 소속",
            "정의 검증 후 `C_abs(z)`, `re(z)`, `img(z)`는 실수입니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "ComplexCoordinateInReal",
            "Tọa độ phức trong số thực",
            "Sau kiểm tra xác định tốt, `C_abs(z)`, `re(z)`, `img(z)` là thực",
        )
    },

        }
    }
}

impl ComplexCoordinateInComplexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInComplex",
            "Complex Coordinate In Complex",
            "Complex modulus / coordinates also inhabit C via R ⊂ C",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexCoordinateInComplex",
            "复坐标属于复数",
            "模与实部虚部属于复数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ComplexCoordinateInComplex",
                "複數座標屬於複數",
                "複數模或座標亦經 R ⊂ C 屬於 C",
            ),
            OutputLanguage::French => text(
                "ComplexCoordinateInComplex",
                "Coordonnée complexe dans les complexes",
                "Le module et les coordonnées complexes appartiennent aussi à C via R ⊂ C",
            ),
            OutputLanguage::Russian => text(
                "ComplexCoordinateInComplex",
                "Комплексная координата в комплексных",
                "Комплексный модуль и координаты также принадлежат C через R ⊂ C",
            ),
            OutputLanguage::Spanish => text(
                "ComplexCoordinateInComplex",
                "Coordenada compleja en complejos",
                "El módulo y las coordenadas complejas también pertenecen a C por R ⊂ C",
            ),
            OutputLanguage::Arabic => text(
                "ComplexCoordinateInComplex",
                "إحداثي مركب في الأعداد المركبة",
                "المقياس والإحداثيات المركبة تنتمي أيضًا إلى C عبر R ⊂ C",
            ),
            OutputLanguage::Japanese => text(
                "ComplexCoordinateInComplex",
                "複素座標の複素数への所属",
                "複素数の絶対値と座標は R ⊂ C により C にも属します",
            ),
            OutputLanguage::Korean => text(
                "ComplexCoordinateInComplex",
                "복소수 좌표의 복소수 소속",
                "복소수 절댓값과 좌표는 R ⊂ C로 C에도 속합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ComplexCoordinateInComplex",
                "Tọa độ phức trong số phức",
                "Môđun và tọa độ phức cũng thuộc C qua R ⊂ C",
            ),
        }
    }
}

impl RealArithmeticClosureBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealArithmeticClosure",
            "Real Arithmetic Closure",
            "after domain WD, abs, sqrt, log and ln have real-valued results",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealArithmeticClosure",
            "实数运算封闭",
            "良定的实数运算结果属于实数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "RealArithmeticClosure",
                "實數運算封閉",
                "定義域良定後，abs、sqrt、log、ln 的結果為實數",
            ),
            OutputLanguage::French => text(
                "RealArithmeticClosure",
                "Clôture arithmétique réelle",
                "Après bonne définition du domaine, abs, sqrt, log et ln donnent des réels",
            ),
            OutputLanguage::Russian => text(
                "RealArithmeticClosure",
                "Замкнутость вещественной арифметики",
                "После корректности области abs, sqrt, log и ln дают вещественные значения",
            ),
            OutputLanguage::Spanish => text(
                "RealArithmeticClosure",
                "Clausura aritmética real",
                "Tras buena definición del dominio, abs, sqrt, log y ln dan valores reales",
            ),
            OutputLanguage::Arabic => text(
                "RealArithmeticClosure",
                "انغلاق الحساب الحقيقي",
                "بعد حسن تعريف المجال تكون نتائج abs وsqrt وlog وln حقيقية",
            ),
            OutputLanguage::Japanese => text(
                "RealArithmeticClosure",
                "実数演算の閉性",
                "定義域の検証後、abs、sqrt、log、ln の結果は実数です",
            ),
            OutputLanguage::Korean => text(
                "RealArithmeticClosure",
                "실수 산술 닫힘",
                "정의역 검증 후 abs, sqrt, log, ln의 결과는 실수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "RealArithmeticClosure",
                "Đóng của số học thực",
                "Sau kiểm tra xác định tốt của miền, abs, sqrt, log, ln cho kết quả thực",
            ),
        }
    }
}

impl StandardSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetSubsetMembership",
            "Standard Set Subset Membership",
            "if `x $in S` and `S $subset T` among standard sets,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardSetSubsetMembership",
            "标准集链上传成员",
            "沿标准集包含链提升成员关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "StandardSetSubsetMembership",
                "標準集合子集成員",
                "標準集合中 `x $in S` 與 `S $subset T` 推出 `x $in T`",
            ),
            OutputLanguage::French => text(
                "StandardSetSubsetMembership",
                "Appartenance par inclusion standard",
                "Pour les ensembles standards, `x $in S` et `S $subset T` impliquent `x $in T`",
            ),
            OutputLanguage::Russian => text(
                "StandardSetSubsetMembership",
                "Принадлежность по стандартному включению",
                "Для стандартных множеств `x $in S` и `S $subset T` влекут `x $in T`",
            ),
            OutputLanguage::Spanish => text(
                "StandardSetSubsetMembership",
                "Pertenencia por inclusión estándar",
                "En conjuntos estándar, `x $in S` y `S $subset T` implican `x $in T`",
            ),
            OutputLanguage::Arabic => text(
                "StandardSetSubsetMembership",
                "انتماء عبر احتواء قياسي",
                "للمجموعات القياسية `x $in S` و`S $subset T` تستلزمان `x $in T`",
            ),
            OutputLanguage::Japanese => text(
                "StandardSetSubsetMembership",
                "標準集合の包含による所属",
                "標準集合では `x $in S` と `S $subset T` から `x $in T` を導きます",
            ),
            OutputLanguage::Korean => text(
                "StandardSetSubsetMembership",
                "표준 집합 포함 소속",
                "표준 집합에서 `x $in S`와 `S $subset T`로 `x $in T`를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "StandardSetSubsetMembership",
                "Thuộc về qua tập con chuẩn",
                "Trong tập chuẩn, `x $in S` và `S $subset T` suy ra `x $in T`",
            ),
        }
    }
}

impl FiniteSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetSubsetMembership",
                "Finite Set Subset Membership",
                "the element belongs to a finite set whose every member belongs to the target carrier",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSubsetMembership",
                "有限集合子集成員",
                "元素屬於有限集合，該集合每個成員均屬於目標載體",
            ),
            OutputLanguage::French => text(
                "FiniteSetSubsetMembership",
                "Appartenance par sous-ensemble fini",
                "L'élément appartient à un ensemble fini dont chaque membre appartient à l'ensemble porteur cible",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSubsetMembership",
                "Принадлежность по конечному подмножеству",
                "Элемент принадлежит конечному множеству, каждый член которого принадлежит целевому носителю",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSubsetMembership",
                "Pertenencia por subconjunto finito",
                "El elemento pertenece a conjunto finito cuyos miembros pertenecen al portador objetivo",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSubsetMembership",
                "انتماء عبر مجموعة جزئية منتهية",
                "العنصر ينتمي إلى مجموعة منتهية ينتمي كل عنصر منها إلى المجموعة الحاملة الهدف",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSubsetMembership",
                "有限部分集合による所属",
                "要素はすべての要素が対象台集合に属する有限集合に属します",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSubsetMembership",
                "유한 부분집합 소속",
                "원소는 모든 원소가 대상 바탕 집합에 속하는 유한 집합에 속합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSubsetMembership",
                "Thuộc về qua tập con hữu hạn",
                "Phần tử thuộc tập hữu hạn mà mọi phần tử thuộc tập nền mục tiêu",
            ),

            OutputLanguage::Chinese => text(
                "FiniteSetSubsetMembership",
                "有限集成员类型提升",
                "元素属于有限集，且每个列出的成员都属于目标集合",
            ),
        }
    }
}

impl SetBuilderMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetBuilderMembership",
            "Set Builder Membership",
            "Set-builder membership from base membership plus defining facts",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetBuilderMembership",
            "集合构造成员",
            "由底集成员与定义事实得集合构造成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "SetBuilderMembership",
            "集合構造成員",
            "由基礎成員關係及定義命題得集合構造成員",
        )
    },
            OutputLanguage::French => {
        text(
            "SetBuilderMembership",
            "Appartenance à l'ensemble en compréhension",
            "Appartenance à la compréhension depuis l'appartenance de base et les propositions définissantes",
        )
    },
            OutputLanguage::Russian => {
        text(
            "SetBuilderMembership",
            "Принадлежность множеству по условию",
            "Принадлежность множеству по условию из базовой принадлежности и определяющих утверждений",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "SetBuilderMembership",
            "Pertenencia a conjunto por comprensión",
            "Pertenencia a comprensión desde pertenencia base y proposiciones definitorias",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "SetBuilderMembership",
            "انتماء لمجموعة مبنية",
            "انتماء للمجموعة المبنية من الانتماء الأساسي وقضايا التعريف",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "SetBuilderMembership",
            "内包表記集合への所属",
            "基底集合への所属と定義命題から内包表記集合への所属を導きます",
        )
    },
            OutputLanguage::Korean => {
        text(
            "SetBuilderMembership",
            "조건제시 집합 소속",
            "기초 소속과 정의 명제로 조건제시 집합 소속을 도출합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "SetBuilderMembership",
            "Thuộc tập dựng",
            "Thuộc tập dựng từ sự thuộc về cơ sở và các mệnh đề định nghĩa",
        )
    },

        }
    }
}

impl NativeConstantMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativeConstantMembership",
            "Native Constant Membership",
            "Native mathematical constants inhabit fixed carriers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativeConstantMembership",
            "内置常数成员",
            "内置数学常数属于固定载体",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NativeConstantMembership",
                "內建常數成員",
                "內建數學常數屬於固定載體",
            ),
            OutputLanguage::French => text(
                "NativeConstantMembership",
                "Appartenance de constante native",
                "Les constantes mathématiques natives appartiennent à des ensembles porteurs fixes",
            ),
            OutputLanguage::Russian => text(
                "NativeConstantMembership",
                "Принадлежность встроенной константы",
                "Встроенные математические константы принадлежат фиксированным носителям",
            ),
            OutputLanguage::Spanish => text(
                "NativeConstantMembership",
                "Pertenencia de constante nativa",
                "Las constantes matemáticas nativas pertenecen a portadores fijos",
            ),
            OutputLanguage::Arabic => text(
                "NativeConstantMembership",
                "انتماء ثابت أصلي",
                "الثوابت الرياضية الأصلية تنتمي إلى مجموعات حاملة ثابتة",
            ),
            OutputLanguage::Japanese => text(
                "NativeConstantMembership",
                "組み込み定数の所属",
                "組み込みの数学定数は固定の台集合に属します",
            ),
            OutputLanguage::Korean => text(
                "NativeConstantMembership",
                "내장 상수 소속",
                "내장 수학 상수는 고정된 바탕 집합에 속합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NativeConstantMembership",
                "Thuộc về hằng tích hợp",
                "Các hằng toán học tích hợp thuộc tập nền cố định",
            ),
        }
    }
}

impl ListSetElementMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetElementMembership",
            "List Set Element Membership",
            "if `x = a_i` for some `a_i` in `{a_1, …, a_n}`,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetElementMembership",
            "列表集元素成员",
            "等于某一列出元素则属于列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ListSetElementMembership",
                "列表集合元素成員",
                "x 等於某個列出元素時屬於 `{a_1, …, a_n}`",
            ),
            OutputLanguage::French => text(
                "ListSetElementMembership",
                "Appartenance d'élément d'ensemble liste",
                "Si x égale un élément listé, il appartient à `{a_1, …, a_n}`",
            ),
            OutputLanguage::Russian => text(
                "ListSetElementMembership",
                "Принадлежность элемента списочного множества",
                "Если x равен указанному элементу, он принадлежит `{a_1, …, a_n}`",
            ),
            OutputLanguage::Spanish => text(
                "ListSetElementMembership",
                "Pertenencia de elemento de conjunto de lista",
                "Si x es igual a un elemento listado, pertenece a `{a_1, …, a_n}`",
            ),
            OutputLanguage::Arabic => text(
                "ListSetElementMembership",
                "انتماء عنصر مجموعة قائمة",
                "إذا ساوت x عنصرًا مدرجًا فإنها تنتمي إلى `{a_1, …, a_n}`",
            ),
            OutputLanguage::Japanese => text(
                "ListSetElementMembership",
                "リスト集合の要素の所属",
                "x が列挙された要素に等しければ `{a_1, …, a_n}` に属します",
            ),
            OutputLanguage::Korean => text(
                "ListSetElementMembership",
                "목록 집합 원소 소속",
                "x가 열거된 원소와 같으면 `{a_1, …, a_n}`에 속합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ListSetElementMembership",
                "Thuộc phần tử tập danh sách",
                "Nếu x bằng phần tử liệt kê thì thuộc `{a_1, …, a_n}`",
            ),
        }
    }
}

impl CartMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CartMembership",
            "Cart Membership",
            "`e $in cart(A1,…,An)` (n≥2) from coordinate",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CartMembership",
            "笛卡尔积成员",
            "各分量成员推出笛卡尔积成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "CartMembership",
                "笛卡兒積成員",
                "分量成員推出 `e $in cart(A1,…,An)`（n≥2）",
            ),
            OutputLanguage::French => text(
                "CartMembership",
                "Appartenance au produit cartésien",
                "`e $in cart(A1,…,An)` (n≥2) depuis l'appartenance des coordonnées",
            ),
            OutputLanguage::Russian => text(
                "CartMembership",
                "Принадлежность декартову произведению",
                "`e $in cart(A1,…,An)` (n≥2) из принадлежности координат",
            ),
            OutputLanguage::Spanish => text(
                "CartMembership",
                "Pertenencia a producto cartesiano",
                "`e $in cart(A1,…,An)` (n≥2) desde pertenencia de coordenadas",
            ),
            OutputLanguage::Arabic => text(
                "CartMembership",
                "انتماء لحاصل الضرب الديكارتي",
                "`e $in cart(A1,…,An)` (n≥2) من انتماء الإحداثيات",
            ),
            OutputLanguage::Japanese => text(
                "CartMembership",
                "直積への所属",
                "成分の所属から `e $in cart(A1,…,An)`（n≥2）",
            ),
            OutputLanguage::Korean => text(
                "CartMembership",
                "데카르트 곱 소속",
                "좌표 소속으로 `e $in cart(A1,…,An)`(n≥2)",
            ),
            OutputLanguage::Vietnamese => text(
                "CartMembership",
                "Thuộc tích Descartes",
                "`e $in cart(A1,…,An)` (n≥2) từ sự thuộc về của tọa độ",
            ),
        }
    }
}

impl PowerSetMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowerSetMembership",
            "Power Set Membership",
            "if `A $subset B`, then `A $in power_set(B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerSetMembership", "幂集成员", "子集关系推出幂集成员")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowerSetMembership",
                "冪集成員",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::French => text(
                "PowerSetMembership",
                "Appartenance à l'ensemble des parties",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Russian => text(
                "PowerSetMembership",
                "Принадлежность множеству подмножеств",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Spanish => text(
                "PowerSetMembership",
                "Pertenencia a conjunto potencia",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Arabic => text(
                "PowerSetMembership",
                "انتماء لمجموعة القوى",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Japanese => text(
                "PowerSetMembership",
                "べき集合への所属",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Korean => text(
                "PowerSetMembership",
                "멱집합 소속",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "PowerSetMembership",
                "Thuộc tập lũy thừa",
                "`A $subset B` ⇒ `A $in power_set(B)`",
            ),
        }
    }
}

impl StructObjMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StructObjMembership",
            "Struct Obj Membership",
            "`e` inhabits `&Struct` when it meets the field",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StructObjMembership",
            "结构对象成员",
            "结构载体与等价律推出结构集成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "StructObjMembership",
            "結構物件成員",
            "結構載體與等價律推出 `e` 為結構集合成員",
        )
    },
            OutputLanguage::French => {
        text(
            "StructObjMembership",
            "Appartenance d'objet de structure",
            "L'ensemble porteur de structure et les lois d'équivalence établissent l'appartenance de `e`",
        )
    },
            OutputLanguage::Russian => {
        text(
            "StructObjMembership",
            "Принадлежность структурного объекта",
            "Структурный носитель и законы эквивалентности устанавливают принадлежность `e`",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "StructObjMembership",
            "Pertenencia de objeto de estructura",
            "El portador estructural y las leyes de equivalencia establecen pertenencia de `e`",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "StructObjMembership",
            "انتماء كائن بنية",
            "المجموعة الحاملة للبنية وقوانين التكافؤ تثبت انتماء `e`",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "StructObjMembership",
            "構造オブジェクトの所属",
            "構造の台集合と同値法則から `e` の構造集合への所属を導きます",
        )
    },
            OutputLanguage::Korean => {
        text(
            "StructObjMembership",
            "구조 객체 소속",
            "구조 바탕 집합과 동치 법칙으로 `e`의 구조 집합 소속을 도출합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "StructObjMembership",
            "Thuộc đối tượng cấu trúc",
            "Tập nền cấu trúc và luật tương đương xác lập sự thuộc về của `e`",
        )
    },

        }
    }
}

impl PredecessorFromNaturalAboveZeroBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "PredecessorFromNaturalAboveZero",
                "Natural above zero has a predecessor",
                "`x $in N` and `0 < x` imply `x - 1 $in N`",
            ),
            OutputLanguage::ChineseTraditional => text(
                "PredecessorFromNaturalAboveZero",
                "大於零的自然數有前驅",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::French => text(
                "PredecessorFromNaturalAboveZero",
                "Un naturel supérieur à zéro a un prédécesseur",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Russian => text(
                "PredecessorFromNaturalAboveZero",
                "Натуральное больше нуля имеет предыдущее значение",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Spanish => text(
                "PredecessorFromNaturalAboveZero",
                "Un natural mayor que cero tiene predecesor",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Arabic => text(
                "PredecessorFromNaturalAboveZero",
                "للعدد الطبيعي الأكبر من صفر سابق",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Japanese => text(
                "PredecessorFromNaturalAboveZero",
                "ゼロより大きい自然数には直前の値があります",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Korean => text(
                "PredecessorFromNaturalAboveZero",
                "0보다 큰 자연수는 이전 값이 있습니다",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Vietnamese => text(
                "PredecessorFromNaturalAboveZero",
                "Số tự nhiên lớn hơn không có số liền trước",
                "`x $in N` ∧ `0 < x` ⇒ `x - 1 $in N`",
            ),

            OutputLanguage::Chinese => text(
                "PredecessorFromNaturalAboveZero",
                "零小于自然数时的前驱",
                "已知自然数 x 且 0 < x，其前驱仍属于自然数",
            ),
        }
    }
}

impl PredecessorFromPositiveNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "PredecessorFromPositiveNatural",
                "Predecessor of a positive natural",
                "`x $in N` and `x > 0` imply `x - 1 $in N`",
            ),
            OutputLanguage::ChineseTraditional => text(
                "PredecessorFromPositiveNatural",
                "正自然數的前驅",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::French => text(
                "PredecessorFromPositiveNatural",
                "Prédécesseur d'un naturel positif",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Russian => text(
                "PredecessorFromPositiveNatural",
                "Предыдущее значение положительного натурального",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Spanish => text(
                "PredecessorFromPositiveNatural",
                "Predecesor de natural positivo",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Arabic => text(
                "PredecessorFromPositiveNatural",
                "سابق عدد طبيعي موجب",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Japanese => text(
                "PredecessorFromPositiveNatural",
                "正の自然数の直前の値",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Korean => text(
                "PredecessorFromPositiveNatural",
                "양의 자연수의 이전 값",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Vietnamese => text(
                "PredecessorFromPositiveNatural",
                "Số liền trước của tự nhiên dương",
                "`x $in N` ∧ `x > 0` ⇒ `x - 1 $in N`",
            ),

            OutputLanguage::Chinese => text(
                "PredecessorFromPositiveNatural",
                "正自然数的前驱",
                "已知自然数严格大于零，其前驱仍属于自然数",
            ),
        }
    }
}

impl PredecessorInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PredecessorInNatural",
            "Predecessor In Natural",
            "`x $in N` and `x >= 1` ⇒ `x - 1 $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PredecessorInNatural",
            "前驱属于自然数",
            "自然数且至少为 1 则前驱仍是自然数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PredecessorInNatural",
                "前驅屬於自然數",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::French => text(
                "PredecessorInNatural",
                "Prédécesseur dans les naturels",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Russian => text(
                "PredecessorInNatural",
                "Предыдущее значение в натуральных",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Spanish => text(
                "PredecessorInNatural",
                "Predecesor en naturales",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Arabic => text(
                "PredecessorInNatural",
                "السابق في الأعداد الطبيعية",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Japanese => text(
                "PredecessorInNatural",
                "直前の値の自然数への所属",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Korean => text(
                "PredecessorInNatural",
                "이전 값의 자연수 소속",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
            OutputLanguage::Vietnamese => text(
                "PredecessorInNatural",
                "Số liền trước trong tự nhiên",
                "`x $in N` ∧ `x >= 1` ⇒ `x - 1 $in N`",
            ),
        }
    }
}

impl AnonymousFnApplicationInFnRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AnonymousFnApplicationInFnRange",
            "Anonymous function application in range",
            "A well-defined application of an anonymous function belongs to its range",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AnonymousFnApplicationInFnRange",
            "匿名函数应用落在值域",
            "良定的匿名函数应用落在该函数值域",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "AnonymousFnApplicationInFnRange",
            "匿名函數套用落在值域",
            "良定的匿名函數套用屬於其值域",
        )
    },
            OutputLanguage::French => {
        text(
            "AnonymousFnApplicationInFnRange",
            "Application de fonction anonyme dans l'image",
            "Une application bien définie d'une fonction anonyme appartient à son image",
        )
    },
            OutputLanguage::Russian => {
        text(
            "AnonymousFnApplicationInFnRange",
            "Применение анонимной функции в области значений",
            "Корректно определённое применение анонимной функции принадлежит её области значений",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "AnonymousFnApplicationInFnRange",
            "Aplicación de función anónima en rango",
            "Una aplicación bien definida de función anónima pertenece a su rango",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "AnonymousFnApplicationInFnRange",
            "تطبيق دالة مجهولة في المدى",
            "التطبيق حسن التعريف لدالة مجهولة ينتمي إلى مداها",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "AnonymousFnApplicationInFnRange",
            "無名関数の適用の値域への所属",
            "適切に定義された無名関数の適用はその値域に属します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "AnonymousFnApplicationInFnRange",
            "익명 함수 적용의 치역 소속",
            "타당하게 정의된 익명 함수 적용은 그 치역에 속합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "AnonymousFnApplicationInFnRange",
            "Áp dụng hàm ẩn danh trong miền giá trị",
            "Áp dụng xác định tốt của hàm ẩn danh thuộc miền giá trị của nó",
        )
    },

        }
    }
}

impl UnionMembershipFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromLeft",
            "Union Membership From Left",
            "`x $in A` ⇒ `x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromLeft",
            "由左因子得并成员",
            "属于左因子则属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionMembershipFromLeft",
                "由左成員得聯集成員",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::French => text(
                "UnionMembershipFromLeft",
                "Appartenance à l'union depuis la gauche",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "UnionMembershipFromLeft",
                "Принадлежность объединению слева",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "UnionMembershipFromLeft",
                "Pertenencia a unión desde izquierda",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "UnionMembershipFromLeft",
                "انتماء للاتحاد من اليسار",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "UnionMembershipFromLeft",
                "左側から和集合への所属",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "UnionMembershipFromLeft",
                "왼쪽으로 합집합 소속",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionMembershipFromLeft",
                "Thuộc hợp từ trái",
                "`x $in A` ⇒ `x $in union(A, B)`",
            ),
        }
    }
}

impl UnionMembershipFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromRight",
            "Union Membership From Right",
            "`x $in B` ⇒ `x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionMembershipFromRight",
            "由右因子得并成员",
            "属于右因子则属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionMembershipFromRight",
                "由右成員得聯集成員",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::French => text(
                "UnionMembershipFromRight",
                "Appartenance à l'union depuis la droite",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "UnionMembershipFromRight",
                "Принадлежность объединению справа",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "UnionMembershipFromRight",
                "Pertenencia a unión desde derecha",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "UnionMembershipFromRight",
                "انتماء للاتحاد من اليمين",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "UnionMembershipFromRight",
                "右側から和集合への所属",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "UnionMembershipFromRight",
                "오른쪽으로 합집합 소속",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionMembershipFromRight",
                "Thuộc hợp từ phải",
                "`x $in B` ⇒ `x $in union(A, B)`",
            ),
        }
    }
}

impl IntersectMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectMembership",
            "Intersect Membership",
            "`x $in A` and `x $in B` ⇒ `x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectMembership", "交成员", "同时属于两边则属于交")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectMembership",
                "交集成員",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::French => text(
                "IntersectMembership",
                "Appartenance à l'intersection",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "IntersectMembership",
                "Принадлежность пересечению",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "IntersectMembership",
                "Pertenencia a intersección",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "IntersectMembership",
                "انتماء للتقاطع",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "IntersectMembership",
                "交差への所属",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "IntersectMembership",
                "교집합 소속",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectMembership",
                "Thuộc giao",
                "`x $in A` ∧ `x $in B` ⇒ `x $in intersect(A, B)`",
            ),
        }
    }
}

impl SetMinusMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusMembership",
            "Set Minus Membership",
            "`x $in A` and `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusMembership",
            "差集成员",
            "属于左且不属于右则属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusMembership",
                "差集成員",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::French => text(
                "SetMinusMembership",
                "Appartenance à la différence",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "SetMinusMembership",
                "Принадлежность разности",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusMembership",
                "Pertenencia a diferencia",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusMembership",
                "انتماء للفرق",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusMembership",
                "差集合への所属",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "SetMinusMembership",
                "차집합 소속",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusMembership",
                "Thuộc hiệu",
                "`x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
            ),
        }
    }
}

impl FamilyUnionMembershipFromMemberBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FamilyUnionMembershipFromMember",
            "Family Union Membership From Member",
            "`A $in F` and `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FamilyUnionMembershipFromMember",
            "由成员集得族并成员",
            "属于族中某集则属于族并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FamilyUnionMembershipFromMember",
                "由集合族成員得聯集成員",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::French => text(
                "FamilyUnionMembershipFromMember",
                "Appartenance à l'union d'une famille depuis un membre",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Russian => text(
                "FamilyUnionMembershipFromMember",
                "Принадлежность объединению семейства из элемента",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Spanish => text(
                "FamilyUnionMembershipFromMember",
                "Pertenencia a unión de familia desde miembro",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Arabic => text(
                "FamilyUnionMembershipFromMember",
                "انتماء لاتحاد عائلة من عنصر",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Japanese => text(
                "FamilyUnionMembershipFromMember",
                "集合族の要素から和への所属",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Korean => text(
                "FamilyUnionMembershipFromMember",
                "집합족 원소로 합집합 소속",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
            OutputLanguage::Vietnamese => text(
                "FamilyUnionMembershipFromMember",
                "Thuộc hợp của họ từ phần tử",
                "`A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
            ),
        }
    }
}

impl IndexUnionMembershipFromIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IndexUnionMembershipFromIndex",
            "Index Union Membership From Index",
            "`i $in I` and `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IndexUnionMembershipFromIndex",
            "由指标得指标并成员",
            "属于某指标纤维则属于指标并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IndexUnionMembershipFromIndex",
                "由索引得帶索引聯集成員",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::French => text(
                "IndexUnionMembershipFromIndex",
                "Appartenance à l'union indexée depuis l'indice",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Russian => text(
                "IndexUnionMembershipFromIndex",
                "Принадлежность индексированному объединению из индекса",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Spanish => text(
                "IndexUnionMembershipFromIndex",
                "Pertenencia a unión indexada desde índice",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Arabic => text(
                "IndexUnionMembershipFromIndex",
                "انتماء لاتحاد مفهرس من فهرس",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Japanese => text(
                "IndexUnionMembershipFromIndex",
                "添字から添字付きの和への所属",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Korean => text(
                "IndexUnionMembershipFromIndex",
                "인덱스로 인덱스 합집합 소속",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
            OutputLanguage::Vietnamese => text(
                "IndexUnionMembershipFromIndex",
                "Thuộc hợp theo chỉ số từ chỉ số",
                "`i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
            ),
        }
    }
}

impl IntervalMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntervalMembership",
            "Interval Membership",
            "`x $in R` plus the matching open/closed endpoint inequalities",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntervalMembership",
            "区间成员",
            "由载体与端点界推出区间成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntervalMembership",
                "區間成員",
                "`x $in R` 及對應開閉端點不等式",
            ),
            OutputLanguage::French => text(
                "IntervalMembership",
                "Appartenance à l'intervalle",
                "`x $in R` et les inégalités correspondantes aux extrémités ouvertes ou fermées",
            ),
            OutputLanguage::Russian => text(
                "IntervalMembership",
                "Принадлежность интервалу",
                "`x $in R` и соответствующие неравенства открытых или замкнутых границ",
            ),
            OutputLanguage::Spanish => text(
                "IntervalMembership",
                "Pertenencia a intervalo",
                "`x $in R` y desigualdades correspondientes de extremos abiertos o cerrados",
            ),
            OutputLanguage::Arabic => text(
                "IntervalMembership",
                "انتماء لفترة",
                "`x $in R` والمتباينات المقابلة للأطراف المفتوحة أو المغلقة",
            ),
            OutputLanguage::Japanese => text(
                "IntervalMembership",
                "区間への所属",
                "`x $in R` と対応する開端点または閉端点の不等式",
            ),
            OutputLanguage::Korean => text(
                "IntervalMembership",
                "구간 소속",
                "`x $in R`과 대응하는 열린 또는 닫힌 끝점 부등식",
            ),
            OutputLanguage::Vietnamese => text(
                "IntervalMembership",
                "Thuộc khoảng",
                "`x $in R` cùng các bất đẳng thức đầu mút mở hoặc đóng tương ứng",
            ),
        }
    }
}

impl OneSideInfinityIntervalMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalMembership",
            "One Side Infinity Interval Membership",
            "One-sided real ray membership from carrier and the finite endpoint bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalMembership",
            "单侧无穷区间成员",
            "由载体与有限端点界推出射线成员",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "OneSideInfinityIntervalMembership",
            "單側無限區間成員",
            "由載體與有限端點界得單側實射線成員",
        )
    },
            OutputLanguage::French => {
        text(
            "OneSideInfinityIntervalMembership",
            "Appartenance à un intervalle non borné d'un côté",
            "Appartenance à une demi-droite réelle depuis l'ensemble porteur et la borne d'extrémité finie",
        )
    },
            OutputLanguage::Russian => {
        text(
            "OneSideInfinityIntervalMembership",
            "Принадлежность интервалу с одной бесконечной границей",
            "Принадлежность вещественному лучу по носителю и конечной границе",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "OneSideInfinityIntervalMembership",
            "Pertenencia a intervalo infinito por un lado",
            "Pertenencia a semirrecta real desde portador y cota del extremo finito",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "OneSideInfinityIntervalMembership",
            "انتماء لفترة غير محدودة من جانب واحد",
            "انتماء لشعاع حقيقي من المجموعة الحاملة وحد الطرف المنتهي",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "OneSideInfinityIntervalMembership",
            "片側が無限の区間への所属",
            "台集合と有限端点の境界から片側実数半直線への所属を導きます",
        )
    },
            OutputLanguage::Korean => {
        text(
            "OneSideInfinityIntervalMembership",
            "한쪽 무한 구간 소속",
            "바탕 집합과 유한 끝점 경계로 실수 반직선 소속을 도출합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "OneSideInfinityIntervalMembership",
            "Thuộc khoảng vô hạn một phía",
            "Thuộc tia thực một phía từ tập nền và cận đầu mút hữu hạn",
        )
    },

        }
    }
}

impl AddInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddInNatural",
            "Add In Natural",
            "Natural addition closure: `a $in N` and `b $in N` ⇒ `a + b $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AddInNatural", "自然数加法封闭", "自然数加法封闭")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AddInNatural",
                "自然數加法封閉",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::French => text(
                "AddInNatural",
                "Addition dans les naturels",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Russian => text(
                "AddInNatural",
                "Сложение в натуральных",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Spanish => text(
                "AddInNatural",
                "Suma en naturales",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Arabic => text(
                "AddInNatural",
                "جمع في الأعداد الطبيعية",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Japanese => text(
                "AddInNatural",
                "自然数での加算",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Korean => text(
                "AddInNatural",
                "자연수 덧셈",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
            OutputLanguage::Vietnamese => text(
                "AddInNatural",
                "Cộng trong số tự nhiên",
                "`a $in N` ∧ `b $in N` ⇒ `a + b $in N`",
            ),
        }
    }
}

impl MulInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulInNatural",
            "Mul In Natural",
            "Natural multiplication closure: `a $in N` and `b $in N` ⇒ `a * b $in N`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MulInNatural", "自然数乘法封闭", "自然数乘法封闭")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulInNatural",
                "自然數乘法封閉",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::French => text(
                "MulInNatural",
                "Multiplication dans les naturels",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Russian => text(
                "MulInNatural",
                "Умножение в натуральных",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Spanish => text(
                "MulInNatural",
                "Multiplicación en naturales",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Arabic => text(
                "MulInNatural",
                "ضرب في الأعداد الطبيعية",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Japanese => text(
                "MulInNatural",
                "自然数での乗算",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Korean => text(
                "MulInNatural",
                "자연수 곱셈",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
            OutputLanguage::Vietnamese => text(
                "MulInNatural",
                "Nhân trong số tự nhiên",
                "`a $in N` ∧ `b $in N` ⇒ `a * b $in N`",
            ),
        }
    }
}

impl NativeScalarCodomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Native Scalar Codomain".to_string(),
            message: format!(
                "after input-domain WD, the native result belongs to {} and its standard-set supertypes",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "原生标量返回类型".to_string(),
            message: format!(
                "参数定义域已通过良定检查，原生运算结果属于 {} 及其标准集合超集",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "原生純量陪域".to_string(),
            message: format!(
                "輸入定義域良定後，原生結果屬於 {} 及其標準集合超集",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::French => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Codomaine scalaire natif".to_string(),
            message: format!(
                "Après bonne définition du domaine d'entrée, le résultat natif appartient à {} et à ses sur-ensembles standards",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Russian => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Встроенная скалярная область значений".to_string(),
            message: format!(
                "После корректности входной области встроенный результат принадлежит {} и его стандартным надмножествам",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Spanish => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Codominio escalar nativo".to_string(),
            message: format!(
                "Tras buena definición del dominio de entrada, el resultado nativo pertenece a {} y a sus superconjuntos estándar",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Arabic => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "مجال مقابل قياسي أصلي".to_string(),
            message: format!(
                "بعد حسن تعريف مجال الإدخال تنتمي النتيجة الأصلية إلى {} ومجموعاتها القياسية الفوقية",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Japanese => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "組み込みスカラー終域".to_string(),
            message: format!(
                "入力定義域の検証後、組み込みの結果は {} とその標準上位集合に属します",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Korean => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "내장 스칼라 공역".to_string(),
            message: format!(
                "입력 정의역 검증 후 내장 결과는 {}와 표준 상위집합에 속합니다",
                self.codomain.ir().as_str(),
            ),
        }
    },
            OutputLanguage::Vietnamese => {
        BuiltinRuleText {
            rule_id: "NativeScalarCodomain",
            rule_name: "Đối miền vô hướng tích hợp".to_string(),
            message: format!(
                "Sau kiểm tra xác định tốt của miền đầu vào, kết quả tích hợp thuộc {} và các tập cha chuẩn",
                self.codomain.ir().as_str(),
            ),
        }
    },

        }
    }
}

impl CartDimInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("CartDimInNatural", "Cartesian Dimension in N", "a well-defined Cartesian dimension belongs to N and its numeric supertypes"),
            OutputLanguage::ChineseTraditional => text("CartDimInNatural", "笛卡兒積維度屬於 N", "良定的笛卡兒積維度屬於 N 及其數值超集"),
            OutputLanguage::French => text("CartDimInNatural", "Dimension cartésienne dans N", "Une dimension cartésienne bien définie appartient à N et à ses sur-ensembles numériques"),
            OutputLanguage::Russian => text("CartDimInNatural", "Декартова размерность в N", "Корректно определённая декартова размерность принадлежит N и его числовым надмножествам"),
            OutputLanguage::Spanish => text("CartDimInNatural", "Dimensión cartesiana en N", "Una dimensión cartesiana bien definida pertenece a N y a sus superconjuntos numéricos"),
            OutputLanguage::Arabic => text("CartDimInNatural", "بعد ديكارتي في N", "البعد الديكارتي حسن التعريف ينتمي إلى N ومجموعاته العددية الفوقية"),
            OutputLanguage::Japanese => text("CartDimInNatural", "直積の次元の N への所属", "適切に定義された直積の次元は N とその数値上位集合に属します"),
            OutputLanguage::Korean => text("CartDimInNatural", "데카르트 차원의 N 소속", "타당하게 정의된 데카르트 차원은 N과 그 수치 상위집합에 속합니다"),
            OutputLanguage::Vietnamese => text("CartDimInNatural", "Chiều Descartes trong N", "Chiều Descartes xác định tốt thuộc N và các tập số cha của nó"),

            OutputLanguage::Chinese => text("CartDimInNatural", "笛卡尔维数属于自然数", "已通过良定检查的笛卡尔维数属于 N 及其数值超集"),
        }
    }
}

impl TupleDimInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("TupleDimInNatural", "Tuple Dimension in N", "a well-defined tuple dimension belongs to N and its numeric supertypes"),
            OutputLanguage::ChineseTraditional => text("TupleDimInNatural", "元組維度屬於 N", "良定的元組維度屬於 N 及其數值超集"),
            OutputLanguage::French => text("TupleDimInNatural", "Dimension de tuple dans N", "Une dimension de tuple bien définie appartient à N et à ses sur-ensembles numériques"),
            OutputLanguage::Russian => text("TupleDimInNatural", "Размерность кортежа в N", "Корректно определённая размерность кортежа принадлежит N и его числовым надмножествам"),
            OutputLanguage::Spanish => text("TupleDimInNatural", "Dimensión de tupla en N", "Una dimensión de tupla bien definida pertenece a N y a sus superconjuntos numéricos"),
            OutputLanguage::Arabic => text("TupleDimInNatural", "بعد صف في N", "بعد الصف حسن التعريف ينتمي إلى N ومجموعاته العددية الفوقية"),
            OutputLanguage::Japanese => text("TupleDimInNatural", "タプルの次元の N への所属", "適切に定義されたタプルの次元は N とその数値上位集合に属します"),
            OutputLanguage::Korean => text("TupleDimInNatural", "튜플 차원의 N 소속", "타당하게 정의된 튜플 차원은 N과 그 수치 상위집합에 속합니다"),
            OutputLanguage::Vietnamese => text("TupleDimInNatural", "Chiều của bộ trong N", "Chiều bộ xác định tốt thuộc N và các tập số cha của nó"),

            OutputLanguage::Chinese => text("TupleDimInNatural", "元组维数属于自然数", "已通过良定检查的元组维数属于 N 及其数值超集"),
        }
    }
}

impl AnonymousFnInDeclaredFnSetBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("AnonymousFnInDeclaredFnSet", "Anonymous function in declared function set", "the checked function's signature matches the target modulo bound-name renaming"),
            OutputLanguage::ChineseTraditional => text("AnonymousFnInDeclaredFnSet", "匿名函數屬於宣告函數集", "經檢查函數的簽章在繫結名稱改名後符合目標"),
            OutputLanguage::French => text("AnonymousFnInDeclaredFnSet", "Fonction anonyme dans l'ensemble de fonctions déclaré", "La signature vérifiée de la fonction correspond à la cible après renommage des noms liés"),
            OutputLanguage::Russian => text("AnonymousFnInDeclaredFnSet", "Анонимная функция в объявленном множестве функций", "Проверенная сигнатура функции совпадает с целью с точностью до переименования связанных имён"),
            OutputLanguage::Spanish => text("AnonymousFnInDeclaredFnSet", "Función anónima en conjunto de funciones declarado", "La firma comprobada de función coincide con objetivo salvo renombrado de nombres ligados"),
            OutputLanguage::Arabic => text("AnonymousFnInDeclaredFnSet", "دالة مجهولة في مجموعة الدوال المعلنة", "توقيع الدالة المتحقق منه يطابق الهدف بعد إعادة تسمية الأسماء المرتبطة"),
            OutputLanguage::Japanese => text("AnonymousFnInDeclaredFnSet", "宣言された関数集合への無名関数の所属", "検査済みの関数の型は束縛名の変更を除いて目標と一致します"),
            OutputLanguage::Korean => text("AnonymousFnInDeclaredFnSet", "선언된 함수 집합의 익명 함수", "검사된 함수의 시그니처는 바인딩 이름 변경을 제외하고 목표와 일치합니다"),
            OutputLanguage::Vietnamese => text("AnonymousFnInDeclaredFnSet", "Hàm ẩn danh trong tập hàm đã khai báo", "Chữ ký hàm đã kiểm tra khớp mục tiêu sau đổi tên biến ràng buộc"),

            OutputLanguage::Chinese => text("AnonymousFnInDeclaredFnSet", "匿名函数属于声明的函数集", "函数已通过良定检查，目标签名仅在绑定参数名称上不同"),
        }
    }
}

impl PositiveIntegerInNPosBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let (name, message) = match lang {
            OutputLanguage::English => (
                "Positive integer membership",
                "An integer strictly greater than zero belongs to N+",
            ),
            OutputLanguage::ChineseTraditional => ("正整數成員關係", "嚴格大於零的整數屬於 N+"),
            OutputLanguage::French => (
                "Appartenance aux entiers positifs",
                "Un entier strictement positif appartient à N+",
            ),
            OutputLanguage::Russian => (
                "Принадлежность положительным целым",
                "Целое строго больше нуля принадлежит N+",
            ),
            OutputLanguage::Spanish => (
                "Pertenencia a enteros positivos",
                "Un entero estrictamente mayor que cero pertenece a N+",
            ),
            OutputLanguage::Arabic => (
                "انتماء للأعداد الصحيحة الموجبة",
                "العدد الصحيح الأكبر تمامًا من صفر ينتمي إلى N+",
            ),
            OutputLanguage::Japanese => (
                "正の整数への所属",
                "ゼロより厳密に大きい整数は N+ に属します",
            ),
            OutputLanguage::Korean => ("양의 정수 소속", "0보다 엄격히 큰 정수는 N+에 속합니다"),
            OutputLanguage::Vietnamese => ("Thuộc số nguyên dương", "Số nguyên dương thuộc N+"),

            OutputLanguage::Chinese => ("正整数成员", "整数且严格大于零的对象属于 N+"),
        };
        BuiltinRuleText {
            rule_id: "PositiveIntegerInNPos",
            rule_name: name.into(),
            message: message.into(),
        }
    }
}

impl FiniteSetMaxMemberBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FiniteSetMaxMember", "Finite set maximum member", "A well-defined finite nonempty real set contains its maximum"),
            OutputLanguage::Chinese => text("FiniteSetMaxMember", "有限集合最大值是成员", "良定的有限非空实数集合包含它的最大值"),
            OutputLanguage::ChineseTraditional => text("FiniteSetMaxMember", "有限集合最大值是成員", "良定的有限非空實數集合包含它的最大值"),
            OutputLanguage::French => text("FiniteSetMaxMember", "Maximum dans un ensemble fini", "Un ensemble réel fini non vide contient son maximum"),
            OutputLanguage::Russian => text("FiniteSetMaxMember", "максимум конечного множества", "Непустое конечное вещественное множество содержит свой максимум"),
            OutputLanguage::Spanish => text("FiniteSetMaxMember", "máximo de conjunto finito", "Un conjunto real finito no vacío contiene su máximo"),
            OutputLanguage::Arabic => text("FiniteSetMaxMember", "قيمتها العظمى مجموعة منتهية", "تحتوي المجموعة الحقيقية المنتهية غير الفارغة على قيمتها العظمى"),
            OutputLanguage::Japanese => text("FiniteSetMaxMember", "有限集合の最大値は元", "有限非空実数集合はその最大値を含みます"),
            OutputLanguage::Korean => text("FiniteSetMaxMember", "유한 집합의 최댓값 원소", "비어 있지 않은 유한 실수 집합은 그 최댓값을 포함합니다"),
            OutputLanguage::Vietnamese => text("FiniteSetMaxMember", "Giá trị lớn nhất thuộc tập hữu hạn", "Tập số thực hữu hạn khác rỗng chứa Giá trị lớn nhất của nó"),
        }
    }
}

impl FiniteSetMinMemberBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FiniteSetMinMember", "Finite set minimum member", "A well-defined finite nonempty real set contains its minimum"),
            OutputLanguage::Chinese => text("FiniteSetMinMember", "有限集合最小值是成员", "良定的有限非空实数集合包含它的最小值"),
            OutputLanguage::ChineseTraditional => text("FiniteSetMinMember", "有限集合最小值是成員", "良定的有限非空實數集合包含它的最小值"),
            OutputLanguage::French => text("FiniteSetMinMember", "Minimum dans un ensemble fini", "Un ensemble réel fini non vide contient son minimum"),
            OutputLanguage::Russian => text("FiniteSetMinMember", "минимум конечного множества", "Непустое конечное вещественное множество содержит свой минимум"),
            OutputLanguage::Spanish => text("FiniteSetMinMember", "mínimo de conjunto finito", "Un conjunto real finito no vacío contiene su mínimo"),
            OutputLanguage::Arabic => text("FiniteSetMinMember", "قيمتها الصغرى مجموعة منتهية", "تحتوي المجموعة الحقيقية المنتهية غير الفارغة على قيمتها الصغرى"),
            OutputLanguage::Japanese => text("FiniteSetMinMember", "有限集合の最小値は元", "有限非空実数集合はその最小値を含みます"),
            OutputLanguage::Korean => text("FiniteSetMinMember", "유한 집합의 최솟값 원소", "비어 있지 않은 유한 실수 집합은 그 최솟값을 포함합니다"),
            OutputLanguage::Vietnamese => text("FiniteSetMinMember", "Giá trị nhỏ nhất thuộc tập hữu hạn", "Tập số thực hữu hạn khác rỗng chứa Giá trị nhỏ nhất của nó"),
        }
    }
}
