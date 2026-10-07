//! Explain + cite for `NotEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{NotEqualFactSearchProofByBuiltinRule,
    AbsNonzeroFromArgBuiltinRuleProof,
    AddNonzeroFromNotEqualNegationBuiltinRuleProof,
    ClosedDecimalNotEqualBuiltinRuleProof,
    CosNonzeroAtZeroBuiltinRuleProof,
    CosNonzeroOnOpenHalfPiBuiltinRuleProof,
    DiffNonzeroFromInequalityBuiltinRuleProof,
    DivNonzeroFromFactorsBuiltinRuleProof,
    EmptySetFromNonemptyBuiltinRuleProof,
    FromKnownStrictOrderBuiltinRuleProof,
    ListSetDifferentLengthBuiltinRuleProof,
    MembershipContradictionBuiltinRuleProof,
    NotEqualSymmetryBuiltinRuleProof,
    PowNonzeroFromBaseBuiltinRuleProof,
    ProductComponentNonzeroBuiltinRuleProof,
    SinNonzeroAtHalfPiBuiltinRuleProof,
    SinNonzeroOnOpenPiBuiltinRuleProof,
    SqrtNonzeroFromPositiveArgBuiltinRuleProof,
    SquareSumNonzeroFromComponentBuiltinRuleProof,
    ZeroFromNatAndOneLeBuiltinRuleProof
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl NotEqualFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("Exponential is nonzero", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("Factorial is nonzero", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("Nonzero sign from argument", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("Nonzero sign reflection", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_en(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_en(),
            Self::PeriodicTrigNonzero(_) => text(
                "Nonzero periodic trigonometric value",
                "The exact pi coefficient and checked integer terms exclude sine/cosine zeros",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "Nonzero value from a signed bound",
                "A checked bound separates the value strictly from zero",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "Imaginary unit is nonzero",
                "The reserved imaginary unit satisfies i² = -1 and is nonzero",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "Inequality from a nonzero difference",
                "A checked nonzero difference implies the two operands are unequal",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "Nonopposite operands from a nonzero sum",
                "A checked nonzero sum shows that neither operand is the negation of the other",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "Nonzero modulus of a nonzero complex number",
                "A nonzero complex number has a nonzero modulus",
            ),
            Self::PiNonzero(_) => text(
                "Pi is nonzero",
                "Pi is strictly positive and therefore cannot equal zero",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_en(),
            Self::ClosedRational(_) => text(
                "Exact rational inequality",
                "Exact closed fractions have different normalized values",
            ),
            Self::ClosedComplex(_) => text(
                "Exact complex inequality",
                "The exact real or imaginary coordinates differ",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_en(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_en(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_en(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_en(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_en(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_en(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_en(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_en(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_en(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_en(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_en(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_en(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_en(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_en(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_en(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_en(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_en(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_en(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_en(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_en(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("指数函数非零", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("阶乘非零", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("非零参数的 sign 非零", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("sign 的非零反射", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_zh(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_zh(),
            Self::PeriodicTrigNonzero(_) => text(
                "周期三角值非零",
                "精确 pi 系数和已验证的整数项排除了正弦或余弦的零点",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "由带符号界推出非零",
                "已验证的界使该值严格大于零或严格小于零",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "虚数单位非零",
                "内建虚数单位满足 i² = -1，因而不等于零",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "差非零推出不相等",
                "已验证的差非零说明两个操作数不相等",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "和非零排除互为相反数",
                "已验证的和非零说明两个操作数不互为相反数",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "非零复数的模非零",
                "非零复数的模不等于零",
            ),
            Self::PiNonzero(_) => text(
                "圆周率非零",
                "圆周率严格为正，因此不等于零",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_zh(),
            Self::ClosedRational(_) => text(
                "精确分数不等",
                "两边的精确分数规范化后不同",
            ),
            Self::ClosedComplex(_) => text(
                "精确复数不等",
                "精确实部或虚部不同",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_zh(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_zh(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_zh(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_zh(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_zh(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_zh(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_zh(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_zh(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_zh(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_zh(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_zh(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_zh(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_zh(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_zh(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_zh(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_zh(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_zh(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_zh(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_zh(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_zh(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("指數函數非零", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("階乘非零", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("非零參數的 sign 非零", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("sign 的非零反射", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_zh_hant(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_zh_hant(),
            Self::PeriodicTrigNonzero(_) => text(
                "週期三角值非零",
                "精確 pi 係數與已驗證的整數項排除正弦或餘弦零點",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "由帶符號界推出非零",
                "已驗證的界使該值嚴格大於零或嚴格小於零",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "虛數單位非零",
                "保留的虛數單位滿足 i² = -1 且非零",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "差非零推出不相等",
                "已驗證的差非零說明兩個運算元不相等",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "和非零排除互為相反數",
                "已驗證的和非零說明兩個運算元不互為相反數",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "非零複數的模非零",
                "非零複數的模不等於零",
            ),
            Self::PiNonzero(_) => text(
                "圓周率非零",
                "圓周率嚴格為正，因此不等於零",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_zh_hant(),
            Self::ClosedRational(_) => text(
                "精確有理數不等",
                "精確封閉分數的正規化值不同",
            ),
            Self::ClosedComplex(_) => text(
                "精確複數不等",
                "精確實部或虛部座標不同",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_zh_hant(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_zh_hant(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_zh_hant(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_zh_hant(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_zh_hant(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_zh_hant(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_zh_hant(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_zh_hant(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_zh_hant(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_zh_hant(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_zh_hant(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_zh_hant(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_zh_hant(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_zh_hant(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_zh_hant(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_zh_hant(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_zh_hant(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_zh_hant(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("Exponentielle non nulle", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("Factorielle non nulle", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("Signe non nul de l’argument", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("Réflexion du signe non nul", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_fr(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_fr(),
            Self::PeriodicTrigNonzero(_) => text("Valeur trigonométrique périodique non nulle", "Le coefficient exact de pi et les termes entiers vérifiés excluent les zéros du sinus ou cosinus"),
            Self::NonzeroFromSignedBound(_) => text("Non-nullité issue d’une borne signée", "Une borne vérifiée sépare strictement la valeur de zéro"),
            Self::ImaginaryUnitNonzero(_) => text("Unité imaginaire non nulle", "L'unité imaginaire réservée vérifie i² = -1 et est non nulle"),
            Self::InequalityFromDifferenceNonzero(_) => text("Inégalité issue d’une différence non nulle", "Une différence non nulle vérifiée implique que les deux opérandes sont distincts"),
            Self::InequalityFromSumNonzero(_) => text("Termes non opposés issus d’une somme non nulle", "Une somme non nulle vérifiée montre que les deux termes ne sont pas opposés"),
            Self::ComplexModulusNonzero(_) => text("Module non nul d’un complexe non nul", "Un nombre complexe non nul a un module non nul"),
            Self::PiNonzero(_) => text("Pi non nul", "Pi est strictement positif et ne peut donc pas être nul"),
            Self::ClosedDecimal(p) => p.rule_name_and_message_fr(),
            Self::ClosedRational(_) => text("Inégalité rationnelle exacte", "Les fractions fermées exactes ont des valeurs normalisées différentes"),
            Self::ClosedComplex(_) => text("Inégalité complexe exacte", "Les coordonnées réelles ou imaginaires exactes diffèrent"),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_fr(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_fr(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_fr(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_fr(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_fr(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_fr(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_fr(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_fr(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_fr(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_fr(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_fr(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_fr(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_fr(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_fr(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_fr(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_fr(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_fr(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_fr(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_fr(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_fr(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("Экспонента не равна нулю", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("Факториал не равен нулю", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("Ненулевой знак аргумента", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("Отражение ненулевого знака", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ru(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ru(),
            Self::PeriodicTrigNonzero(_) => text("Ненулевое периодическое тригонометрическое значение", "Точный коэффициент pi и проверенные целочисленные члены исключают нули синуса или косинуса"),
            Self::NonzeroFromSignedBound(_) => text("Ненулевое значение из знаковой границы", "Проверенная граница строго отделяет значение от нуля"),
            Self::ImaginaryUnitNonzero(_) => text("Мнимая единица отлична от нуля", "Зарезервированная мнимая единица удовлетворяет i² = -1 и ненулевая"),
            Self::InequalityFromDifferenceNonzero(_) => text("Неравенство из ненулевой разности", "Проверенная ненулевая разность означает, что операнды различны"),
            Self::InequalityFromSumNonzero(_) => text("Числа не противоположны при ненулевой сумме", "Проверенная ненулевая сумма означает, что числа не противоположны"),
            Self::ComplexModulusNonzero(_) => text("Ненулевой модуль ненулевого комплексного числа", "Ненулевое комплексное число имеет ненулевой модуль"),
            Self::PiNonzero(_) => text("Число пи отлично от нуля", "Число пи строго положительно и потому не равно нулю"),
            Self::ClosedDecimal(p) => p.rule_name_and_message_ru(),
            Self::ClosedRational(_) => text("Точное рациональное неравенство", "Точные замкнутые дроби имеют различные нормализованные значения"),
            Self::ClosedComplex(_) => text("Точное комплексное неравенство", "Точные действительные или мнимые координаты различаются"),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_ru(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_ru(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_ru(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_ru(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_ru(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_ru(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_ru(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_ru(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_ru(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_ru(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_ru(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_ru(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_ru(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_ru(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_ru(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_ru(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_ru(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_ru(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_ru(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_ru(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("Exponencial no nula", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("Factorial no nulo", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("Signo no nulo del argumento", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("Reflexión del signo no nulo", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_es(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_es(),
            Self::PeriodicTrigNonzero(_) => text("Valor trigonométrico periódico no nulo", "El coeficiente exacto de pi y los términos enteros comprobados excluyen ceros de seno o coseno"),
            Self::NonzeroFromSignedBound(_) => text("Valor no nulo a partir de una cota con signo", "Una cota comprobada separa estrictamente el valor de cero"),
            Self::ImaginaryUnitNonzero(_) => text("Unidad imaginaria no nula", "La unidad imaginaria reservada cumple i² = -1 y es no nula"),
            Self::InequalityFromDifferenceNonzero(_) => text("Desigualdad a partir de una diferencia no nula", "Una diferencia no nula comprobada implica que los operandos son distintos"),
            Self::InequalityFromSumNonzero(_) => text("Operandos no opuestos a partir de una suma no nula", "Una suma no nula comprobada muestra que los operandos no son opuestos"),
            Self::ComplexModulusNonzero(_) => text("Módulo no nulo de un complejo no nulo", "Un número complejo no nulo tiene módulo no nulo"),
            Self::PiNonzero(_) => text("Pi no nulo", "Pi es estrictamente positivo y por tanto no puede ser cero"),
            Self::ClosedDecimal(p) => p.rule_name_and_message_es(),
            Self::ClosedRational(_) => text("Desigualdad racional exacta", "Las fracciones cerradas exactas tienen valores normalizados distintos"),
            Self::ClosedComplex(_) => text("Desigualdad compleja exacta", "Las coordenadas reales o imaginarias exactas difieren"),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_es(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_es(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_es(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_es(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_es(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_es(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_es(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_es(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_es(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_es(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_es(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_es(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_es(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_es(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_es(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_es(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_es(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_es(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_es(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_es(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("الدالة الأسية غير صفرية", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("المضروب غير صفري", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("إشارة وسيط غير صفري", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("انعكاس الإشارة غير الصفرية", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ar(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ar(),
            Self::PeriodicTrigNonzero(_) => text(
                "قيمة مثلثية دورية غير صفرية",
                "معامل pi الدقيق والحدود الصحيحة المتحقق منها يستبعدان أصفار الجيب أو جيب التمام",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "قيمة غير صفرية من حد ذي إشارة",
                "الحد المتحقق منه يفصل القيمة عن الصفر بشكل صارم",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "الوحدة التخيلية غير صفرية",
                "الوحدة التخيلية المحجوزة تحقق i² = -1 وهي غير صفرية",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "عدم التساوي من فرق غير صفري",
                "الفرق غير الصفري المتحقق منه يعني أن المعاملين غير متساويين",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "عددان غير متعاكسين من مجموع غير صفري",
                "المجموع غير الصفري المتحقق منه يبيّن أن العددين ليسا متعاكسين",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "مقياس غير صفري لعدد مركب غير صفري",
                "العدد المركب غير الصفري له مقياس غير صفري",
            ),
            Self::PiNonzero(_) => text(
                "باي غير صفري",
                "باي موجب تمامًا ولذلك لا يمكن أن يساوي صفرًا",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_ar(),
            Self::ClosedRational(_) => text(
                "عدم مساواة نسبية دقيقة",
                "الكسور المغلقة الدقيقة لها قيم مطبّعة مختلفة",
            ),
            Self::ClosedComplex(_) => text(
                "عدم مساواة مركبة دقيقة",
                "الإحداثيات الحقيقية أو التخيلية الدقيقة مختلفة",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_ar(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_ar(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_ar(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_ar(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_ar(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_ar(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_ar(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_ar(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_ar(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_ar(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_ar(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_ar(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_ar(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_ar(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_ar(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_ar(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_ar(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_ar(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_ar(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_ar(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("指数関数はゼロでない", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("階乗はゼロでない", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("引数がゼロでなければ符号もゼロでない", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("符号がゼロでなければ引数もゼロでない", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ja(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ja(),
            Self::PeriodicTrigNonzero(_) => text(
                "周期的三角関数値の非ゼロ性",
                "正確な pi の係数と検証済みの整数項が正弦または余弦の零点を除外します",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "符号付きの境界による非零性",
                "確認済みの境界により値が零より厳密に大きいか小さいことが分かります",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "虚数単位の非零性",
                "予約された虚数単位は i² = -1 を満たし、非ゼロです",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "非零の差による不等性",
                "差が零でないことを確認すると、二つの数が異なると分かります",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "非零の和による互いに逆符号である可能性の排除",
                "和が零でないことを確認すると、二つの数は互いに符号反転した値ではありません",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "非零の複素数の絶対値の非零性",
                "零でない複素数の絶対値は零ではありません",
            ),
            Self::PiNonzero(_) => text(
                "円周率の非零性",
                "円周率は正なので零にはなりません",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_ja(),
            Self::ClosedRational(_) => text(
                "有理数の正確な不等性",
                "正確な閉じた分数の正規化値が異なります",
            ),
            Self::ClosedComplex(_) => text(
                "複素数の正確な不等性",
                "正確な実部または虚部の座標が異なります",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_ja(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_ja(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_ja(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_ja(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_ja(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_ja(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_ja(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_ja(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_ja(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_ja(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_ja(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_ja(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_ja(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_ja(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_ja(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_ja(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_ja(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_ja(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_ja(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_ja(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("지수 함수는 영이 아님", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("팩토리얼은 영이 아님", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("영이 아닌 인수의 부호", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("영이 아닌 부호의 반영", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ko(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_ko(),
            Self::PeriodicTrigNonzero(_) => text(
                "주기 삼각함숫값이 0이 아님",
                "정확한 pi 계수와 검증된 정수 항이 사인 또는 코사인의 영점을 배제합니다",
            ),
            Self::NonzeroFromSignedBound(_) => text(
                "부호가 있는 경계에 따른 비영성",
                "검사된 경계가 값을 영보다 엄격히 크거나 작게 만듭니다",
            ),
            Self::ImaginaryUnitNonzero(_) => text(
                "허수단위의 비영성",
                "예약된 허수 단위는 i² = -1을 만족하며 0이 아닙니다",
            ),
            Self::InequalityFromDifferenceNonzero(_) => text(
                "영이 아닌 차에 따른 서로 다름",
                "검사된 차가 영이 아니면 두 피연산자는 서로 다릅니다",
            ),
            Self::InequalityFromSumNonzero(_) => text(
                "영이 아닌 합에 따른 반대 수 관계 배제",
                "검사된 합이 영이 아니면 두 피연산자는 서로 반대 수가 아닙니다",
            ),
            Self::ComplexModulusNonzero(_) => text(
                "영이 아닌 복소수 절댓값의 비영성",
                "영이 아닌 복소수의 절댓값은 영이 아닙니다",
            ),
            Self::PiNonzero(_) => text(
                "원주율의 비영성",
                "원주율은 양수이므로 영일 수 없습니다",
            ),
            Self::ClosedDecimal(p) => p.rule_name_and_message_ko(),
            Self::ClosedRational(_) => text(
                "정확한 유리수 불일치",
                "정확한 닫힌 분수의 정규화 값이 다릅니다",
            ),
            Self::ClosedComplex(_) => text(
                "정확한 복소수 불일치",
                "정확한 실수부 또는 허수부 좌표가 다릅니다",
            ),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_ko(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_ko(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_ko(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_ko(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_ko(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_ko(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_ko(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_ko(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_ko(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_ko(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_ko(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_ko(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_ko(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_ko(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_ko(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_ko(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_ko(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_ko(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_ko(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_ko(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::ExpNonzero(_) => text("Hàm mũ khác không", "x in R: exp(x)>0 => exp(x)!=0"),
            Self::FactorialNonzero(_) => text("Giai thừa khác không", "n in N: factorial(n)>0 => factorial(n)!=0"),
            Self::SignNonzeroFromArgument(_) => text("Dấu của đối số khác không", "x in R, x!=0 => sign(x)!=0"),
            Self::SignNonzeroReflection(_) => text("Phản ánh dấu khác không", "x in R, sign(x)!=0 => x!=0"),
            Self::CosNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_vi(),
            Self::SinNonzeroOnFirstQuadrant(p) => p.rule_name_and_message_vi(),
            Self::PeriodicTrigNonzero(_) => text("Giá trị lượng giác tuần hoàn khác không", "Hệ số pi chính xác và các hạng nguyên đã kiểm tra loại trừ điểm không của sin hoặc cos"),
            Self::NonzeroFromSignedBound(_) => text("Giá trị khác không từ cận có dấu", "Cận đã kiểm tra tách giá trị nghiêm ngặt khỏi không"),
            Self::ImaginaryUnitNonzero(_) => text("Đơn vị ảo khác không", "Đơn vị ảo dành riêng thỏa i² = -1 và khác không"),
            Self::InequalityFromDifferenceNonzero(_) => text("Không bằng nhau từ hiệu khác không", "Hiệu khác không đã kiểm tra suy ra hai toán hạng khác nhau"),
            Self::InequalityFromSumNonzero(_) => text("Các số không đối nhau từ tổng khác không", "Tổng khác không đã kiểm tra cho thấy hai toán hạng không đối nhau"),
            Self::ComplexModulusNonzero(_) => text("Môđun khác không của số phức khác không", "Số phức khác không có môđun khác không"),
            Self::PiNonzero(_) => text("Pi khác không", "Pi dương nên không thể bằng không"),
            Self::ClosedDecimal(p) => p.rule_name_and_message_vi(),
            Self::ClosedRational(_) => text("Bất đẳng thức hữu tỉ chính xác", "Các phân số đóng chính xác có giá trị chuẩn hóa khác nhau"),
            Self::ClosedComplex(_) => text("Bất đẳng thức phức chính xác", "Các tọa độ thực hoặc ảo chính xác khác nhau"),
            Self::NotEqualSymmetry(p) => p.rule_name_and_message_vi(),
            Self::ListSetDifferentLength(p) => p.rule_name_and_message_vi(),
            Self::FromKnownStrictOrder(p) => p.rule_name_and_message_vi(),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_name_and_message_vi(),
            Self::CosNonzeroAtZero(p) => p.rule_name_and_message_vi(),
            Self::SinNonzeroOnOpenPi(p) => p.rule_name_and_message_vi(),
            Self::SinNonzeroAtHalfPi(p) => p.rule_name_and_message_vi(),
            Self::AbsNonzeroFromArg(p) => p.rule_name_and_message_vi(),
            Self::DiffNonzeroFromInequality(p) => p.rule_name_and_message_vi(),
            Self::EmptySetFromNonempty(p) => p.rule_name_and_message_vi(),
            Self::ZeroFromNatAndOneLe(p) => p.rule_name_and_message_vi(),
            Self::LcmNonzeroFromNonzeroOperands(p) => p.rule_name_and_message_vi(),
            Self::LogNonzeroFromNonunitArgument(p) => p.rule_name_and_message_vi(),
            Self::PositiveNonunitIntegerPower(p) => p.rule_name_and_message_vi(),
            Self::PowNonzeroFromBase(p) => p.rule_name_and_message_vi(),
            Self::DivNonzeroFromFactors(p) => p.rule_name_and_message_vi(),
            Self::ProductComponentNonzero(p) => p.rule_name_and_message_vi(),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_name_and_message_vi(),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_name_and_message_vi(),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_name_and_message_vi(),
            Self::MembershipContradiction(p) => p.rule_name_and_message_vi(),
        }
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

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NonzeroFromSignedBound(p) => Some(p.cite_fact_id),
            Self::FromKnownStrictOrder(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromDifferenceNonzero(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromSumNonzero(p) => p.premise_proof.cite_fact_id(),
            _ => None,
        }
    }
}

impl ClosedDecimalNotEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closed decimal inequality",
            "Both sides evaluate to different closed numbers",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "封闭数值不等",
            "两边算出不同的封闭数",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "封閉十進位不等",
            "兩邊算出不同的封閉數值",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inégalité décimale fermée",
            "Les deux membres donnent des nombres fermés différents",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неравенство замкнутых десятичных значений",
            "Обе части вычисляются в различные замкнутые числа",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desigualdad decimal cerrada",
            "Ambos lados dan números cerrados diferentes",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدم مساواة عشرية مغلقة",
            "يُقيَّم الطرفان إلى عددين مغلقين مختلفين",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉じた小数値の不等性",
            "両辺の評価値は異なる閉じた数値です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 소수 값의 불일치",
            "양변의 평가값은 서로 다른 닫힌 수입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bất đẳng thức thập phân đóng",
            "Hai vế cho các số đóng khác nhau",
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

impl NotEqualSymmetryBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inequality symmetry",
            "Inequality is symmetric in its two sides",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("不等号对称性", "不等关系对两边对称")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("不等關係對稱性", "不等關係的兩邊對稱")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Symétrie de l'inégalité de valeurs",
            "L'inégalité de valeurs est symétrique entre ses deux membres",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Симметрия неравенства значений",
            "Неравенство значений симметрично относительно обеих частей",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Simetría de desigualdad de valores",
            "La desigualdad de valores es simétrica entre sus dos lados",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تناظر عدم المساواة",
            "عدم المساواة متناظرة في طرفيها",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非等値関係の対称性",
            "非等値関係は両辺について対称です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "불일치 대칭성",
            "같지 않음 관계는 양변에 대해 대칭입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính đối xứng của không bằng nhau",
            "Quan hệ không bằng nhau đối xứng theo hai vế",
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

impl ListSetDifferentLengthBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "List sets ≠ by length",
            "List sets of different lengths are unequal",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "列表集因长度不等",
            "不同长度的列表集不等",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由長度得列表集合不等",
            "長度不同的列表集合不相等",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inégalité d'ensembles listes par longueur",
            "Des ensembles listes de longueurs différentes sont inégaux",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неравенство списочных множеств по длине",
            "Списочные множества различной длины не равны",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desigualdad de conjuntos de lista por longitud",
            "Conjuntos de lista de distinta longitud son desiguales",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدم مساواة مجموعات القوائم بالطول",
            "مجموعات القوائم ذات الأطوال المختلفة غير متساوية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "長さによるリスト集合の不等性",
            "長さの異なるリスト集合は等しくありません",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "길이에 의한 목록 집합 불일치",
            "길이가 다른 목록 집합은 같지 않습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập danh sách khác nhau theo độ dài",
            "Các tập danh sách có độ dài khác nhau không bằng nhau",
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

impl FromKnownStrictOrderBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From known strict order",
            "Inequality follows from a known strict order fact",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由已知严格序",
            "不等关系由已知严格序事实推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知嚴格序",
            "不等由已知嚴格序命題得出",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis un ordre strict connu",
            "L'inégalité découle d'une proposition d'ordre strict connue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известного строгого порядка",
            "Неравенство следует из известного утверждения строгого порядка",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde orden estricto conocido",
            "La desigualdad se deduce de una proposición de orden estricto conocida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من ترتيب صارم معلوم",
            "تنتج عدم المساواة من قضية ترتيب صارم معلومة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の狭義順序から",
            "不等性は既知の狭義順序の命題から導かれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 엄격한 순서에서",
            "불일치는 알려진 엄격한 순서 명제에서 도출됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ thứ tự nghiêm ngặt đã biết",
            "Bất đẳng thức suy ra từ mệnh đề thứ tự nghiêm ngặt đã biết",
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

impl CosNonzeroOnOpenHalfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cosine is nonzero on the open half-pi interval",
            "cosine is nonzero on the open half-pi interval",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "cos 在 (-π/2,π/2) 非零",
            "余弦在开半 π 区间上非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "(-π/2,π/2) 上 cos ≠ 0",
            "餘弦在開半 pi 區間上非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "cos ≠ 0 sur (-π/2,π/2)",
            "Le cosinus est non nul sur l'intervalle ouvert de demi-pi",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "cos ≠ 0 на (-π/2,π/2)",
            "Косинус ненулевой на открытом интервале половины pi",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Coseno no nulo en el intervalo abierto de menos pi sobre dos a pi sobre dos",
            "El coseno es no nulo en el intervalo abierto de medio pi",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "cos ≠ 0 على (-π/2,π/2)",
            "جيب التمام غير صفري على فترة نصف pi المفتوحة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "(-π/2,π/2) 上で cos ≠ 0",
            "余弦は開いた半 pi 区間上で非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "(-π/2,π/2)에서 cos ≠ 0",
            "코사인은 열린 반 pi 구간에서 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "cos ≠ 0 trên (-π/2,π/2)",
            "Cos khác không trên khoảng nửa pi mở",
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

impl CosNonzeroAtZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cosine is nonzero at zero",
            "cosine is nonzero at zero",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("余弦函数在零处非零", "余弦在 0 处非零")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("餘弦函數在零處非零", "餘弦在零處非零")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cosinus non nul en zéro",
            "Le cosinus est non nul en zéro",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Косинус ненулевой при нулевом аргументе", "Косинус ненулевой в нуле")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Coseno no nulo en cero",
            "El coseno es no nulo en cero",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جيب التمام غير صفري عند الصفر",
            "جيب التمام غير صفري عند الصفر",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における余弦の非零性", "余弦はゼロで非ゼロです")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "영에서 코사인의 비영성",
            "코사인은 0에서 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Cosin khác không tại không", "Cos khác không tại không")
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

impl SinNonzeroOnOpenPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sine is nonzero between zero and pi",
            "sine is nonzero on the open pi interval",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "sin 在 (0,π) 非零",
            "正弦在开 π 区间上非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "(0,π) 上 sin ≠ 0",
            "正弦在開 pi 區間上非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "sin ≠ 0 sur (0,π)",
            "Le sinus est non nul sur l'intervalle ouvert de pi",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "sin ≠ 0 на (0,π)",
            "Синус ненулевой на открытом интервале pi",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Seno no nulo entre cero y pi",
            "El seno es no nulo en el intervalo abierto de pi",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "sin ≠ 0 على (0,π)",
            "الجيب غير صفري على فترة pi المفتوحة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "(0,π) 上で sin ≠ 0",
            "正弦は開いた pi 区間上で非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "(0,π)에서 sin ≠ 0",
            "사인은 열린 pi 구간에서 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "sin ≠ 0 trên (0,π)",
            "Sin khác không trên khoảng pi mở",
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

impl SinNonzeroAtHalfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sine is nonzero at half pi",
            "sine is nonzero at half pi",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正弦函数在半圆周率处非零", "正弦在 π/2 处非零")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正弦函數在半圓周率處非零", "正弦在半 pi 處非零")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Sinus non nul en pi sur deux",
            "Le sinus est non nul en demi-pi",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Синус ненулевой при половине пи",
            "Синус ненулевой в половине pi",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Seno no nulo en pi sobre dos",
            "El seno es no nulo en medio pi",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الجيب غير صفري عند نصف باي",
            "الجيب غير صفري عند نصف pi",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "二分のπにおける正弦の非零性",
            "正弦は半 pi で非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "이분의 π에서 사인의 비영성",
            "사인은 반 pi에서 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Sin khác không tại pi chia hai",
            "Sin khác không tại nửa pi",
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

impl AbsNonzeroFromArgBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonzero argument has nonzero absolute value",
            "Absolute value is nonzero when the argument is nonzero",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非零参数的绝对值非零",
            "当参数非零时绝对值非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非零引數的絕對值非零",
            "引數非零時絕對值非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Argument non nul et valeur absolue non nulle",
            "La valeur absolue est non nulle si l'argument est non nul",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ненулевой аргумент имеет ненулевой модуль",
            "Модуль ненулевой, если аргумент ненулевой",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Argumento no nulo con valor absoluto no nulo",
            "El valor absoluto es no nulo si el argumento es no nulo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الوسيط غير الصفري له قيمة مطلقة غير صفرية",
            "القيمة المطلقة غير صفرية إذا كان الوسيط غير صفري",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非零の引数の絶対値の非零性",
            "引数が非ゼロなら絶対値は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "영이 아닌 인수의 절댓값 비영성",
            "인수가 0이 아니면 절댓값은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đối số khác không có giá trị tuyệt đối khác không",
            "Giá trị tuyệt đối khác không khi đối số khác không",
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

impl DiffNonzeroFromInequalityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Unequal operands have nonzero difference",
            "A difference is nonzero when the operands are unequal",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "不相等的数之差非零",
            "两边不等则差非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "不相等的數之差非零",
            "運算元不等時差非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Opérandes distincts et différence non nulle",
            "Une différence est non nulle si les opérandes sont différents",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Различные операнды имеют ненулевую разность",
            "Разность ненулевая, если операнды не равны",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Operandos distintos tienen diferencia no nula",
            "La diferencia es no nula si los operandos son distintos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "المعاملات غير المتساوية لها فرق غير صفري",
            "الفرق غير صفري إذا كان المعاملان غير متساويين",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "異なる数の差の非零性",
            "被演算子が異なれば差は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "서로 다른 수의 차의 비영성",
            "피연산자가 다르면 차는 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hai toán hạng khác nhau có hiệu khác không",
            "Hiệu khác không khi các toán hạng không bằng nhau",
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

impl EmptySetFromNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ nonempty",
            "The empty set is unequal to a nonempty set",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("∅ ≠ 非空", "空集不等于非空集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "∅ 不等於非空集合",
            "空集合不等於非空集合",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ ensemble non vide",
            "L'ensemble vide est différent d'un ensemble non vide",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ непустое множество",
            "Пустое множество не равно непустому",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ conjunto no vacío",
            "El conjunto vacío no es igual a un conjunto no vacío",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ مجموعة غير خالية",
            "المجموعة الخالية لا تساوي مجموعة غير خالية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ 空でない集合",
            "空集合は空でない集合と等しくありません",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ 비어 있지 않은 집합",
            "공집합은 비어 있지 않은 집합과 같지 않습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "∅ ≠ tập không rỗng",
            "Tập rỗng không bằng tập không rỗng",
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

impl ZeroFromNatAndOneLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural number at least one is nonzero",
            "A natural number bounded below by one cannot equal zero: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "至少为一的自然数非零",
            "自然数 n 满足 n ≥ 1 时不可能等于零，即 n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "至少為一的自然數非零",
            "自然數 n 滿足 n ≥ 1 時不可能等於零，即 n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Naturel au moins égal à un et non nul",
            "Un naturel minoré par un ne peut pas être nul: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Натуральное число не меньше единицы ненулевое",
            "Натуральное число не меньше единицы не может быть равно нулю: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Natural al menos uno es no nulo",
            "Un natural acotado inferiormente por uno no puede ser cero: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "العدد الطبيعي الذي لا يقل عن واحد غير صفري",
            "العدد الطبيعي المحدود من أسفل بواحد لا يمكن أن يساوي صفرًا: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "一以上の自然数の非零性",
            "一以上の自然数が零になることはありません：n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "일 이상인 자연수의 비영성",
            "일 이상인 자연수는 영일 수 없습니다: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số tự nhiên ít nhất bằng một khác không",
            "Số tự nhiên có cận dưới bằng một không thể bằng không: n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0",
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

impl PowNonzeroFromBaseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "pow ≠ 0 from base",
            "A power is nonzero when the base is nonzero",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由底非零得幂非零", "底非零则幂非零")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由底數非零得冪非零",
            "底數非零時冪非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance ≠ 0 depuis la base",
            "Une puissance est non nulle si la base est non nulle",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Степень ≠ 0 из основания",
            "Степень ненулевая, если основание ненулевое",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia ≠ 0 desde la base",
            "Una potencia es no nula si la base es no nula",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القوة ≠ 0 من الأساس",
            "القوة غير صفرية إذا كان الأساس غير صفري",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "底から冪 ≠ 0",
            "底が非ゼロなら冪は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "밑으로 거듭제곱 ≠ 0",
            "밑이 0이 아니면 거듭제곱은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa ≠ 0 từ cơ số",
            "Lũy thừa khác không khi cơ số khác không",
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

impl DivNonzeroFromFactorsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 from factors",
            "A quotient is nonzero when numerator and denominator are nonzero",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由因子得 a/b ≠ 0",
            "分子分母都非零则商非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由因子非零得 a/b ≠ 0",
            "分子與分母非零時商非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 depuis les facteurs",
            "Un quotient est non nul si le numérateur et le dénominateur sont non nuls",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 из множителей",
            "Частное ненулевое, если числитель и знаменатель ненулевые",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 a partir de factores",
            "Un cociente es no nulo si numerador y denominador son no nulos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 من العوامل",
            "خارج القسمة غير صفري إذا كان البسط والمقام غير صفريين",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "因子から a/b ≠ 0",
            "分子と分母が非ゼロなら商は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "인자로 a/b ≠ 0",
            "분자와 분모가 0이 아니면 몫은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "a/b ≠ 0 từ các thừa số",
            "Thương khác không khi tử và mẫu khác không",
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

impl ProductComponentNonzeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Product ≠ 0 from component",
            "A product is nonzero when a component is nonzero under nonzero companions",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由分量得积 ≠ 0",
            "在同伴非零时，分量非零则积非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由分量非零得乘積非零",
            "一因子非零且其他因子非零時乘積非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit ≠ 0 depuis une composante",
            "Un produit est non nul si une composante et ses facteurs associés sont non nuls",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Произведение ≠ 0 из компоненты",
            "Произведение ненулевое, если компонента и остальные множители ненулевые",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto ≠ 0 desde componente",
            "Un producto es no nulo si una componente y los factores acompañantes son no nulos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل الضرب ≠ 0 من مكوّن",
            "حاصل الضرب غير صفري إذا كان أحد المكونات ومرافقاته غير صفرية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "成分から積 ≠ 0",
            "一つの成分と他の因子が非ゼロなら積は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "성분으로 곱 ≠ 0",
            "한 성분과 나머지 인자가 모두 0이 아니면 곱은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích ≠ 0 từ thành phần",
            "Tích khác không khi một thành phần và các thừa số đi kèm khác không",
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

impl SqrtNonzeroFromPositiveArgBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 from positive arg",
            "Square root is nonzero when the argument is positive",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由正参数得 √ ≠ 0",
            "当参数为正时平方根非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由正引數得 √ 非零",
            "引數正時平方根非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 depuis un argument positif",
            "La racine carrée est non nulle si l'argument est positif",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 из положительного аргумента",
            "Квадратный корень ненулевой, если аргумент положителен",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 desde argumento positivo",
            "La raíz cuadrada es no nula si el argumento es positivo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 من وسيط موجب",
            "الجذر التربيعي غير صفري إذا كان الوسيط موجبًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の引数から √ ≠ 0",
            "引数が正なら平方根は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양수 인수로 √ ≠ 0",
            "인수가 양수이면 제곱근은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "√ ≠ 0 từ đối số dương",
            "Căn bậc hai khác không khi đối số dương",
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

impl SquareSumNonzeroFromComponentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonzero real component gives a nonzero sum of squares",
            "A sum of squares is nonzero when a component is nonzero",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实数分量非零则平方和非零",
            "分量非零则平方和非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "實數分量非零則平方和非零",
            "一分量非零時平方和非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composante réelle non nulle et somme des carrés non nulle",
            "Une somme de carrés est non nulle si une composante est non nulle",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ненулевая вещественная компонента даёт ненулевую сумму квадратов",
            "Сумма квадратов ненулевая, если одна компонента ненулевая",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Componente real no nula y suma de cuadrados no nula",
            "Una suma de cuadrados es no nula si una componente es no nula",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مكوّن حقيقي غير صفري يجعل مجموع المربعات غير صفري",
            "مجموع المربعات غير صفري إذا كان أحد المكونات غير صفري",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非零の実数成分による二乗和の非零性",
            "一つの成分が非ゼロなら平方和は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "영이 아닌 실수 성분에 따른 제곱합의 비영성",
            "한 성분이 0이 아니면 제곱합은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thành phần thực khác không cho tổng bình phương khác không",
            "Tổng bình phương khác không khi một thành phần khác không",
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

impl AddNonzeroFromNotEqualNegationBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonopposite summands have nonzero sum",
            "A sum is nonzero when the summands are not negatives",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非互为相反数的加数之和非零",
            "加数互不为相反数则和非零",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非互為相反數的加數之和非零",
            "加數不是互為相反數時和非零",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme non nulle de termes non opposés",
            "Une somme est non nulle si les termes ne sont pas opposés",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сумма чисел, не противоположных друг другу, ненулевая",
            "Сумма ненулевая, если слагаемые не противоположны",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Sumandos no opuestos tienen suma no nula",
            "Una suma es no nula si los sumandos no son opuestos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع حدين غير متعاكسين غير صفري",
            "المجموع غير صفري إذا لم يكن الحدّان متعاكسين",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "互いに逆符号でない二数の和の非零性",
            "加数が互いに逆符号の同値でなければ和は非ゼロです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "서로 반대 수가 아닌 두 수의 합의 비영성",
            "두 항이 서로 반대수가 아니면 합은 0이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Các số hạng không đối nhau có tổng khác không",
            "Tổng khác không khi các số hạng không đối nhau",
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

impl MembershipContradictionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Membership contradiction",
            "Conflicting membership facts yield inequality",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "成员关系矛盾",
            "冲突的成员关系推出不等",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "成員關係矛盾",
            "衝突的成員關係得出不等",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Contradiction d'appartenance",
            "Des appartenances incompatibles impliquent l'inégalité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Противоречие принадлежности",
            "Противоречивые принадлежности дают неравенство",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Contradicción de pertenencia",
            "Pertenencias incompatibles implican desigualdad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تناقض الانتماء",
            "قضايا انتماء متعارضة تؤدي إلى عدم المساواة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "所属の矛盾",
            "矛盾する所属命題から不等性を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "소속 모순",
            "상충하는 소속 명제로 불일치를 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Mâu thuẫn thuộc về",
            "Các mệnh đề thuộc về mâu thuẫn suy ra bất đẳng thức",
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
