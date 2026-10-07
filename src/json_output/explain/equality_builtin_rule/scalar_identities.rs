//! Scalar and trigonometric proof enums own one explanation method per language.

use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("Zero sign reflection", "x in R: sign(x)=0 => x=0"),
Self::FiniteSetMaxSelection(_) => ("Exact finite-set maximum", "Select an original rational member and certify every member is no greater"),
Self::FiniteSetMinSelection(_) => ("Exact finite-set minimum", "Select an original rational member and certify every member is no smaller"),
Self::AbsZeroArgument(_) => ("Zero absolute value", "A real number whose absolute value is zero equals zero"),
Self::FloorNegation(_) => ("Floor of a negation", "floor(-x) = -ceil(x) for real x"),
Self::CeilNegation(_) => ("Ceiling of a negation", "ceil(-x) = -floor(x) for real x"),
Self::FloorIntegerTranslation(_) => ("Integer translation of floor", "An integer shift commutes with floor"),
Self::CeilIntegerTranslation(_) => ("Integer translation of ceiling", "An integer shift commutes with ceiling"),
Self::MinMaxAbsorption(_) => ("Minimum absorbs maximum", "min(a, max(a, b)) = a for real operands"),
Self::MaxMinAbsorption(_) => ("Maximum absorbs minimum", "max(a, min(a, b)) = a for real operands"),
Self::LcmZero(_) => ("Zero argument of lcm", "The least common multiple is zero when either integer argument is zero"),
};
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("sign 的零反射", "x in R: sign(x)=0 => x=0"),
Self::FiniteSetMaxSelection(_) => ("有限集合最大值精确选取", "选取原有理数成员并证明每个成员不大于它"),
Self::FiniteSetMinSelection(_) => ("有限集合最小值精确选取", "选取原有理数成员并证明每个成员不小于它"),
Self::AbsZeroArgument(_) => ("绝对值为零", "实数的绝对值为零时，该实数等于零"),
Self::FloorNegation(_) => ("取负后的向下取整", "实数 x 满足 floor(-x) = -ceil(x)"),
Self::CeilNegation(_) => ("取负后的向上取整", "实数 x 满足 ceil(-x) = -floor(x)"),
Self::FloorIntegerTranslation(_) => ("向下取整的整数平移", "经验证的整数位移可移出 floor"),
Self::CeilIntegerTranslation(_) => ("向上取整的整数平移", "经验证的整数位移可移出 ceil"),
Self::MinMaxAbsorption(_) => ("最小值吸收最大值", "实数操作数满足 min(a, max(a, b)) = a"),
Self::MaxMinAbsorption(_) => ("最大值吸收最小值", "实数操作数满足 max(a, min(a, b)) = a"),
Self::LcmZero(_) => ("lcm 的零参数", "lcm 的任一整数参数为零时，结果为零"),
};
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("sign 的零反射", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("有限集合最大值精確選取", "選取原有理數成員並證明每個成員不大於它"),
            Self::FiniteSetMinSelection(_) => ("有限集合最小值精確選取", "選取原有理數成員並證明每個成員不小於它"),
            Self::AbsZeroArgument(_) => ("絕對值為零", "實數的絕對值為零時，該實數等於零"),
            Self::FloorNegation(_) => ("取負後的向下取整", "實數 x 滿足 floor(-x) = -ceil(x)"),
            Self::CeilNegation(_) => ("取負後的向上取整", "實數 x 滿足 ceil(-x) = -floor(x)"),
            Self::FloorIntegerTranslation(_) => ("向下取整的整數平移", "整數位移可移出 floor"),
            Self::CeilIntegerTranslation(_) => ("向上取整的整數平移", "整數位移可移出 ceil"),
            Self::MinMaxAbsorption(_) => ("最小值吸收最大值", "實數運算元滿足 min(a, max(a, b)) = a"),
            Self::MaxMinAbsorption(_) => ("最大值吸收最小值", "實數運算元滿足 max(a, min(a, b)) = a"),
            Self::LcmZero(_) => ("lcm 的零引數", "任一整數引數為零時，最小公倍數為零"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("Réflexion du signe nul", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("Maximum exact d'un ensemble fini", "Choisir un membre rationnel original et certifier qu'aucun membre n'est plus grand"),
            Self::FiniteSetMinSelection(_) => ("Minimum exact d'un ensemble fini", "Choisir un membre rationnel original et certifier qu'aucun membre n'est plus petit"),
            Self::AbsZeroArgument(_) => ("Valeur absolue nulle", "Un réel de valeur absolue nulle est égal à zéro"),
            Self::FloorNegation(_) => ("Partie entière inférieure d'un opposé", "floor(-x) = -ceil(x) pour x réel"),
            Self::CeilNegation(_) => ("Partie entière supérieure d'un opposé", "ceil(-x) = -floor(x) pour x réel"),
            Self::FloorIntegerTranslation(_) => ("Translation entière de la partie entière inférieure", "Une translation entière commute avec floor"),
            Self::CeilIntegerTranslation(_) => ("Translation entière de la partie entière supérieure", "Une translation entière commute avec ceil"),
            Self::MinMaxAbsorption(_) => ("Le minimum absorbe le maximum", "min(a, max(a, b)) = a pour des opérandes réels"),
            Self::MaxMinAbsorption(_) => ("Le maximum absorbe le minimum", "max(a, min(a, b)) = a pour des opérandes réels"),
            Self::LcmZero(_) => ("Argument nul de lcm", "Le plus petit commun multiple est nul si l'un des arguments entiers est nul"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("Отражение нулевого знака", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("Точный максимум конечного множества", "Выбрать исходный рациональный элемент и подтвердить, что ни один элемент не больше"),
            Self::FiniteSetMinSelection(_) => ("Точный минимум конечного множества", "Выбрать исходный рациональный элемент и подтвердить, что ни один элемент не меньше"),
            Self::AbsZeroArgument(_) => ("Нулевой модуль", "Вещественное число с нулевым модулем равно нулю"),
            Self::FloorNegation(_) => ("Округление противоположного числа вниз", "floor(-x) = -ceil(x) для вещественного x"),
            Self::CeilNegation(_) => ("Округление противоположного числа вверх", "ceil(-x) = -floor(x) для вещественного x"),
            Self::FloorIntegerTranslation(_) => ("Целочисленный сдвиг округления вниз", "Округление вниз после целочисленного сдвига равно округлению вниз исходного числа плюс этот сдвиг"),
            Self::CeilIntegerTranslation(_) => ("Целочисленный сдвиг округления вверх", "Округление вверх после целочисленного сдвига равно округлению вверх исходного числа плюс этот сдвиг"),
            Self::MinMaxAbsorption(_) => ("Минимум поглощает максимум", "min(a, max(a, b)) = a для вещественных операндов"),
            Self::MaxMinAbsorption(_) => ("Максимум поглощает минимум", "max(a, min(a, b)) = a для вещественных операндов"),
            Self::LcmZero(_) => ("Нулевой аргумент lcm", "Наименьшее общее кратное равно нулю, если один из целых аргументов равен нулю"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("Reflexión del signo cero", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("Máximo exacto de conjunto finito", "Elegir un miembro racional original y certificar que ningún miembro es mayor"),
            Self::FiniteSetMinSelection(_) => ("Mínimo exacto de conjunto finito", "Elegir un miembro racional original y certificar que ningún miembro es menor"),
            Self::AbsZeroArgument(_) => ("Valor absoluto cero", "Un número real de valor absoluto cero es igual a cero"),
            Self::FloorNegation(_) => ("Piso de una negación", "floor(-x) = -ceil(x) para x real"),
            Self::CeilNegation(_) => ("Techo de una negación", "ceil(-x) = -floor(x) para x real"),
            Self::FloorIntegerTranslation(_) => ("Traslación entera del piso", "Una traslación entera conmuta con floor"),
            Self::CeilIntegerTranslation(_) => ("Traslación entera del techo", "Una traslación entera conmuta con ceil"),
            Self::MinMaxAbsorption(_) => ("El mínimo absorbe el máximo", "min(a, max(a, b)) = a para operandos reales"),
            Self::MaxMinAbsorption(_) => ("El máximo absorbe el mínimo", "max(a, min(a, b)) = a para operandos reales"),
            Self::LcmZero(_) => ("Argumento cero de lcm", "El mínimo común múltiplo es cero si cualquiera de los argumentos enteros es cero"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("انعكاس الإشارة الصفرية", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("قيمة عظمى دقيقة لمجموعة منتهية", "اختيار عنصر نسبي أصلي وإثبات أن كل عنصر لا يزيد عليه"),
            Self::FiniteSetMinSelection(_) => ("قيمة صغرى دقيقة لمجموعة منتهية", "اختيار عنصر نسبي أصلي وإثبات أن كل عنصر لا يقل عنه"),
            Self::AbsZeroArgument(_) => ("قيمة مطلقة صفرية", "العدد الحقيقي ذو القيمة المطلقة الصفرية يساوي صفرًا"),
            Self::FloorNegation(_) => ("التقريب لأسفل للعدد المعاكس", "floor(-x) = -ceil(x) للعدد الحقيقي x"),
            Self::CeilNegation(_) => ("التقريب لأعلى للعدد المعاكس", "ceil(-x) = -floor(x) للعدد الحقيقي x"),
            Self::FloorIntegerTranslation(_) => ("إزاحة صحيحة للتقريب لأسفل", "التقريب لأسفل بعد إزاحة صحيحة يساوي التقريب لأسفل للقيمة الأصلية مضافًا إليه مقدار الإزاحة"),
            Self::CeilIntegerTranslation(_) => ("إزاحة صحيحة للتقريب لأعلى", "التقريب لأعلى بعد إزاحة صحيحة يساوي التقريب لأعلى للقيمة الأصلية مضافًا إليه مقدار الإزاحة"),
            Self::MinMaxAbsorption(_) => ("القيمة الصغرى تمتص القيمة العظمى", "min(a, max(a, b)) = a للمعاملات الحقيقية"),
            Self::MaxMinAbsorption(_) => ("القيمة العظمى تمتص القيمة الصغرى", "max(a, min(a, b)) = a للمعاملات الحقيقية"),
            Self::LcmZero(_) => ("وسيط صفري لـ lcm", "المضاعف المشترك الأصغر يساوي صفرًا إذا كان أحد الوسيطين الصحيحين صفرًا"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("符号がゼロなら引数もゼロ", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("有限集合の正確な最大値", "元の有理数の要素を選び、すべての要素がそれ以下であることを証明します"),
            Self::FiniteSetMinSelection(_) => ("有限集合の正確な最小値", "元の有理数の要素を選び、すべての要素がそれ以上であることを証明します"),
            Self::AbsZeroArgument(_) => ("絶対値がゼロ", "絶対値がゼロである実数はゼロです"),
            Self::FloorNegation(_) => ("符号反転の床関数", "実数 x について floor(-x) = -ceil(x)"),
            Self::CeilNegation(_) => ("符号反転の天井関数", "実数 x について ceil(-x) = -floor(x)"),
            Self::FloorIntegerTranslation(_) => ("床関数の整数平行移動", "整数の平行移動は floor と可換です"),
            Self::CeilIntegerTranslation(_) => ("天井関数の整数平行移動", "整数の平行移動は ceil と可換です"),
            Self::MinMaxAbsorption(_) => ("最小値による最大値の吸収", "実数の被演算子について min(a, max(a, b)) = a"),
            Self::MaxMinAbsorption(_) => ("最大値による最小値の吸収", "実数の被演算子について max(a, min(a, b)) = a"),
            Self::LcmZero(_) => ("lcm のゼロ引数", "整数引数のいずれかがゼロなら最小公倍数はゼロです"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("영인 부호의 반영", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("유한 집합의 정확한 최댓값", "원래의 유리수 원소를 선택하고 모든 원소가 그보다 크지 않음을 인증합니다"),
            Self::FiniteSetMinSelection(_) => ("유한 집합의 정확한 최솟값", "원래의 유리수 원소를 선택하고 모든 원소가 그보다 작지 않음을 인증합니다"),
            Self::AbsZeroArgument(_) => ("절댓값이 0", "절댓값이 0인 실수는 0입니다"),
            Self::FloorNegation(_) => ("부호 반전의 바닥 함수", "실수 x에 대해 floor(-x) = -ceil(x)"),
            Self::CeilNegation(_) => ("부호 반전의 천장 함수", "실수 x에 대해 ceil(-x) = -floor(x)"),
            Self::FloorIntegerTranslation(_) => ("바닥 함수의 정수 평행이동", "정수 평행이동은 floor와 교환됩니다"),
            Self::CeilIntegerTranslation(_) => ("천장 함수의 정수 평행이동", "정수 평행이동은 ceil과 교환됩니다"),
            Self::MinMaxAbsorption(_) => ("최솟값의 최댓값 흡수", "실수 피연산자에 대해 min(a, max(a, b)) = a"),
            Self::MaxMinAbsorption(_) => ("최댓값의 최솟값 흡수", "실수 피연산자에 대해 max(a, min(a, b)) = a"),
            Self::LcmZero(_) => ("lcm의 0 인수", "정수 인수 중 하나가 0이면 최소공배수는 0입니다"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::SignZeroReflection(_) => ("Phản ánh dấu bằng không", "x in R: sign(x)=0 => x=0"),
            Self::FiniteSetMaxSelection(_) => ("Giá trị lớn nhất chính xác của tập hữu hạn", "Chọn phần tử hữu tỉ gốc và chứng nhận mọi phần tử không lớn hơn nó"),
            Self::FiniteSetMinSelection(_) => ("Giá trị nhỏ nhất chính xác của tập hữu hạn", "Chọn phần tử hữu tỉ gốc và chứng nhận mọi phần tử không nhỏ hơn nó"),
            Self::AbsZeroArgument(_) => ("Giá trị tuyệt đối bằng không", "Số thực có giá trị tuyệt đối bằng không thì bằng không"),
            Self::FloorNegation(_) => ("Hàm sàn của số đối", "floor(-x) = -ceil(x) với x thực"),
            Self::CeilNegation(_) => ("Hàm trần của số đối", "ceil(-x) = -floor(x) với x thực"),
            Self::FloorIntegerTranslation(_) => ("Tịnh tiến nguyên của hàm sàn", "Tịnh tiến nguyên giao hoán với floor"),
            Self::CeilIntegerTranslation(_) => ("Tịnh tiến nguyên của hàm trần", "Tịnh tiến nguyên giao hoán với ceil"),
            Self::MinMaxAbsorption(_) => ("Giá trị nhỏ nhất hấp thụ giá trị lớn nhất", "min(a, max(a, b)) = a với các toán hạng thực"),
            Self::MaxMinAbsorption(_) => ("Giá trị lớn nhất hấp thụ giá trị nhỏ nhất", "max(a, min(a, b)) = a với các toán hạng thực"),
            Self::LcmZero(_) => ("Đối số không của lcm", "Bội chung nhỏ nhất bằng không khi một trong hai đối số nguyên bằng không"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("Complex modulus coordinates", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("Real part of a quotient", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("Imaginary part of a quotient", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("Tangent-cotangent product", "For real x with sin(x) and cos(x) nonzero: tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("Tangent square identity", "For real x with cos(x) nonzero: 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("Cosine double angle", "For checked real x: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("Sine reflection about pi/2", "For checked real x: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("Cosine reflection about pi/2", "For checked real x: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("Sine complementary angle", "For checked real x: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("Cosine complementary angle", "For checked real x: cos(pi/2-x)=sin(x)"),
Self::SinHalfPiShift(_) => ("Sine quarter-turn shift", "sin(x+pi/2)=cos(x) for checked real x"),
Self::CosHalfPiShift(_) => ("Cosine quarter-turn shift", "cos(x+pi/2)=-sin(x) for checked real x"),
Self::PeriodicTrig(_) => ("Exact periodic trigonometric value", "Reduce the exact pi coefficient using checked integer periods"),
Self::NumericComplexModulus(_) => ("Exact numeric complex modulus", "Compute exact real/imaginary coordinates and take the nonnegative principal root"),
Self::SinDifference => ("Sine difference formula", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) for checked real arguments"),
Self::CosDifference => ("Cosine difference formula", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) for checked real arguments"),
Self::ComplexModulusProduct => ("Multiplicativity of complex modulus", "C_abs(z*w)=C_abs(z)*C_abs(w) for checked complex arguments"),
Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("Trigonometric or complex coordinate identity", "Apply the trigonometric or complex coordinate identity with checked premises"),
};
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("复数模的坐标公式", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("复数商的实部", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("复数商的虚部", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("正切余切乘积", "实数 x 的 sin(x)、cos(x) 非零时：tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("正切平方恒等式", "实数 x 的 cos(x) 非零时：1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("余弦倍角公式", "经验证的实数 x 满足：cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("正弦的 pi 反射", "经验证的实数 x 满足：sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("余弦的 pi 反射", "经验证的实数 x 满足：cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("正弦余角公式", "经验证的实数 x 满足：sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("余弦余角公式", "经验证的实数 x 满足：cos(pi/2-x)=sin(x)"),
Self::SinHalfPiShift(_) => ("正弦的半 pi 平移", "经验证的实数 x 满足 sin(x+pi/2)=cos(x)"),
Self::CosHalfPiShift(_) => ("余弦的半 pi 平移", "经验证的实数 x 满足 cos(x+pi/2)=-sin(x)"),
Self::PeriodicTrig(_) => ("精确周期三角值", "依据已验证的整数周期归约精确 pi 系数"),
Self::NumericComplexModulus(_) => ("数字复数模长精确计算", "精确计算实部与虚部并取非负主根"),
Self::SinDifference => ("正弦差角公式", "经验证的实数参数满足 sin(x-y)=sin(x)cos(y)-cos(x)sin(y)"),
Self::CosDifference => ("余弦差角公式", "经验证的实数参数满足 cos(x-y)=cos(x)cos(y)+sin(x)sin(y)"),
Self::ComplexModulusProduct => ("复数模的乘法公式", "经验证的复数参数满足 C_abs(z*w)=C_abs(z)*C_abs(w)"),
Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("三角或复坐标恒等式", "依据已验证的前提应用三角或复坐标恒等式"),
};
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("複數模的座標公式", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("複數商的實部", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("複數商的虛部", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("正切餘切乘積", "實數 x 的 sin(x)、cos(x) 非零時：tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("正切平方恆等式", "實數 x 的 cos(x) 非零時：1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("餘弦倍角公式", "經驗證的實數 x 滿足：cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("正弦的 pi 反射", "經驗證的實數 x 滿足：sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("餘弦的 pi 反射", "經驗證的實數 x 滿足：cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("正弦餘角公式", "經驗證的實數 x 滿足：sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("餘弦餘角公式", "經驗證的實數 x 滿足：cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("正弦的半 pi 平移", "經驗證的實數 x 滿足 sin(x+pi/2)=cos(x)"),
            Self::CosHalfPiShift(_) => ("餘弦的半 pi 平移", "經驗證的實數 x 滿足 cos(x+pi/2)=-sin(x)"),
            Self::PeriodicTrig(_) => ("精確週期三角值", "以已驗證的整數週期歸約精確 pi 係數"),
            Self::NumericComplexModulus(_) => ("數值複數模長精確計算", "精確計算實部與虛部並取非負主根"),
            Self::SinDifference => ("正弦差角公式", "經驗證的實數引數滿足 sin(x-y)=sin(x)cos(y)-cos(x)sin(y)"),
            Self::CosDifference => ("餘弦差角公式", "經驗證的實數引數滿足 cos(x-y)=cos(x)cos(y)+sin(x)sin(y)"),
            Self::ComplexModulusProduct => ("複數模的乘法公式", "經驗證的複數引數滿足 C_abs(z*w)=C_abs(z)*C_abs(w)"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("三角或複數座標恆等式", "依已驗證的前提套用三角或複數座標恆等式"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("Coordonnées du module complexe", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("Partie réelle du quotient", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("Partie imaginaire du quotient", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("Produit tangente-cotangente", "Pour x réel, sin(x) et cos(x) non nuls : tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("Identité du carré de la tangente", "Pour x réel avec cos(x) non nul : 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("Angle double du cosinus", "Pour x réel vérifié : cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("Réflexion du sinus en pi/2", "Pour x réel vérifié : sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("Réflexion du cosinus en pi/2", "Pour x réel vérifié : cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("Angle complémentaire du sinus", "Pour x réel vérifié : sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("Angle complémentaire du cosinus", "Pour x réel vérifié : cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("Translation d'un quart de tour du sinus", "sin(x+pi/2)=cos(x) pour x réel vérifié"),
            Self::CosHalfPiShift(_) => ("Translation d'un quart de tour du cosinus", "cos(x+pi/2)=-sin(x) pour x réel vérifié"),
            Self::PeriodicTrig(_) => ("Valeur trigonométrique périodique exacte", "Réduire le coefficient exact de pi avec des périodes entières vérifiées"),
            Self::NumericComplexModulus(_) => ("Module complexe numérique exact", "Calculer les coordonnées réelles et imaginaires exactes et prendre la racine principale non négative"),
            Self::SinDifference => ("Formule du sinus d'une différence", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) pour des arguments réels vérifiés"),
            Self::CosDifference => ("Formule du cosinus d'une différence", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) pour des arguments réels vérifiés"),
            Self::ComplexModulusProduct => ("Multiplicativité du module complexe", "C_abs(z*w)=C_abs(z)*C_abs(w) pour des arguments complexes vérifiés"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("Identité trigonométrique ou de coordonnées complexes", "Appliquer l'identité trigonométrique ou de coordonnées complexes avec les prémisses vérifiées"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("Координаты модуля комплексного числа", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("Действительная часть частного", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("Мнимая часть частного", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("Произведение тангенса и котангенса", "Для вещественного x при ненулевых sin(x) и cos(x): tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("Квадрат тангенса", "Для вещественного x при ненулевом cos(x): 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("Двойной угол косинуса", "Для проверенного вещественного x: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("Отражение синуса относительно pi/2", "Для проверенного вещественного x: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("Отражение косинуса относительно pi/2", "Для проверенного вещественного x: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("Дополнительный угол синуса", "Для проверенного вещественного x: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("Дополнительный угол косинуса", "Для проверенного вещественного x: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("Сдвиг синуса на четверть оборота", "sin(x+pi/2)=cos(x) для проверенного вещественного x"),
            Self::CosHalfPiShift(_) => ("Сдвиг косинуса на четверть оборота", "cos(x+pi/2)=-sin(x) для проверенного вещественного x"),
            Self::PeriodicTrig(_) => ("Точное периодическое тригонометрическое значение", "Сократить точный коэффициент pi по проверенным целочисленным периодам"),
            Self::NumericComplexModulus(_) => ("Точный модуль числового комплексного значения", "Точно вычислить действительную и мнимую координаты и взять неотрицательный главный корень"),
            Self::SinDifference => ("Формула синуса разности", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) для проверенных вещественных аргументов"),
            Self::CosDifference => ("Формула косинуса разности", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) для проверенных вещественных аргументов"),
            Self::ComplexModulusProduct => ("Мультипликативность комплексного модуля", "C_abs(z*w)=C_abs(z)*C_abs(w) для проверенных комплексных аргументов"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("Тригонометрическое или комплексное координатное тождество", "Применить тригонометрическое или комплексное координатное тождество с проверенными предпосылками"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("Coordenadas del módulo complejo", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("Parte real de un cociente", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("Parte imaginaria de un cociente", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("Producto tangente-cotangente", "Para x real con sin(x) y cos(x) distintos de cero: tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("Identidad del cuadrado de la tangente", "Para x real con cos(x) distinto de cero: 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("Ángulo doble del coseno", "Para x real comprobado: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("Reflexión del seno respecto a pi/2", "Para x real comprobado: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("Reflexión del coseno respecto a pi/2", "Para x real comprobado: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("Ángulo complementario del seno", "Para x real comprobado: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("Ángulo complementario del coseno", "Para x real comprobado: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("Desplazamiento de un cuarto de vuelta del seno", "sin(x+pi/2)=cos(x) para x real comprobado"),
            Self::CosHalfPiShift(_) => ("Desplazamiento de un cuarto de vuelta del coseno", "cos(x+pi/2)=-sin(x) para x real comprobado"),
            Self::PeriodicTrig(_) => ("Valor trigonométrico periódico exacto", "Reducir el coeficiente exacto de pi usando períodos enteros comprobados"),
            Self::NumericComplexModulus(_) => ("Módulo complejo numérico exacto", "Calcular las coordenadas reales e imaginarias exactas y tomar la raíz principal no negativa"),
            Self::SinDifference => ("Fórmula del seno de una diferencia", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) para argumentos reales comprobados"),
            Self::CosDifference => ("Fórmula del coseno de una diferencia", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) para argumentos reales comprobados"),
            Self::ComplexModulusProduct => ("Multiplicatividad del módulo complejo", "C_abs(z*w)=C_abs(z)*C_abs(w) para argumentos complejos comprobados"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("Identidad trigonométrica o de coordenadas complejas", "Aplicar la identidad trigonométrica o de coordenadas complejas con premisas comprobadas"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("إحداثيات معيار العدد المركب", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("الجزء الحقيقي للقسمة", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("الجزء التخيلي للقسمة", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("حاصل ضرب الظل وظل التمام", "للعدد الحقيقي x عندما sin(x) وcos(x) غير صفريين: tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("متطابقة مربع الظل", "للعدد الحقيقي x عندما cos(x) غير صفري: 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("الزاوية المضاعفة لجيب التمام", "للعدد الحقيقي x المتحقق منه: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("انعكاس الجيب حول pi/2", "للعدد الحقيقي x المتحقق منه: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("انعكاس جيب التمام حول pi/2", "للعدد الحقيقي x المتحقق منه: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("الزاوية المتممة للجيب", "للعدد الحقيقي x المتحقق منه: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("الزاوية المتممة لجيب التمام", "للعدد الحقيقي x المتحقق منه: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("إزاحة الجيب بربع دورة", "sin(x+pi/2)=cos(x) للعدد الحقيقي x المتحقق منه"),
            Self::CosHalfPiShift(_) => ("إزاحة جيب التمام بربع دورة", "cos(x+pi/2)=-sin(x) للعدد الحقيقي x المتحقق منه"),
            Self::PeriodicTrig(_) => ("قيمة مثلثية دورية دقيقة", "اختزال معامل pi الدقيق باستخدام دورات صحيحة متحقق منها"),
            Self::NumericComplexModulus(_) => ("مقياس مركب عددي دقيق", "حساب الإحداثيين الحقيقي والتخيلي بدقة وأخذ الجذر الرئيسي غير السالب"),
            Self::SinDifference => ("صيغة جيب الفرق", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) للوسائط الحقيقية المتحقق منها"),
            Self::CosDifference => ("صيغة جيب تمام الفرق", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) للوسائط الحقيقية المتحقق منها"),
            Self::ComplexModulusProduct => ("ضربية المقياس المركب", "C_abs(z*w)=C_abs(z)*C_abs(w) للوسائط المركبة المتحقق منها"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("هوية مثلثية أو إحداثيات مركبة", "تطبيق الهوية المثلثية أو هوية الإحداثيات المركبة بالمقدمات المتحقق منها"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("複素数の絶対値の座標式", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("複素数の商の実部", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("複素数の商の虚部", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("正接と余接の積", "実数 x で sin(x) と cos(x) が非零なら tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("正接の平方恒等式", "実数 x で cos(x) が非零なら 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("余弦の倍角公式", "検証済みの実数 x について: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("pi/2 に関する正弦の反転", "検証済みの実数 x について: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("pi/2 に関する余弦の反転", "検証済みの実数 x について: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("正弦の余角公式", "検証済みの実数 x について: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("余弦の余角公式", "検証済みの実数 x について: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("正弦の四分の一回転の平行移動", "検証済みの実数 x について sin(x+pi/2)=cos(x)"),
            Self::CosHalfPiShift(_) => ("余弦の四分の一回転の平行移動", "検証済みの実数 x について cos(x+pi/2)=-sin(x)"),
            Self::PeriodicTrig(_) => ("正確な周期的三角関数値", "検証済みの整数周期を用いて正確な pi の係数を簡約します"),
            Self::NumericComplexModulus(_) => ("数値的複素数の正確な絶対値", "実部と虚部を正確に計算し、非負の主平方根を取ります"),
            Self::SinDifference => ("正弦の差角公式", "検証済みの実数引数について sin(x-y)=sin(x)cos(y)-cos(x)sin(y)"),
            Self::CosDifference => ("余弦の差角公式", "検証済みの実数引数について cos(x-y)=cos(x)cos(y)+sin(x)sin(y)"),
            Self::ComplexModulusProduct => ("複素数の絶対値の乗法性", "検証済みの複素数引数について C_abs(z*w)=C_abs(z)*C_abs(w)"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("三角関数または複素座標の恒等式", "検証済みの前提で三角関数または複素座標の恒等式を適用します"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("복소수 절댓값의 좌표식", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("복소수 몫의 실수부", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("복소수 몫의 허수부", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("탄젠트와 코탄젠트의 곱", "실수 x에서 sin(x), cos(x)가 0이 아니면 tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("탄젠트 제곱 항등식", "실수 x에서 cos(x)가 0이 아니면 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("코사인 배각 공식", "검증된 실수 x에 대해: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("pi/2에 대한 사인 반사", "검증된 실수 x에 대해: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("pi/2에 대한 코사인 반사", "검증된 실수 x에 대해: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("사인의 여각 공식", "검증된 실수 x에 대해: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("코사인의 여각 공식", "검증된 실수 x에 대해: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("사인의 4분의 1회전 이동", "검증된 실수 x에 대해 sin(x+pi/2)=cos(x)"),
            Self::CosHalfPiShift(_) => ("코사인의 4분의 1회전 이동", "검증된 실수 x에 대해 cos(x+pi/2)=-sin(x)"),
            Self::PeriodicTrig(_) => ("정확한 주기 삼각함숫값", "검증된 정수 주기로 정확한 pi 계수를 축약합니다"),
            Self::NumericComplexModulus(_) => ("수치 복소수의 정확한 절댓값", "실수부와 허수부를 정확하게 계산하고 음이 아닌 주 제곱근을 취합니다"),
            Self::SinDifference => ("사인 차각 공식", "검증된 실수 인수에 대해 sin(x-y)=sin(x)cos(y)-cos(x)sin(y)"),
            Self::CosDifference => ("코사인 차각 공식", "검증된 실수 인수에 대해 cos(x-y)=cos(x)cos(y)+sin(x)sin(y)"),
            Self::ComplexModulusProduct => ("복소수 절댓값의 곱셈성", "검증된 복소수 인수에 대해 C_abs(z*w)=C_abs(z)*C_abs(w)"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("삼각함수 또는 복소수 좌표 항등식", "검증된 전제로 삼각함수 또는 복소수 좌표 항등식을 적용합니다"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        let (name, message) = match self {
            Self::ComplexModulusCoordinates(_) => ("Tọa độ môđun số phức", "z in C: C_abs(z)=sqrt(re(z)^2+img(z)^2)"),
            Self::RealPartQuotient(_) => ("Phần thực của thương", "z,w in C, w!=0: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2"),
            Self::ImaginaryPartQuotient(_) => ("Phần ảo của thương", "z,w in C, w!=0: img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2"),
            Self::TanCotProduct(_) => ("Tích tang và côtang", "Với x thực, sin(x) và cos(x) khác 0: tan(x)*cot(x)=1"),
            Self::TanSquareReciprocalCosine(_) => ("Đẳng thức bình phương tang", "Với x thực, cos(x) khác 0: 1+tan(x)^2=1/cos(x)^2"),
            Self::CosDoubleAngle(_) => ("Góc kép của cos", "Với x thực đã kiểm tra: cos(2*x)=cos(x)^2-sin(x)^2=1-2*sin(x)^2=2*cos(x)^2-1"),
            Self::SinPiReflection(_) => ("Phản xạ sin qua pi/2", "Với x thực đã kiểm tra: sin(pi-x)=sin(x)"),
            Self::CosPiReflection(_) => ("Phản xạ cos qua pi/2", "Với x thực đã kiểm tra: cos(pi-x)=-cos(x)"),
            Self::SinHalfPiReflection(_) => ("Góc phụ của sin", "Với x thực đã kiểm tra: sin(pi/2-x)=cos(x)"),
            Self::CosHalfPiReflection(_) => ("Góc phụ của cos", "Với x thực đã kiểm tra: cos(pi/2-x)=sin(x)"),
            Self::SinHalfPiShift(_) => ("Dịch sin một phần tư vòng", "sin(x+pi/2)=cos(x) với x thực đã kiểm tra"),
            Self::CosHalfPiShift(_) => ("Dịch cos một phần tư vòng", "cos(x+pi/2)=-sin(x) với x thực đã kiểm tra"),
            Self::PeriodicTrig(_) => ("Giá trị lượng giác tuần hoàn chính xác", "Rút gọn hệ số pi chính xác bằng các chu kỳ nguyên đã kiểm tra"),
            Self::NumericComplexModulus(_) => ("Môđun phức dạng số chính xác", "Tính chính xác tọa độ thực và ảo rồi lấy căn chính không âm"),
            Self::SinDifference => ("Công thức sin hiệu", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) với các đối số thực đã kiểm tra"),
            Self::CosDifference => ("Công thức cos hiệu", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) với các đối số thực đã kiểm tra"),
            Self::ComplexModulusProduct => ("Tính nhân của môđun phức", "C_abs(z*w)=C_abs(z)*C_abs(w) với các đối số phức đã kiểm tra"),
            Self::SinNegation | Self::CosNegation | Self::SinPiShift | Self::CosPiShift | Self::SinDoubleAngle | Self::ComplexReconstruction | Self::RealPartAddition | Self::ImaginaryPartAddition | Self::RealPartSubtraction | Self::ImaginaryPartSubtraction | Self::ComplexPowerCoordinates { .. } | Self::ComplexModulusZero { .. } | Self::ComplexCoordinatesEqual { .. } => ("Đồng nhất thức lượng giác hoặc tọa độ phức", "Áp dụng đồng nhất thức lượng giác hoặc tọa độ phức với các tiền đề đã kiểm tra"),
        };
        BuiltinRuleText {rule_name: name.into(), message: message.into()}
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
