//! Leaf proof structs: ten locale methods and a language selector.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{
    ArccosCosRightInverseBuiltinRuleProof, ArccosExactNegOneBuiltinRuleProof,
    ArccosExactOneBuiltinRuleProof, ArccosExactZeroBuiltinRuleProof,
    ArccotCotRightInverseBuiltinRuleProof, ArccotExactZeroBuiltinRuleProof,
    ArcsinExactNegOneBuiltinRuleProof, ArcsinExactOneBuiltinRuleProof,
    ArcsinExactZeroBuiltinRuleProof, ArcsinSinRightInverseBuiltinRuleProof,
    ArctanExactZeroBuiltinRuleProof, ArctanTanRightInverseBuiltinRuleProof,
    CosArccosLeftInverseBuiltinRuleProof, CotArccotLeftInverseBuiltinRuleProof,
    SinArcsinLeftInverseBuiltinRuleProof, TanArctanLeftInverseBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave2::{
    AbsOfNegationBuiltinRuleProof, AbsProductBuiltinRuleProof, AbsSquareBuiltinRuleProof,
    LogArgPowerBuiltinRuleProof, LogBaseSelfBuiltinRuleProof, LogChangeOfBaseBuiltinRuleProof,
    LogOfOneBuiltinRuleProof, LogOfPowerSameBaseBuiltinRuleProof, LogProductBuiltinRuleProof,
    LogQuotientBuiltinRuleProof, LogReciprocalBuiltinRuleProof, ModOneBuiltinRuleProof,
    NestedSameModAbsorptionBuiltinRuleProof, ModCompatibleSmallerModulusBuiltinRuleProof,
    OneModAtLeastTwoBuiltinRuleProof,
    OneToAnyPowerBuiltinRuleProof, SqrtOfSquareBuiltinRuleProof, SqrtOneBuiltinRuleProof,
    SqrtProductBuiltinRuleProof, SqrtQuotientBuiltinRuleProof, SqrtSquareBuiltinRuleProof,
    SqrtZeroBuiltinRuleProof, ZeroModBuiltinRuleProof, ZeroToPosNatPowerBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave3::{
    AbsAbsAbsorptionBuiltinRuleProof, CeilOfIntegerBuiltinRuleProof, ExpOfLnBuiltinRuleProof,
    FloorOfIntegerBuiltinRuleProof, LnOfExpBuiltinRuleProof, MaxCommutativeBuiltinRuleProof,
    MaxIdempotentBuiltinRuleProof, MinCommutativeBuiltinRuleProof, MinIdempotentBuiltinRuleProof,
    ModSelfZeroBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave4::{
    CeilOfFloorOfIntegerBuiltinRuleProof, FloorOfCeilOfIntegerBuiltinRuleProof,
    SqrtOfSquareEqualsAbsBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave5::{
    FactorialSuccessorBuiltinRuleProof, GcdCommutativeBuiltinRuleProof,
    GcdIdempotentAbsBuiltinRuleProof, GcdLeftZeroAbsBuiltinRuleProof,
    GcdRightZeroAbsBuiltinRuleProof, LcmCommutativeBuiltinRuleProof,
    LcmIdempotentAbsBuiltinRuleProof, QuotByOneBuiltinRuleProof, QuotSelfOneBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave6::{
    AbsNonnegEqualsSelfBuiltinRuleProof, AbsNonposEqualsNegationBuiltinRuleProof,
    MaxLeftWhenLessEqualBuiltinRuleProof, MaxRightWhenLessEqualBuiltinRuleProof,
    MinLeftWhenLessEqualBuiltinRuleProof, MinRightWhenLessEqualBuiltinRuleProof,
    SignOfNegativeBuiltinRuleProof, SignOfPositiveBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave7::{
    AbsEqualsSignTimesArgBuiltinRuleProof, DiffZeroFromEqualOperandsBuiltinRuleProof,
    EqualityFromTwoSidedWeakOrderBuiltinRuleProof, GcdDividesArgumentBuiltinRuleProof,
    ProductModFactorZeroBuiltinRuleProof, SignOfNegationBuiltinRuleProof,
    SignOfProductBuiltinRuleProof, SignTimesAbsEqualsArgBuiltinRuleProof,
    SubtractionFromKnownAdditionBuiltinRuleProof, ZeroProductCancelBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equal_from_known_difference_zero::EqualFromKnownDifferenceZeroBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave8::{
    LcmGcdProductAbsBuiltinRuleProof, MinusOneOddNaturalPowerBuiltinRuleProof,
    ModDividendMinusRemainderZeroBuiltinRuleProof, QuotEuclideanDecompositionBuiltinRuleProof,
    SquareSumComponentZeroBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave9::{
    EmptySetFromNotNonemptyBuiltinRuleProof, IntersectAssociativeBuiltinRuleProof,
    IntersectCommutativeBuiltinRuleProof, IntersectEmptyLeftBuiltinRuleProof,
    IntersectEmptyRightBuiltinRuleProof, IntersectFromSubsetBuiltinRuleProof,
    IntersectIdempotentBuiltinRuleProof, IntersectSetMinusSelfEmptyBuiltinRuleProof,
    IntersectUnionDistributiveBuiltinRuleProof, PowerSetFiniteSetSizeBuiltinRuleProof,
    SetMinusEmptyLeftBuiltinRuleProof, SetMinusEmptyRightBuiltinRuleProof,
    SetMinusIntersectDeMorganBuiltinRuleProof, SetMinusSelfEmptyBuiltinRuleProof,
    SetMinusUnionDeMorganBuiltinRuleProof, UnionAssociativeBuiltinRuleProof,
    UnionCommutativeBuiltinRuleProof, UnionEmptyLeftBuiltinRuleProof,
    UnionEmptyRightBuiltinRuleProof, UnionIdempotentBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave10::{
    FiniteSetProductEmptyBuiltinRuleProof, FiniteSetReduceEmptyBuiltinRuleProof,
    FiniteSetSumEmptyBuiltinRuleProof, ProductEmptyRangeBuiltinRuleProof,
    ReduceEmptyBuiltinRuleProof, SumEmptyRangeBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave11::{
    ClosedRangeSingletonListSetBuiltinRuleProof,
    EmptySetFromSizeZeroBuiltinRuleProof, FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof,
    FiniteSetSizeSetMinusBuiltinRuleProof, FiniteSetSizeUnionBuiltinRuleProof,
    PowOfLogInverseBuiltinRuleProof, ProductSingleTermBuiltinRuleProof,
    ReduceAddZeroEqualsSumBuiltinRuleProof, SetMinusRecoversSubsetBuiltinRuleProof,
    SumSingleTermBuiltinRuleProof, UnionAbsorptionFromSubsetBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave12::{
    ComplexAbsOfImaginaryUnitBuiltinRuleProof, FiniteSetProductListExpansionBuiltinRuleProof,
    FiniteSetSumListExpansionBuiltinRuleProof, ImgOfImaginaryUnitBuiltinRuleProof,
    ImgOfRealEmbeddingBuiltinRuleProof, ImgOfRealPlusIBuiltinRuleProof,
    ModNestedDivisibleAbsorptionBuiltinRuleProof, ProductSplitLastTermBuiltinRuleProof,
    ReOfImaginaryUnitBuiltinRuleProof, ReOfRealEmbeddingBuiltinRuleProof,
    ReOfRealPlusIBuiltinRuleProof, SetMinusIntersectSelfBuiltinRuleProof,
    SumSplitLastTermBuiltinRuleProof, UnionSetMinusDecompositionBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave13::{
    CartWithEmptyFactorBuiltinRuleProof, ClosedRangeLiteralExpansionBuiltinRuleProof,
    ComplexAbsOfImagScaledBuiltinRuleProof, ComplexAbsOfNonnegRealBuiltinRuleProof,
    EulerEqualsExpOneBuiltinRuleProof, FamilyUnionOfEmptyBuiltinRuleProof, FamilyUnionOfSingletonBuiltinRuleProof, FamilyUnionOfPowerSetBuiltinRuleProof,
    FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof, FnRangeOfConstantAnonymousFnBuiltinRuleProof,
    ImgOfRealBuiltinRuleProof, ImgOfRealPlusImagScaledBuiltinRuleProof,
    LnOfEulerBuiltinRuleProof, PowerSetOfEmptyBuiltinRuleProof,
    PowerSetOfSingletonBuiltinRuleProof, RangeLiteralExpansionBuiltinRuleProof,
    ReOfRealBuiltinRuleProof, ReOfRealPlusImagScaledBuiltinRuleProof,
    SeqEqualsFnOnNPosBuiltinRuleProof, SetMinusChainToUnionBuiltinRuleProof,
    UnionOverIntersectDistributiveBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave14::{
    ComplexAbsSquaredOfRectFormBuiltinRuleProof, CosOfSumBuiltinRuleProof,
    ExpOfSumBuiltinRuleProof, FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof,
    ImgOfProductBuiltinRuleProof, IndexCartEmptyIndexBuiltinRuleProof,
    IndexIntersectEmptyIndexBuiltinRuleProof, IndexUnionEmptyIndexBuiltinRuleProof,
    IndexUnionSingletonBuiltinRuleProof, LogBasePowerBuiltinRuleProof,
    ReduceSingleTermWithAddZeroBuiltinRuleProof, ReOfProductBuiltinRuleProof,
    SetBuilderObviouslyEmptyBuiltinRuleProof, SinOfSumBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave15::{
    FiniteSetSumFubiniSwapBuiltinRuleProof, FiniteSetSumOverCartesianProductBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_closed_trig::{
    CosOfPiBuiltinRuleProof, CosOfZeroBuiltinRuleProof, CotOfHalfPiBuiltinRuleProof,
    PythagoreanIdentityBuiltinRuleProof, SinOfHalfPiBuiltinRuleProof, SinOfPiBuiltinRuleProof,
    SinOfZeroBuiltinRuleProof,
    TanOfZeroBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_power_laws::{
    PowerOfPowerBuiltinRuleProof, PowerOfProductBuiltinRuleProof,
    PowerProductSameBaseBuiltinRuleProof, QuotientAsMulNegOnePowerBuiltinRuleProof,
    ReciprocalAsNegOnePowerBuiltinRuleProof
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::json_output::explain::text::text;

impl SinArcsinLeftInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of sin and arcsin",
            "On [-1, 1], composing sin with arcsin returns the original argument: sin(arcsin(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "sin与arcsin的逆运算复合",
            "在 [-1, 1] 上，sin与arcsin复合后得到原参数，即 sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "sin與arcsin的逆運算複合",
            "在 [-1, 1] 上，sin與arcsin複合後得到原引數，即 sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de sin et arcsin",
            "Sur [-1, 1], la composition de sin avec arcsin restitue l’argument initial: sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция sin и arcsin",
            "На [-1, 1] композиция sin с arcsin возвращает исходный аргумент: sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de sin y arcsin",
            "En [-1, 1], componer sin con arcsin devuelve el argumento original: sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ sin وarcsin",
            "على [-1, 1]، يعيد تركيب sin مع arcsin الوسيط الأصلي: sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "sinとarcsinの逆演算の合成",
            "[-1, 1] 上では、sinとarcsinの合成により元の引数が得られます：sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "sin와 arcsin의 역연산 합성",
            "[-1, 1]에서 sin와 arcsin를 합성하면 원래 인수를 얻습니다: sin(arcsin(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của sin và arcsin",
            "Trên [-1, 1], hợp thành sin với arcsin trả về đối số ban đầu: sin(arcsin(x)) = x",
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

impl CosArccosLeftInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of cos and arccos",
            "On [-1, 1], composing cos with arccos returns the original argument: cos(arccos(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "cos与arccos的逆运算复合",
            "在 [-1, 1] 上，cos与arccos复合后得到原参数，即 cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "cos與arccos的逆運算複合",
            "在 [-1, 1] 上，cos與arccos複合後得到原引數，即 cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de cos et arccos",
            "Sur [-1, 1], la composition de cos avec arccos restitue l’argument initial: cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция cos и arccos",
            "На [-1, 1] композиция cos с arccos возвращает исходный аргумент: cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de cos y arccos",
            "En [-1, 1], componer cos con arccos devuelve el argumento original: cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ cos وarccos",
            "على [-1, 1]، يعيد تركيب cos مع arccos الوسيط الأصلي: cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "cosとarccosの逆演算の合成",
            "[-1, 1] 上では、cosとarccosの合成により元の引数が得られます：cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "cos와 arccos의 역연산 합성",
            "[-1, 1]에서 cos와 arccos를 합성하면 원래 인수를 얻습니다: cos(arccos(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của cos và arccos",
            "Trên [-1, 1], hợp thành cos với arccos trả về đối số ban đầu: cos(arccos(x)) = x",
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

impl TanArctanLeftInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Inverse composition of tan and arctan", "On R, composing tan with arctan returns the original argument: tan(arctan(x)) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("tan与arctan的逆运算复合", "在 R 上，tan与arctan复合后得到原参数，即 tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("tan與arctan的逆運算複合", "在 R 上，tan與arctan複合後得到原引數，即 tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Composition inverse de tan et arctan", "Sur R, la composition de tan avec arctan restitue l’argument initial: tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Обратная композиция tan и arctan", "На R композиция tan с arctan возвращает исходный аргумент: tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Composición inversa de tan y arctan", "En R, componer tan con arctan devuelve el argumento original: tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("التركيب العكسي لـ tan وarctan", "على R، يعيد تركيب tan مع arctan الوسيط الأصلي: tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("tanとarctanの逆演算の合成", "R 上では、tanとarctanの合成により元の引数が得られます：tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("tan와 arctan의 역연산 합성", "R에서 tan와 arctan를 합성하면 원래 인수를 얻습니다: tan(arctan(x)) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hợp thành nghịch đảo của tan và arctan", "Trên R, hợp thành tan với arctan trả về đối số ban đầu: tan(arctan(x)) = x")
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

impl CotArccotLeftInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Inverse composition of cot and arccot", "On R, composing cot with arccot returns the original argument: cot(arccot(x)) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("cot与arccot的逆运算复合", "在 R 上，cot与arccot复合后得到原参数，即 cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("cot與arccot的逆運算複合", "在 R 上，cot與arccot複合後得到原引數，即 cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Composition inverse de cot et arccot", "Sur R, la composition de cot avec arccot restitue l’argument initial: cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Обратная композиция cot и arccot", "На R композиция cot с arccot возвращает исходный аргумент: cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Composición inversa de cot y arccot", "En R, componer cot con arccot devuelve el argumento original: cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("التركيب العكسي لـ cot وarccot", "على R، يعيد تركيب cot مع arccot الوسيط الأصلي: cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("cotとarccotの逆演算の合成", "R 上では、cotとarccotの合成により元の引数が得られます：cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("cot와 arccot의 역연산 합성", "R에서 cot와 arccot를 합성하면 원래 인수를 얻습니다: cot(arccot(x)) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hợp thành nghịch đảo của cot và arccot", "Trên R, hợp thành cot với arccot trả về đối số ban đầu: cot(arccot(x)) = x")
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

impl ArcsinSinRightInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of arcsin and sin",
            "On [-π/2, π/2], composing arcsin with sin returns the original argument: arcsin(sin(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arcsin与sin的逆运算复合",
            "在 [-π/2, π/2] 上，arcsin与sin复合后得到原参数，即 arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arcsin與sin的逆運算複合",
            "在 [-π/2, π/2] 上，arcsin與sin複合後得到原引數，即 arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de arcsin et sin",
            "Sur [-π/2, π/2], la composition de arcsin avec sin restitue l’argument initial: arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция arcsin и sin",
            "На [-π/2, π/2] композиция arcsin с sin возвращает исходный аргумент: arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de arcsin y sin",
            "En [-π/2, π/2], componer arcsin con sin devuelve el argumento original: arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ arcsin وsin",
            "على [-π/2, π/2]، يعيد تركيب arcsin مع sin الوسيط الأصلي: arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arcsinとsinの逆演算の合成",
            "[-π/2, π/2] 上では、arcsinとsinの合成により元の引数が得られます：arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arcsin와 sin의 역연산 합성",
            "[-π/2, π/2]에서 arcsin와 sin를 합성하면 원래 인수를 얻습니다: arcsin(sin(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của arcsin và sin",
            "Trên [-π/2, π/2], hợp thành arcsin với sin trả về đối số ban đầu: arcsin(sin(x)) = x",
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

impl ArccosCosRightInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of arccos and cos",
            "On [0, π], composing arccos with cos returns the original argument: arccos(cos(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arccos与cos的逆运算复合",
            "在 [0, π] 上，arccos与cos复合后得到原参数，即 arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arccos與cos的逆運算複合",
            "在 [0, π] 上，arccos與cos複合後得到原引數，即 arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de arccos et cos",
            "Sur [0, π], la composition de arccos avec cos restitue l’argument initial: arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция arccos и cos",
            "На [0, π] композиция arccos с cos возвращает исходный аргумент: arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de arccos y cos",
            "En [0, π], componer arccos con cos devuelve el argumento original: arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ arccos وcos",
            "على [0, π]، يعيد تركيب arccos مع cos الوسيط الأصلي: arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arccosとcosの逆演算の合成",
            "[0, π] 上では、arccosとcosの合成により元の引数が得られます：arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arccos와 cos의 역연산 합성",
            "[0, π]에서 arccos와 cos를 합성하면 원래 인수를 얻습니다: arccos(cos(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của arccos và cos",
            "Trên [0, π], hợp thành arccos với cos trả về đối số ban đầu: arccos(cos(x)) = x",
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

impl ArctanTanRightInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of arctan and tan",
            "On (-π/2, π/2), composing arctan with tan returns the original argument: arctan(tan(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arctan与tan的逆运算复合",
            "在 (-π/2, π/2) 上，arctan与tan复合后得到原参数，即 arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arctan與tan的逆運算複合",
            "在 (-π/2, π/2) 上，arctan與tan複合後得到原引數，即 arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de arctan et tan",
            "Sur (-π/2, π/2), la composition de arctan avec tan restitue l’argument initial: arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция arctan и tan",
            "На (-π/2, π/2) композиция arctan с tan возвращает исходный аргумент: arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de arctan y tan",
            "En (-π/2, π/2), componer arctan con tan devuelve el argumento original: arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ arctan وtan",
            "على (-π/2, π/2)، يعيد تركيب arctan مع tan الوسيط الأصلي: arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arctanとtanの逆演算の合成",
            "(-π/2, π/2) 上では、arctanとtanの合成により元の引数が得られます：arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arctan와 tan의 역연산 합성",
            "(-π/2, π/2)에서 arctan와 tan를 합성하면 원래 인수를 얻습니다: arctan(tan(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của arctan và tan",
            "Trên (-π/2, π/2), hợp thành arctan với tan trả về đối số ban đầu: arctan(tan(x)) = x",
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

impl ArccotCotRightInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inverse composition of arccot and cot",
            "On (0, π), composing arccot with cot returns the original argument: arccot(cot(x)) = x",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arccot与cot的逆运算复合",
            "在 (0, π) 上，arccot与cot复合后得到原参数，即 arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arccot與cot的逆運算複合",
            "在 (0, π) 上，arccot與cot複合後得到原引數，即 arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Composition inverse de arccot et cot",
            "Sur (0, π), la composition de arccot avec cot restitue l’argument initial: arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратная композиция arccot и cot",
            "На (0, π) композиция arccot с cot возвращает исходный аргумент: arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Composición inversa de arccot y cot",
            "En (0, π), componer arccot con cot devuelve el argumento original: arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التركيب العكسي لـ arccot وcot",
            "على (0, π)، يعيد تركيب arccot مع cot الوسيط الأصلي: arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arccotとcotの逆演算の合成",
            "(0, π) 上では、arccotとcotの合成により元の引数が得られます：arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arccot와 cot의 역연산 합성",
            "(0, π)에서 arccot와 cot를 합성하면 원래 인수를 얻습니다: arccot(cot(x)) = x",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp thành nghịch đảo của arccot và cot",
            "Trên (0, π), hợp thành arccot với cot trả về đối số ban đầu: arccot(cot(x)) = x",
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

impl ArcsinExactZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arcsine at zero", "The value of arcsine at zero is zero: arcsin(0) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反正弦函数在零处的值", "反正弦函数在零处的值为零，即 arcsin(0) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反正弦函數在零處的值", "反正弦函數在零處的值為零，即 arcsin(0) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arcsinus en zéro", "La valeur de l’arcsinus en zéro est zéro: arcsin(0) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арксинус» при аргументе нуль", "При аргументе нуль функция «арксинус» принимает значение нуль: arcsin(0) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcoseno en cero", "El valor de arcoseno en cero es cero: arcsin(0) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب العكسية عند الصفر", "قيمة دالة الجيب العكسية عند الصفر تساوي الصفر: arcsin(0) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における逆正弦関数の値", "零における逆正弦関数の値は零です：arcsin(0) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 역사인 함수 값", "영에서의 역사인 함수 값은 영입니다: arcsin(0) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arcsin tại không", "Giá trị của hàm arcsin tại không bằng không: arcsin(0) = 0")
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

impl ArcsinExactOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arcsine at one", "The value of arcsine at one is π/2: arcsin(1) = π/2")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反正弦函数在一处的值", "反正弦函数在一处的值为π/2，即 arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反正弦函數在一處的值", "反正弦函數在一處的值為π/2，即 arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arcsinus en un", "La valeur de l’arcsinus en un est π/2: arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арксинус» при аргументе единица", "При аргументе единица функция «арксинус» принимает значение π/2: arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcoseno en uno", "El valor de arcoseno en uno es π/2: arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب العكسية عند الواحد", "قيمة دالة الجيب العكسية عند الواحد تساوي π/2: arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一における逆正弦関数の値", "一における逆正弦関数の値はπ/2です：arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일에서의 역사인 함수 값", "일에서의 역사인 함수 값은 π/2입니다: arcsin(1) = π/2")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arcsin tại một", "Giá trị của hàm arcsin tại một bằng π/2: arcsin(1) = π/2")
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

impl ArcsinExactNegOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arcsine at minus one", "The value of arcsine at minus one is -π/2: arcsin(-1) = -π/2")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反正弦函数在负一处的值", "反正弦函数在负一处的值为-π/2，即 arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反正弦函數在負一處的值", "反正弦函數在負一處的值為-π/2，即 arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arcsinus en moins un", "La valeur de l’arcsinus en moins un est -π/2: arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арксинус» при аргументе минус единица", "При аргументе минус единица функция «арксинус» принимает значение -π/2: arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcoseno en menos uno", "El valor de arcoseno en menos uno es -π/2: arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب العكسية عند سالب واحد", "قيمة دالة الجيب العكسية عند سالب واحد تساوي -π/2: arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("負の一における逆正弦関数の値", "負の一における逆正弦関数の値は-π/2です：arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("음의 일에서의 역사인 함수 값", "음의 일에서의 역사인 함수 값은 -π/2입니다: arcsin(-1) = -π/2")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arcsin tại âm một", "Giá trị của hàm arcsin tại âm một bằng -π/2: arcsin(-1) = -π/2")
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

impl ArccosExactOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arccosine at one", "The value of arccosine at one is zero: arccos(1) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反余弦函数在一处的值", "反余弦函数在一处的值为零，即 arccos(1) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反餘弦函數在一處的值", "反餘弦函數在一處的值為零，即 arccos(1) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arccosinus en un", "La valeur de l’arccosinus en un est zéro: arccos(1) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арккосинус» при аргументе единица", "При аргументе единица функция «арккосинус» принимает значение нуль: arccos(1) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcocoseno en uno", "El valor de arcocoseno en uno es cero: arccos(1) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة جيب التمام العكسية عند الواحد", "قيمة دالة جيب التمام العكسية عند الواحد تساوي الصفر: arccos(1) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一における逆余弦関数の値", "一における逆余弦関数の値は零です：arccos(1) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일에서의 역코사인 함수 값", "일에서의 역코사인 함수 값은 영입니다: arccos(1) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arccos tại một", "Giá trị của hàm arccos tại một bằng không: arccos(1) = 0")
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

impl ArccosExactZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arccosine at zero", "The value of arccosine at zero is π/2: arccos(0) = π/2")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反余弦函数在零处的值", "反余弦函数在零处的值为π/2，即 arccos(0) = π/2")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反餘弦函數在零處的值", "反餘弦函數在零處的值為π/2，即 arccos(0) = π/2")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arccosinus en zéro", "La valeur de l’arccosinus en zéro est π/2: arccos(0) = π/2")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арккосинус» при аргументе нуль", "При аргументе нуль функция «арккосинус» принимает значение π/2: arccos(0) = π/2")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcocoseno en cero", "El valor de arcocoseno en cero es π/2: arccos(0) = π/2")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة جيب التمام العكسية عند الصفر", "قيمة دالة جيب التمام العكسية عند الصفر تساوي π/2: arccos(0) = π/2")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における逆余弦関数の値", "零における逆余弦関数の値はπ/2です：arccos(0) = π/2")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 역코사인 함수 값", "영에서의 역코사인 함수 값은 π/2입니다: arccos(0) = π/2")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arccos tại không", "Giá trị của hàm arccos tại không bằng π/2: arccos(0) = π/2")
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

impl ArccosExactNegOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arccosine at minus one", "The value of arccosine at minus one is π: arccos(-1) = π")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反余弦函数在负一处的值", "反余弦函数在负一处的值为π，即 arccos(-1) = π")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反餘弦函數在負一處的值", "反餘弦函數在負一處的值為π，即 arccos(-1) = π")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arccosinus en moins un", "La valeur de l’arccosinus en moins un est π: arccos(-1) = π")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арккосинус» при аргументе минус единица", "При аргументе минус единица функция «арккосинус» принимает значение π: arccos(-1) = π")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcocoseno en menos uno", "El valor de arcocoseno en menos uno es π: arccos(-1) = π")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة جيب التمام العكسية عند سالب واحد", "قيمة دالة جيب التمام العكسية عند سالب واحد تساوي π: arccos(-1) = π")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("負の一における逆余弦関数の値", "負の一における逆余弦関数の値はπです：arccos(-1) = π")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("음의 일에서의 역코사인 함수 값", "음의 일에서의 역코사인 함수 값은 π입니다: arccos(-1) = π")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arccos tại âm một", "Giá trị của hàm arccos tại âm một bằng π: arccos(-1) = π")
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

impl ArctanExactZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arctangent at zero", "The value of arctangent at zero is zero: arctan(0) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反正切函数在零处的值", "反正切函数在零处的值为零，即 arctan(0) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反正切函數在零處的值", "反正切函數在零處的值為零，即 arctan(0) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arctangente en zéro", "La valeur de l’arctangente en zéro est zéro: arctan(0) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арктангенс» при аргументе нуль", "При аргументе нуль функция «арктангенс» принимает значение нуль: arctan(0) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcotangente en cero", "El valor de arcotangente en cero es cero: arctan(0) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الظل العكسية عند الصفر", "قيمة دالة الظل العكسية عند الصفر تساوي الصفر: arctan(0) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における逆正接関数の値", "零における逆正接関数の値は零です：arctan(0) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 역탄젠트 함수 값", "영에서의 역탄젠트 함수 값은 영입니다: arctan(0) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arctan tại không", "Giá trị của hàm arctan tại không bằng không: arctan(0) = 0")
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

impl ArccotExactZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of arccotangent at zero", "The value of arccotangent at zero is π/2: arccot(0) = π/2")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("反余切函数在零处的值", "反余切函数在零处的值为π/2，即 arccot(0) = π/2")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("反餘切函數在零處的值", "反餘切函數在零處的值為π/2，即 arccot(0) = π/2")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de l’arccotangente en zéro", "La valeur de l’arccotangente en zéro est π/2: arccot(0) = π/2")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «арккотангенс» при аргументе нуль", "При аргументе нуль функция «арккотангенс» принимает значение π/2: arccot(0) = π/2")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de arcocotangente en cero", "El valor de arcocotangente en cero es π/2: arccot(0) = π/2")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة ظل التمام العكسية عند الصفر", "قيمة دالة ظل التمام العكسية عند الصفر تساوي π/2: arccot(0) = π/2")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における逆余接関数の値", "零における逆余接関数の値はπ/2です：arccot(0) = π/2")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 역코탄젠트 함수 값", "영에서의 역코탄젠트 함수 값은 π/2입니다: arccot(0) = π/2")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm arccot tại không", "Giá trị của hàm arccot tại không bằng π/2: arccot(0) = π/2")
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

impl PowerProductSameBaseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Product of powers with the same base", "Multiplying powers with the same base adds their exponents: a^m · a^n = a^(m+n)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("同底数幂相乘", "同底数幂相乘时，底数不变，指数相加，即 a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("同底數冪相乘", "同底數冪相乘時，底數不變，指數相加，即 a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Produit de puissances de même base", "Multiplier des puissances de même base revient à additionner leurs exposants: a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Произведение степеней с одинаковым основанием", "При умножении степеней с одинаковым основанием показатели складываются: a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Producto de potencias de la misma base", "Al multiplicar potencias de la misma base se suman los exponentes: a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("ضرب قوى ذات أساس واحد", "عند ضرب قوى ذات أساس واحد تُجمع الأسس: a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("同じ底の累乗の積", "同じ底の累乗を掛けると、指数が加算されます：a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑이 같은 거듭제곱의 곱", "밑이 같은 거듭제곱을 곱하면 지수를 더합니다: a^m · a^n = a^(m+n)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tích các lũy thừa cùng cơ số", "Khi nhân các lũy thừa cùng cơ số, ta cộng các số mũ: a^m · a^n = a^(m+n)")
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

impl PowerOfPowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power of a power", "Raising a power to another power multiplies the exponents: (a^m)^n = a^(m·n)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("幂的乘方", "幂再乘方时，底数不变，指数相乘，即 (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("冪的乘方", "冪再乘方時，底數不變，指數相乘，即 (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Puissance d’une puissance", "Élever une puissance à une puissance multiplie les exposants: (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Степень степени", "При возведении степени в степень показатели перемножаются: (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Potencia de una potencia", "Al elevar una potencia a otra potencia se multiplican los exponentes: (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قوة مرفوعة إلى قوة", "عند رفع قوة إلى قوة أخرى تُضرب الأسس: (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("累乗の累乗", "累乗をさらに累乗すると、指数が乗算されます：(a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("거듭제곱의 거듭제곱", "거듭제곱을 다시 거듭제곱하면 지수를 곱합니다: (a^m)^n = a^(m·n)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Lũy thừa của một lũy thừa", "Khi lấy lũy thừa của một lũy thừa, ta nhân các số mũ: (a^m)^n = a^(m·n)")
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

impl PowerOfProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power of a product", "A power of a product equals the product of the corresponding powers: (a·b)^n = a^n · b^n")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("积的乘方", "积的乘方等于各因子同次幂的积，即 (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("積的乘方", "積的乘方等於各因子同次冪的積，即 (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Puissance d’un produit", "La puissance d’un produit est le produit des puissances correspondantes: (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Степень произведения", "Степень произведения равна произведению соответствующих степеней: (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Potencia de un producto", "La potencia de un producto es el producto de las potencias correspondientes: (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قوة حاصل الضرب", "قوة حاصل الضرب تساوي حاصل ضرب القوى المقابلة: (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("積の累乗", "積の累乗は各因子の累乗の積に等しくなります：(a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("곱의 거듭제곱", "곱의 거듭제곱은 각 인수의 거듭제곱을 곱한 값입니다: (a·b)^n = a^n · b^n")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Lũy thừa của một tích", "Lũy thừa của một tích bằng tích các lũy thừa tương ứng: (a·b)^n = a^n · b^n")
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

impl ReciprocalAsNegOnePowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Reciprocal as a negative first power", "The Reciprocal as a negative first power law gives: 1/a = a^(-1)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("倒数写成负一次幂", "倒数写成负一次幂可写为：1/a = a^(-1)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("倒數寫成負一次冪", "倒數寫成負一次冪可寫為：1/a = a^(-1)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Inverse comme puissance d’exposant moins un", "La propriété « Inverse comme puissance d’exposant moins un » donne: 1/a = a^(-1)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Обратное число как степень минус один", "Свойство «Обратное число как степень минус один» выражается равенством: 1/a = a^(-1)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Recíproco como potencia de exponente menos uno", "La propiedad «Recíproco como potencia de exponente menos uno» se expresa como: 1/a = a^(-1)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المقلوب كقوة أسها سالب واحد", "تُكتب خاصية «المقلوب كقوة أسها سالب واحد» كما يلي: 1/a = a^(-1)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("逆数と負一乗", "逆数と負一乗は次の式で表されます：1/a = a^(-1)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("역수와 음의 일제곱", "역수와 음의 일제곱은 다음 식으로 나타납니다: 1/a = a^(-1)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Nghịch đảo dưới dạng lũy thừa âm một", "Tính chất «Nghịch đảo dưới dạng lũy thừa âm một» được biểu diễn bởi: 1/a = a^(-1)")
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

impl QuotientAsMulNegOnePowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Division as multiplication by a reciprocal",
            "The Division as multiplication by a reciprocal law gives: a/b = a · b^(-1)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "除法写成乘以倒数",
            "除法写成乘以倒数可写为：a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "除法寫成乘以倒數",
            "除法寫成乘以倒數可寫為：a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Division comme multiplication par l’inverse",
            "La propriété « Division comme multiplication par l’inverse » donne: a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Деление как умножение на обратное число",
            "Свойство «Деление как умножение на обратное число» выражается равенством: a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "División como multiplicación por el recíproco",
            "La propiedad «División como multiplicación por el recíproco» se expresa como: a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القسمة كضرب في المقلوب",
            "تُكتب خاصية «القسمة كضرب في المقلوب» كما يلي: a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "除算と逆数の積",
            "除算と逆数の積は次の式で表されます：a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "나눗셈과 역수의 곱",
            "나눗셈과 역수의 곱은 다음 식으로 나타납니다: a/b = a · b^(-1)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phép chia dưới dạng nhân với nghịch đảo",
            "Tính chất «Phép chia dưới dạng nhân với nghịch đảo» được biểu diễn bởi: a/b = a · b^(-1)",
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

impl OneToAnyPowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power of one", "Every defined power of one equals one: 1^n = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("一的幂", "一的任何有定义的幂都等于一，即 1^n = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("一的冪", "一的任何有定義的冪都等於一，即 1^n = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Puissance de un", "Toute puissance définie de un vaut un: 1^n = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Степень единицы", "Любая определённая степень единицы равна единице: 1^n = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Potencia de uno", "Toda potencia definida de uno vale uno: 1^n = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قوة العدد واحد", "كل قوة معرّفة للعدد واحد تساوي واحدًا: 1^n = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一の累乗", "定義された一の累乗はすべて一です：1^n = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일의 거듭제곱", "정의된 일의 거듭제곱은 모두 일입니다: 1^n = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Lũy thừa của một", "Mọi lũy thừa xác định của một đều bằng một: 1^n = 1")
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

impl ZeroToPosNatPowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Positive natural power of zero",
            "Zero raised to a positive natural exponent equals zero: 0^n = 0 (n > 0)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("零的正自然数次幂", "零的正自然数次幂等于零，即 0^n = 0 (n > 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("零的正自然數次冪", "零的正自然數次冪等於零，即 0^n = 0 (n > 0)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance naturelle strictement positive de zéro",
            "Zéro élevé à un exposant naturel strictement positif vaut zéro: 0^n = 0 (n > 0)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Положительная натуральная степень нуля",
            "Нуль в положительной натуральной степени равен нулю: 0^n = 0 (n > 0)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia natural positiva de cero",
            "Cero elevado a un exponente natural positivo vale cero: 0^n = 0 (n > 0)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قوة طبيعية موجبة للصفر",
            "الصفر مرفوعًا إلى أس طبيعي موجب يساوي صفرًا: 0^n = 0 (n > 0)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "零の正の自然数乗",
            "零を正の自然数乗すると零になります：0^n = 0 (n > 0)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영의 양의 자연수 거듭제곱", "영을 양의 자연수 지수로 거듭제곱하면 영입니다: 0^n = 0 (n > 0)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa tự nhiên dương của không",
            "Không nâng lên số mũ tự nhiên dương bằng không: 0^n = 0 (n > 0)",
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

impl SqrtSquareBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Square of a square root",
            "Squaring the square root of a nonnegative real number returns that number: (sqrt(x))^2 = x (x ≥ 0)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("平方根的平方", "非负实数的平方根再平方，得到原数，即 (sqrt(x))^2 = x (x ≥ 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("平方根的平方", "非負實數的平方根再平方，得到原數，即 (sqrt(x))^2 = x (x ≥ 0)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Carré d’une racine carrée",
            "Le carré de la racine carrée d’un réel positif ou nul redonne ce réel: (sqrt(x))^2 = x (x ≥ 0)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Квадрат квадратного корня",
            "Квадрат квадратного корня неотрицательного вещественного числа равен самому числу: (sqrt(x))^2 = x (x ≥ 0)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cuadrado de una raíz cuadrada",
            "El cuadrado de la raíz cuadrada de un real no negativo devuelve ese número: (sqrt(x))^2 = x (x ≥ 0)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("مربع الجذر التربيعي", "مربع الجذر التربيعي لعدد حقيقي غير سالب يساوي العدد نفسه: (sqrt(x))^2 = x (x ≥ 0)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("平方根の二乗", "非負の実数の平方根を二乗すると元の数になります：(sqrt(x))^2 = x (x ≥ 0)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("제곱근의 제곱", "음이 아닌 실수의 제곱근을 제곱하면 원래 수가 됩니다: (sqrt(x))^2 = x (x ≥ 0)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bình phương của căn bậc hai",
            "Bình phương căn bậc hai của một số thực không âm trả lại số đó: (sqrt(x))^2 = x (x ≥ 0)",
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

impl SqrtZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of square root at zero", "The value of square root at zero is zero: sqrt(0) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("平方根在零处的值", "平方根在零处的值为零，即 sqrt(0) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("平方根在零處的值", "平方根在零處的值為零，即 sqrt(0) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de la racine carrée en zéro", "La valeur de la racine carrée en zéro est zéro: sqrt(0) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «квадратный корень» при аргументе нуль", "При аргументе нуль функция «квадратный корень» принимает значение нуль: sqrt(0) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de raíz cuadrada en cero", "El valor de raíz cuadrada en cero es cero: sqrt(0) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة الجذر التربيعي عند الصفر", "قيمة الجذر التربيعي عند الصفر تساوي الصفر: sqrt(0) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における平方根の値", "零における平方根の値は零です：sqrt(0) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 제곱근 값", "영에서의 제곱근 값은 영입니다: sqrt(0) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của căn bậc hai tại không", "Giá trị của căn bậc hai tại không bằng không: sqrt(0) = 0")
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

impl SqrtOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of square root at one", "The value of square root at one is one: sqrt(1) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("平方根在一处的值", "平方根在一处的值为一，即 sqrt(1) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("平方根在一處的值", "平方根在一處的值為一，即 sqrt(1) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de la racine carrée en un", "La valeur de la racine carrée en un est un: sqrt(1) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «квадратный корень» при аргументе единица", "При аргументе единица функция «квадратный корень» принимает значение единица: sqrt(1) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de raíz cuadrada en uno", "El valor de raíz cuadrada en uno es uno: sqrt(1) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة الجذر التربيعي عند الواحد", "قيمة الجذر التربيعي عند الواحد تساوي الواحد: sqrt(1) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一における平方根の値", "一における平方根の値は一です：sqrt(1) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일에서의 제곱근 값", "일에서의 제곱근 값은 일입니다: sqrt(1) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của căn bậc hai tại một", "Giá trị của căn bậc hai tại một bằng một: sqrt(1) = 1")
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

impl SqrtOfSquareBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Square root of a square", "The principal square root of a real square is the absolute value of its base: sqrt(a²) = abs(a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("平方的平方根", "实数平方的算术平方根等于该实数的绝对值，即 sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("平方的平方根", "實數平方的算術平方根等於該實數的絕對值，即 sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Racine carrée d’un carré", "La racine carrée principale du carré d’un réel est sa valeur absolue: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Квадратный корень из квадрата", "Главный квадратный корень из квадрата вещественного числа равен его модулю: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Raíz cuadrada de un cuadrado", "La raíz cuadrada principal del cuadrado de un real es su valor absoluto: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجذر التربيعي للمربع", "الجذر التربيعي الرئيسي لمربع عدد حقيقي يساوي قيمته المطلقة: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("平方の平方根", "実数の平方の主平方根は、その実数の絶対値です：sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("제곱의 제곱근", "실수 제곱의 주제곱근은 그 실수의 절댓값입니다: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Căn bậc hai của một bình phương", "Căn bậc hai chính của bình phương một số thực bằng giá trị tuyệt đối của số đó: sqrt(a²) = abs(a)")
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

impl SqrtProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Square root distributes over a product of nonnegative reals", "The Square root distributes over a product of nonnegative reals law gives: √(a·b) = √a · √b")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非负实数乘积的平方根", "非负实数乘积的平方根可写为：√(a·b) = √a · √b")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("非負實數乘積的平方根", "非負實數乘積的平方根可寫為：√(a·b) = √a · √b")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Racine carrée d’un produit de réels positifs ou nuls", "La propriété « Racine carrée d’un produit de réels positifs ou nuls » donne: √(a·b) = √a · √b")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Корень из произведения неотрицательных вещественных чисел",
            "Свойство «Корень из произведения неотрицательных вещественных чисел» выражается равенством: √(a·b) = √a · √b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Raíz de un producto de reales no negativos",
            "La propiedad «Raíz de un producto de reales no negativos» se expresa como: √(a·b) = √a · √b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جذر حاصل ضرب أعداد حقيقية غير سالبة",
            "تُكتب خاصية «جذر حاصل ضرب أعداد حقيقية غير سالبة» كما يلي: √(a·b) = √a · √b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負の実数の積の平方根",
            "非負の実数の積の平方根は次の式で表されます：√(a·b) = √a · √b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음이 아닌 실수의 곱의 제곱근",
            "음이 아닌 실수의 곱의 제곱근은 다음 식으로 나타납니다: √(a·b) = √a · √b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Căn bậc hai của tích các số thực không âm", "Tính chất «Căn bậc hai của tích các số thực không âm» được biểu diễn bởi: √(a·b) = √a · √b")
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

impl SqrtQuotientBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Square root of a nonnegative real quotient with positive denominator", "The Square root of a nonnegative real quotient with positive denominator law gives: √(a/b) = √a / √b")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("分母为正的非负实数商的平方根", "分母为正的非负实数商的平方根可写为：√(a/b) = √a / √b")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("分母為正的非負實數商的平方根", "分母為正的非負實數商的平方根可寫為：√(a/b) = √a / √b")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Racine carrée d’un quotient réel positif ou nul à dénominateur positif", "La propriété « Racine carrée d’un quotient réel positif ou nul à dénominateur positif » donne: √(a/b) = √a / √b")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Корень из неотрицательного вещественного частного с положительным знаменателем",
            "Свойство «Корень из неотрицательного вещественного частного с положительным знаменателем» выражается равенством: √(a/b) = √a / √b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Raíz de un cociente real no negativo con denominador positivo",
            "La propiedad «Raíz de un cociente real no negativo con denominador positivo» se expresa como: √(a/b) = √a / √b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جذر خارج قسمة حقيقي غير سالب ذي مقام موجب",
            "تُكتب خاصية «جذر خارج قسمة حقيقي غير سالب ذي مقام موجب» كما يلي: √(a/b) = √a / √b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "分母が正の非負実数の商の平方根",
            "分母が正の非負実数の商の平方根は次の式で表されます：√(a/b) = √a / √b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "분모가 양수인 음이 아닌 실수 몫의 제곱근",
            "분모가 양수인 음이 아닌 실수 몫의 제곱근은 다음 식으로 나타납니다: √(a/b) = √a / √b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Căn bậc hai của thương thực không âm có mẫu dương", "Tính chất «Căn bậc hai của thương thực không âm có mẫu dương» được biểu diễn bởi: √(a/b) = √a / √b")
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

impl AbsOfNegationBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Absolute value of a negation", "Negating a number leaves its absolute value unchanged: abs(-a) = abs(a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("取负不改变绝对值", "一个数与它的相反数具有相同的绝对值，即 abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("取負不改變絕對值", "一個數與它的相反數具有相同的絕對值，即 abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur absolue d’un opposé", "Un nombre et son opposé ont la même valeur absolue: abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Модуль противоположного числа", "Число и противоположное ему число имеют одинаковый модуль: abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor absoluto del opuesto", "Un número y su opuesto tienen el mismo valor absoluto: abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القيمة المطلقة للعدد المعاكس", "للعدد ومعاكسه القيمة المطلقة نفسها: abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("符号反転と絶対値", "数とその符号を反転した数の絶対値は等しくなります：abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("부호 반전과 절댓값", "수와 그 부호를 반전한 수의 절댓값은 같습니다: abs(-a) = abs(a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị tuyệt đối của số đối", "Một số và số đối của nó có cùng giá trị tuyệt đối: abs(-a) = abs(a)")
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

impl AbsProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Multiplicativity of absolute value", "The Multiplicativity of absolute value law gives: abs(a·b) = abs(a)·abs(b)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("绝对值的乘法性质", "绝对值的乘法性质可写为：abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("絕對值的乘法性質", "絕對值的乘法性質可寫為：abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Multiplicativité de la valeur absolue", "La propriété « Multiplicativité de la valeur absolue » donne: abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Мультипликативность модуля", "Свойство «Мультипликативность модуля» выражается равенством: abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Multiplicatividad del valor absoluto", "La propiedad «Multiplicatividad del valor absoluto» se expresa como: abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية ضرب القيم المطلقة", "تُكتب خاصية «خاصية ضرب القيم المطلقة» كما يلي: abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("絶対値の乗法性", "絶対値の乗法性は次の式で表されます：abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("절댓값의 곱셈 성질", "절댓값의 곱셈 성질은 다음 식으로 나타납니다: abs(a·b) = abs(a)·abs(b)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính nhân của giá trị tuyệt đối", "Tính chất «Tính nhân của giá trị tuyệt đối» được biểu diễn bởi: abs(a·b) = abs(a)·abs(b)")
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

impl AbsSquareBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Square of the absolute value of a real number", "The Square of the absolute value of a real number law gives: abs(a)² = a²")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数绝对值的平方", "实数绝对值的平方可写为：abs(a)² = a²")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("實數絕對值的平方", "實數絕對值的平方可寫為：abs(a)² = a²")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Carré de la valeur absolue d’un réel", "La propriété « Carré de la valeur absolue d’un réel » donne: abs(a)² = a²")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Квадрат модуля вещественного числа", "Свойство «Квадрат модуля вещественного числа» выражается равенством: abs(a)² = a²")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Cuadrado del valor absoluto de un real", "La propiedad «Cuadrado del valor absoluto de un real» se expresa como: abs(a)² = a²")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("مربع القيمة المطلقة لعدد حقيقي", "تُكتب خاصية «مربع القيمة المطلقة لعدد حقيقي» كما يلي: abs(a)² = a²")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("実数の絶対値の二乗", "実数の絶対値の二乗は次の式で表されます：abs(a)² = a²")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("실수 절댓값의 제곱", "실수 절댓값의 제곱은 다음 식으로 나타납니다: abs(a)² = a²")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Bình phương giá trị tuyệt đối của số thực", "Tính chất «Bình phương giá trị tuyệt đối của số thực» được biểu diễn bởi: abs(a)² = a²")
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

impl LogBaseSelfBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Logarithm of the base", "The Logarithm of the base law gives: log_a(a) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("底数自身的对数", "底数自身的对数可写为：log_a(a) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("底數自身的對數", "底數自身的對數可寫為：log_a(a) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme de la base", "La propriété « Logarithme de la base » donne: log_a(a) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Логарифм основания", "Свойство «Логарифм основания» выражается равенством: log_a(a) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo de la base", "La propiedad «Logaritmo de la base» se expresa como: log_a(a) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("لوغاريتم الأساس", "تُكتب خاصية «لوغاريتم الأساس» كما يلي: log_a(a) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("底自身の対数", "底自身の対数は次の式で表されます：log_a(a) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑 자체의 로그", "밑 자체의 로그은 다음 식으로 나타납니다: log_a(a) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit của cơ số", "Tính chất «Logarit của cơ số» được biểu diễn bởi: log_a(a) = 1")
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

impl LogOfOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Logarithm of one", "The Logarithm of one law gives: log_a(1) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("一的对数", "一的对数可写为：log_a(1) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("一的對數", "一的對數可寫為：log_a(1) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme de un", "La propriété « Logarithme de un » donne: log_a(1) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Логарифм единицы", "Свойство «Логарифм единицы» выражается равенством: log_a(1) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo de uno", "La propiedad «Logaritmo de uno» se expresa como: log_a(1) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("لوغاريتم الواحد", "تُكتب خاصية «لوغاريتم الواحد» كما يلي: log_a(1) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一の対数", "一の対数は次の式で表されます：log_a(1) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일의 로그", "일의 로그은 다음 식으로 나타납니다: log_a(1) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit của một", "Tính chất «Logarit của một» được biểu diễn bởi: log_a(1) = 0")
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

impl LogOfPowerSameBaseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Cancellation of logarithm and same-base power", "The Cancellation of logarithm and same-base power law gives: log_a(a^n) = n")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("同底对数与幂的消去", "同底对数与幂的消去可写为：log_a(a^n) = n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("同底對數與冪的消去", "同底對數與冪的消去可寫為：log_a(a^n) = n")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Annulation du logarithme et d’une puissance de même base", "La propriété « Annulation du logarithme et d’une puissance de même base » donne: log_a(a^n) = n")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Сокращение логарифма и степени с тем же основанием", "Свойство «Сокращение логарифма и степени с тем же основанием» выражается равенством: log_a(a^n) = n")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Cancelación del logaritmo y la potencia de la misma base", "La propiedad «Cancelación del logaritmo y la potencia de la misma base» se expresa como: log_a(a^n) = n")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("اختزال اللوغاريتم والقوة ذات الأساس نفسه", "تُكتب خاصية «اختزال اللوغاريتم والقوة ذات الأساس نفسه» كما يلي: log_a(a^n) = n")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("同じ底の対数と累乗の相殺", "同じ底の対数と累乗の相殺は次の式で表されます：log_a(a^n) = n")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑이 같은 로그와 거듭제곱의 소거", "밑이 같은 로그와 거듭제곱의 소거은 다음 식으로 나타납니다: log_a(a^n) = n")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Khử logarit và lũy thừa cùng cơ số", "Tính chất «Khử logarit và lũy thừa cùng cơ số» được biểu diễn bởi: log_a(a^n) = n")
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

impl LogArgPowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power rule for logarithms", "The exponent can be taken out as a factor of the logarithm: log_a(b^n) = n · log_a(b)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("对数的幂法则", "真数的指数可作为乘法因子移到对数前，即 log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("對數的冪法則", "真數的指數可作為乘法因子移到對數前，即 log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Règle des puissances pour les logarithmes", "L’exposant peut être sorti comme facteur du logarithme: log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Логарифм степени", "Показатель степени можно вынести множителем перед логарифмом: log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Regla de la potencia para logaritmos", "El exponente puede extraerse como factor del logaritmo: log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قاعدة لوغاريتم القوة", "يمكن إخراج الأس كعامل أمام اللوغاريتم: log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("対数の累乗法則", "指数は対数の前の係数として取り出せます：log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("로그의 거듭제곱 법칙", "지수를 로그 앞의 곱셈 인수로 꺼낼 수 있습니다: log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Quy tắc logarit của lũy thừa", "Số mũ có thể đưa ra ngoài làm hệ số của logarit: log_a(b^n) = n · log_a(b)")
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

impl LogProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Product rule for logarithms",
            "The logarithm of a product is the sum of the logarithms: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "积的对数",
            "积的对数等于各因子对数之和，即 log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "積的對數",
            "積的對數等於各因子對數之和，即 log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Logarithme d’un produit",
            "Le logarithme d’un produit est la somme des logarithmes: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Логарифм произведения",
            "Логарифм произведения равен сумме логарифмов: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Logaritmo de un producto",
            "El logaritmo de un producto es la suma de los logaritmos: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "لوغاريتم حاصل الضرب",
            "لوغاريتم حاصل الضرب يساوي مجموع اللوغاريتمات: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "積の対数",
            "積の対数は各因子の対数の和です：log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "곱의 로그",
            "곱의 로그는 각 인수의 로그의 합입니다: log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Logarit của một tích",
            "Logarit của một tích bằng tổng các logarit: log_a(b·c) = log_a(b) + log_a(c)",
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

impl LogQuotientBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Quotient rule for logarithms",
            "The logarithm of a quotient is the logarithm of the numerator minus that of the denominator: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "商的对数",
            "商的对数等于分子对数减去分母对数，即 log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "商的對數",
            "商的對數等於分子對數減去分母對數，即 log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Logarithme d’un quotient",
            "Le logarithme d’un quotient est celui du numérateur moins celui du dénominateur: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Логарифм частного",
            "Логарифм частного равен логарифму числителя минус логарифм знаменателя: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Logaritmo de un cociente",
            "El logaritmo de un cociente es el logaritmo del numerador menos el del denominador: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "لوغاريتم خارج القسمة",
            "لوغاريتم خارج القسمة يساوي لوغاريتم البسط ناقص لوغاريتم المقام: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "商の対数",
            "商の対数は分子の対数から分母の対数を引いた値です：log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "몫의 로그",
            "몫의 로그는 분자의 로그에서 분모의 로그를 뺀 값입니다: log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Logarit của một thương",
            "Logarit của một thương bằng logarit tử số trừ logarit mẫu số: log_a(b/c) = log_a(b) - log_a(c)",
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

impl LogReciprocalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Logarithm of a reciprocal", "Taking the logarithm of a reciprocal negates the logarithm: log_a(1/b) = -log_a(b)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("倒数的对数", "倒数的对数等于原数对数的相反数，即 log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("倒數的對數", "倒數的對數等於原數對數的相反數，即 log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme d’un inverse", "Le logarithme d’un inverse est l’opposé du logarithme: log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Логарифм обратного числа", "Логарифм обратного числа равен противоположному логарифму исходного числа: log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo de un recíproco", "El logaritmo de un recíproco es el opuesto del logaritmo: log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("لوغاريتم المقلوب", "لوغاريتم المقلوب يساوي سالب لوغاريتم العدد الأصلي: log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("逆数の対数", "逆数の対数は元の数の対数の符号を反転した値です：log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("역수의 로그", "역수의 로그는 원래 수의 로그의 부호를 반전한 값입니다: log_a(1/b) = -log_a(b)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit của số nghịch đảo", "Logarit của số nghịch đảo bằng số đối của logarit ban đầu: log_a(1/b) = -log_a(b)")
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

impl LogChangeOfBaseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Change of logarithm base",
            "The Change of logarithm base law gives: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "对数换底",
            "对数换底可写为：log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "對數換底",
            "對數換底可寫為：log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Changement de base du logarithme",
            "La propriété « Changement de base du logarithme » donne: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Переход к другому основанию логарифма",
            "Свойство «Переход к другому основанию логарифма» выражается равенством: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cambio de base del logaritmo",
            "La propiedad «Cambio de base del logaritmo» se expresa como: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تغيير أساس اللوغاريتم",
            "تُكتب خاصية «تغيير أساس اللوغاريتم» كما يلي: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "対数の底の変換",
            "対数の底の変換は次の式で表されます：log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "로그의 밑 변환",
            "로그의 밑 변환은 다음 식으로 나타납니다: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đổi cơ số logarit",
            "Tính chất «Đổi cơ số logarit» được biểu diễn bởi: log_a(b) = log_c(b) / log_c(a); a,c>0; a!=1; c!=1; b>0",
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

impl ZeroModBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Remainder of zero", "The Remainder of zero law gives: 0 mod n = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("零的余数", "零的余数可写为：0 mod n = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("零的餘數", "零的餘數可寫為：0 mod n = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Reste de zéro", "La propriété « Reste de zéro » donne: 0 mod n = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Остаток от деления нуля", "Свойство «Остаток от деления нуля» выражается равенством: 0 mod n = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Resto de cero", "La propiedad «Resto de cero» se expresa como: 0 mod n = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("باقي قسمة الصفر", "تُكتب خاصية «باقي قسمة الصفر» كما يلي: 0 mod n = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零の剰余", "零の剰余は次の式で表されます：0 mod n = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영의 나머지", "영의 나머지은 다음 식으로 나타납니다: 0 mod n = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Số dư của không", "Tính chất «Số dư của không» được biểu diễn bởi: 0 mod n = 0")
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

impl ModOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Remainder modulo one", "The Remainder modulo one law gives: a mod 1 = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("除以一的余数", "除以一的余数可写为：a mod 1 = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("除以一的餘數", "除以一的餘數可寫為：a mod 1 = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Reste modulo un", "La propriété « Reste modulo un » donne: a mod 1 = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Остаток по модулю один", "Свойство «Остаток по модулю один» выражается равенством: a mod 1 = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Resto módulo uno", "La propiedad «Resto módulo uno» se expresa como: a mod 1 = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الباقي بترديد واحد", "تُكتب خاصية «الباقي بترديد واحد» كما يلي: a mod 1 = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一を法とする剰余", "一を法とする剰余は次の式で表されます：a mod 1 = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일로 나눈 나머지", "일로 나눈 나머지은 다음 식으로 나타납니다: a mod 1 = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Số dư khi chia cho một", "Tính chất «Số dư khi chia cho một» được biểu diễn bởi: a mod 1 = 0")
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

impl OneModAtLeastTwoBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Remainder of one for a modulus at least two",
            "The Remainder of one for a modulus at least two law gives: 1 mod n = 1",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "一除以至少为二的模数的余数",
            "一除以至少为二的模数的余数可写为：1 mod n = 1",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "一除以至少為二的模數的餘數",
            "一除以至少為二的模數的餘數可寫為：1 mod n = 1",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Reste de un pour un module au moins deux", "La propriété « Reste de un pour un module au moins deux » donne: 1 mod n = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Остаток единицы по модулю не меньше двух", "Свойство «Остаток единицы по модулю не меньше двух» выражается равенством: 1 mod n = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Resto de uno con módulo al menos dos", "La propiedad «Resto de uno con módulo al menos dos» se expresa como: 1 mod n = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("باقي الواحد بترديد لا يقل عن اثنين", "تُكتب خاصية «باقي الواحد بترديد لا يقل عن اثنين» كما يلي: 1 mod n = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "二以上を法とする一の剰余",
            "二以上を法とする一の剰余は次の式で表されます：1 mod n = 1",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "법이 이 이상일 때 일의 나머지",
            "법이 이 이상일 때 일의 나머지은 다음 식으로 나타납니다: 1 mod n = 1",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Số dư của một với môđun ít nhất bằng hai", "Tính chất «Số dư của một với môđun ít nhất bằng hai» được biểu diễn bởi: 1 mod n = 1")
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

impl NestedSameModAbsorptionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Repeated remainder with the same modulus",
            "The Repeated remainder with the same modulus law gives: (a mod n) mod n = a mod n",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "同一模数下重复取余",
            "同一模数下重复取余可写为：(a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "同一模數下重複取餘",
            "同一模數下重複取餘可寫為：(a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Reste répété avec le même module",
            "La propriété « Reste répété avec le même module » donne: (a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Повторное взятие остатка по тому же модулю",
            "Свойство «Повторное взятие остатка по тому же модулю» выражается равенством: (a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Resto repetido con el mismo módulo",
            "La propiedad «Resto repetido con el mismo módulo» se expresa como: (a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تكرار الباقي بالترديد نفسه",
            "تُكتب خاصية «تكرار الباقي بالترديد نفسه» كما يلي: (a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "同じ法による剰余の反復",
            "同じ法による剰余の反復は次の式で表されます：(a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "같은 법으로 나머지를 다시 구하기",
            "같은 법으로 나머지를 다시 구하기은 다음 식으로 나타납니다: (a mod n) mod n = a mod n",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lấy số dư lặp lại với cùng môđun",
            "Tính chất «Lấy số dư lặp lại với cùng môđun» được biểu diễn bởi: (a mod n) mod n = a mod n",
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

impl ModCompatibleSmallerModulusBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Remainder reduction to a divisor modulus",
            "The Remainder reduction to a divisor modulus law gives: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "余数向约数模数约化",
            "余数向约数模数约化可写为，即 m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "餘數向約數模數約化",
            "餘數向約數模數約化可寫為，即 m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réduction du reste à un module diviseur",
            "La propriété « Réduction du reste à un module diviseur » donne: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сведение остатка к модулю-делителю",
            "Свойство «Сведение остатка к модулю-делителю» выражается равенством: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reducción del resto a un módulo divisor",
            "La propiedad «Reducción del resto a un módulo divisor» se expresa como: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اختزال الباقي إلى ترديد يقسم الترديد الأصلي",
            "تُكتب خاصية «اختزال الباقي إلى ترديد يقسم الترديد الأصلي» كما يلي: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "法の約数への剰余の縮約",
            "法の約数への剰余の縮約は次の式で表されます：m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "법의 약수로 나머지 축소",
            "법의 약수로 나머지 축소은 다음 식으로 나타납니다：m mod d = 0 ⇒ a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Rút gọn số dư theo môđun ước",
            "Tính chất «Rút gọn số dư theo môđun ước» được biểu diễn bởi: m mod d = 0 ⇒ a mod d = (a mod m) mod d",
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

impl MinIdempotentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Idempotence of minimum", "Applying minimum to two identical arguments returns that argument: min(a,a) = a")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最小值的幂等性", "最小值的两个参数相同时，结果就是该参数，即 min(a,a) = a")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最小值的冪等性", "最小值的兩個引數相同時，結果就是該引數，即 min(a,a) = a")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Idempotence : minimum", "L’opération « minimum » appliquée à deux arguments identiques restitue cet argument: min(a,a) = a")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Идемпотентность: минимум", "Операция «минимум» с одинаковыми аргументами возвращает этот аргумент: min(a,a) = a")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Idempotencia: mínimo", "La operación «mínimo» con dos argumentos iguales devuelve ese argumento: min(a,a) = a")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية التكرار: القيمة الصغرى", "تطبيق عملية «القيمة الصغرى» على وسيطين متساويين يعيد الوسيط نفسه: min(a,a) = a")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最小値の冪等性", "最小値に同じ引数を二つ与えると、その引数が得られます：min(a,a) = a")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최솟값의 멱등성", "최솟값의 두 인수가 같으면 그 인수가 결과입니다: min(a,a) = a")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính lũy đẳng của giá trị nhỏ nhất", "Phép giá trị nhỏ nhất với hai đối số giống nhau trả về chính đối số đó: min(a,a) = a")
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

impl MaxIdempotentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Idempotence of maximum", "Applying maximum to two identical arguments returns that argument: max(a,a) = a")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最大值的幂等性", "最大值的两个参数相同时，结果就是该参数，即 max(a,a) = a")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最大值的冪等性", "最大值的兩個引數相同時，結果就是該引數，即 max(a,a) = a")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Idempotence : maximum", "L’opération « maximum » appliquée à deux arguments identiques restitue cet argument: max(a,a) = a")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Идемпотентность: максимум", "Операция «максимум» с одинаковыми аргументами возвращает этот аргумент: max(a,a) = a")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Idempotencia: máximo", "La operación «máximo» con dos argumentos iguales devuelve ese argumento: max(a,a) = a")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية التكرار: القيمة العظمى", "تطبيق عملية «القيمة العظمى» على وسيطين متساويين يعيد الوسيط نفسه: max(a,a) = a")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最大値の冪等性", "最大値に同じ引数を二つ与えると、その引数が得られます：max(a,a) = a")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최댓값의 멱등성", "최댓값의 두 인수가 같으면 그 인수가 결과입니다: max(a,a) = a")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính lũy đẳng của giá trị lớn nhất", "Phép giá trị lớn nhất với hai đối số giống nhau trả về chính đối số đó: max(a,a) = a")
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

impl MinCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Commutativity of minimum", "Swapping the two arguments of minimum leaves the result unchanged: min(a,b) = min(b,a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最小值的交换律", "交换最小值的两个参数，结果不变，即 min(a,b) = min(b,a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最小值的交換律", "交換最小值的兩個引數，結果不變，即 min(a,b) = min(b,a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : minimum",
            "Permuter les arguments de l’opération « minimum » ne change pas le résultat: min(a,b) = min(b,a)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: минимум",
            "Перестановка аргументов операции «минимум» не меняет результат: min(a,b) = min(b,a)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: mínimo",
            "Intercambiar los argumentos de la operación «mínimo» no cambia el resultado: min(a,b) = min(b,a)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: القيمة الصغرى", "تبديل وسيطي عملية «القيمة الصغرى» لا يغيّر النتيجة: min(a,b) = min(b,a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最小値の交換法則", "最小値の二つの引数を交換しても結果は変わりません：min(a,b) = min(b,a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최솟값의 교환법칙", "최솟값의 두 인수를 바꾸어도 결과는 같습니다: min(a,b) = min(b,a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính giao hoán của giá trị nhỏ nhất", "Đổi chỗ hai đối số của phép giá trị nhỏ nhất không làm thay đổi kết quả: min(a,b) = min(b,a)")
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

impl MaxCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Commutativity of maximum", "Swapping the two arguments of maximum leaves the result unchanged: max(a,b) = max(b,a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最大值的交换律", "交换最大值的两个参数，结果不变，即 max(a,b) = max(b,a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最大值的交換律", "交換最大值的兩個引數，結果不變，即 max(a,b) = max(b,a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : maximum",
            "Permuter les arguments de l’opération « maximum » ne change pas le résultat: max(a,b) = max(b,a)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: максимум",
            "Перестановка аргументов операции «максимум» не меняет результат: max(a,b) = max(b,a)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: máximo",
            "Intercambiar los argumentos de la operación «máximo» no cambia el resultado: max(a,b) = max(b,a)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: القيمة العظمى", "تبديل وسيطي عملية «القيمة العظمى» لا يغيّر النتيجة: max(a,b) = max(b,a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最大値の交換法則", "最大値の二つの引数を交換しても結果は変わりません：max(a,b) = max(b,a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최댓값의 교환법칙", "최댓값의 두 인수를 바꾸어도 결과는 같습니다: max(a,b) = max(b,a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính giao hoán của giá trị lớn nhất", "Đổi chỗ hai đối số của phép giá trị lớn nhất không làm thay đổi kết quả: max(a,b) = max(b,a)")
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

impl AbsAbsAbsorptionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Idempotence of absolute value", "Taking the absolute value twice gives the same result as taking it once: abs(abs(a)) = abs(a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("绝对值的幂等性", "重复取绝对值不会改变结果，即 abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("絕對值的冪等性", "重複取絕對值不會改變結果，即 abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Idempotence de la valeur absolue", "Prendre deux fois la valeur absolue donne le même résultat qu’une seule fois: abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Идемпотентность модуля", "Повторное взятие модуля не меняет результат: abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Idempotencia del valor absoluto", "Tomar dos veces el valor absoluto da el mismo resultado que una sola vez: abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("ثبات القيمة المطلقة عند تكرارها", "أخذ القيمة المطلقة مرتين يعطي نتيجة أخذها مرة واحدة: abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("絶対値の冪等性", "絶対値を二回取っても一回取った場合と同じ値です：abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("절댓값의 멱등성", "절댓값을 두 번 취해도 한 번 취한 값과 같습니다: abs(abs(a)) = abs(a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính lũy đẳng của giá trị tuyệt đối", "Lấy giá trị tuyệt đối hai lần cho cùng kết quả như lấy một lần: abs(abs(a)) = abs(a)")
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

impl ExpOfLnBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Exponential after natural logarithm", "The Exponential after natural logarithm law gives: exp(ln(x)) = x (x > 0)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("自然对数后的指数运算", "自然对数后的指数运算可写为：exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("自然對數後的指數運算", "自然對數後的指數運算可寫為：exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Exponentielle après logarithme naturel", "La propriété « Exponentielle après logarithme naturel » donne: exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Экспонента натурального логарифма", "Свойство «Экспонента натурального логарифма» выражается равенством: exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Exponencial después del logaritmo natural", "La propiedad «Exponencial después del logaritmo natural» se expresa como: exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الدالة الأسية بعد اللوغاريتم الطبيعي", "تُكتب خاصية «الدالة الأسية بعد اللوغاريتم الطبيعي» كما يلي: exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("自然対数と指数関数の合成", "自然対数と指数関数の合成は次の式で表されます：exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("자연로그 뒤의 지수함수", "자연로그 뒤의 지수함수은 다음 식으로 나타납니다: exp(ln(x)) = x (x > 0)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hàm mũ sau logarit tự nhiên", "Tính chất «Hàm mũ sau logarit tự nhiên» được biểu diễn bởi: exp(ln(x)) = x (x > 0)")
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

impl LnOfExpBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Natural logarithm after exponential", "The Natural logarithm after exponential law gives: ln(exp(x)) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("指数运算后的自然对数", "指数运算后的自然对数可写为：ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("指數運算後的自然對數", "指數運算後的自然對數可寫為：ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme naturel après exponentielle", "La propriété « Logarithme naturel après exponentielle » donne: ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Натуральный логарифм экспоненты", "Свойство «Натуральный логарифм экспоненты» выражается равенством: ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo natural después de la exponencial", "La propiedad «Logaritmo natural después de la exponencial» se expresa como: ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("اللوغاريتم الطبيعي بعد الدالة الأسية", "تُكتب خاصية «اللوغاريتم الطبيعي بعد الدالة الأسية» كما يلي: ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("指数関数と自然対数の合成", "指数関数と自然対数の合成は次の式で表されます：ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("지수함수 뒤의 자연로그", "지수함수 뒤의 자연로그은 다음 식으로 나타납니다: ln(exp(x)) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit tự nhiên sau hàm mũ", "Tính chất «Logarit tự nhiên sau hàm mũ» được biểu diễn bởi: ln(exp(x)) = x")
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

impl FloorOfIntegerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋ for integer n",
            "⌊n⌋ = n when n is an integer",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数 n 的 ⌊n⌋", "当 n 为整数时 ⌊n⌋ = n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("⌊n⌋（n 為整數）", "⌊n⌋ = n（n 為整數時）")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋ pour n entier",
            "⌊n⌋ = n si n est entier",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("⌊n⌋ для целого n", "⌊n⌋ = n если n целое")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋ para n entero",
            "⌊n⌋ = n si n es entero",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋ للعدد الصحيح n",
            "⌊n⌋ = n إذا كان n صحيحًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋（n は整数）",
            "⌊n⌋ = n（n が整数の場合）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("⌊n⌋(n은 정수)", "⌊n⌋ = n(n이 정수일 때)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "⌊n⌋ với n nguyên",
            "⌊n⌋ = n khi n là số nguyên",
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

impl CeilOfIntegerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉ for integer n",
            "⌈n⌉ = n when n is an integer",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数 n 的 ⌈n⌉", "当 n 为整数时 ⌈n⌉ = n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("⌈n⌉（n 為整數）", "⌈n⌉ = n（n 為整數時）")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉ pour n entier",
            "⌈n⌉ = n si n est entier",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("⌈n⌉ для целого n", "⌈n⌉ = n если n целое")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉ para n entero",
            "⌈n⌉ = n si n es entero",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉ للعدد الصحيح n",
            "⌈n⌉ = n إذا كان n صحيحًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉（n は整数）",
            "⌈n⌉ = n（n が整数の場合）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("⌈n⌉(n은 정수)", "⌈n⌉ = n(n이 정수일 때)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "⌈n⌉ với n nguyên",
            "⌈n⌉ = n khi n là số nguyên",
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

impl ModSelfZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Remainder when a nonzero integer divides itself", "The Remainder when a nonzero integer divides itself law gives: a mod a = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非零整数除以自身的余数", "非零整数除以自身的余数可写为：a mod a = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("非零整數除以自身的餘數", "非零整數除以自身的餘數可寫為：a mod a = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Reste d’un entier non nul divisé par lui-même", "La propriété « Reste d’un entier non nul divisé par lui-même » donne: a mod a = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Остаток ненулевого целого при делении на себя", "Свойство «Остаток ненулевого целого при делении на себя» выражается равенством: a mod a = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Resto de un entero no nulo dividido por sí mismo", "La propiedad «Resto de un entero no nulo dividido por sí mismo» se expresa como: a mod a = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("باقي قسمة عدد صحيح غير صفري على نفسه", "تُكتب خاصية «باقي قسمة عدد صحيح غير صفري على نفسه» كما يلي: a mod a = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零でない整数を自身で割った剰余", "零でない整数を自身で割った剰余は次の式で表されます：a mod a = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영이 아닌 정수를 자기 자신으로 나눈 나머지", "영이 아닌 정수를 자기 자신으로 나눈 나머지은 다음 식으로 나타납니다: a mod a = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Số dư của số nguyên khác không chia cho chính nó", "Tính chất «Số dư của số nguyên khác không chia cho chính nó» được biểu diễn bởi: a mod a = 0")
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

impl FloorOfCeilOfIntegerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Floor after ceiling of an integer", "The Floor after ceiling of an integer law gives: ⌊⌈n⌉⌋ = n")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数先向上再向下取整", "整数先向上再向下取整可写为：⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("整數先向上再向下取整", "整數先向上再向下取整可寫為：⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Arrondi inférieur après arrondi supérieur d’un entier", "La propriété « Arrondi inférieur après arrondi supérieur d’un entier » donne: ⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Округление целого вверх, затем вниз", "Свойство «Округление целого вверх, затем вниз» выражается равенством: ⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Redondeo inferior tras redondeo superior de un entero", "La propiedad «Redondeo inferior tras redondeo superior de un entero» se expresa como: ⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("تقريب عدد صحيح لأعلى ثم لأسفل", "تُكتب خاصية «تقريب عدد صحيح لأعلى ثم لأسفل» كما يلي: ⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("整数の切り上げ後の切り捨て", "整数の切り上げ後の切り捨ては次の式で表されます：⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("정수를 올림한 뒤 내림하기", "정수를 올림한 뒤 내림하기은 다음 식으로 나타납니다: ⌊⌈n⌉⌋ = n")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Làm tròn xuống sau khi làm tròn lên một số nguyên", "Tính chất «Làm tròn xuống sau khi làm tròn lên một số nguyên» được biểu diễn bởi: ⌊⌈n⌉⌋ = n")
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

impl CeilOfFloorOfIntegerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Ceiling after floor of an integer", "The Ceiling after floor of an integer law gives: ⌈⌊n⌋⌉ = n")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数先向下再向上取整", "整数先向下再向上取整可写为：⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("整數先向下再向上取整", "整數先向下再向上取整可寫為：⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Arrondi supérieur après arrondi inférieur d’un entier", "La propriété « Arrondi supérieur après arrondi inférieur d’un entier » donne: ⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Округление целого вниз, затем вверх", "Свойство «Округление целого вниз, затем вверх» выражается равенством: ⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Redondeo superior tras redondeo inferior de un entero", "La propiedad «Redondeo superior tras redondeo inferior de un entero» se expresa como: ⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("تقريب عدد صحيح لأسفل ثم لأعلى", "تُكتب خاصية «تقريب عدد صحيح لأسفل ثم لأعلى» كما يلي: ⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("整数の切り捨て後の切り上げ", "整数の切り捨て後の切り上げは次の式で表されます：⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("정수를 내림한 뒤 올림하기", "정수를 내림한 뒤 올림하기은 다음 식으로 나타납니다: ⌈⌊n⌋⌉ = n")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Làm tròn lên sau khi làm tròn xuống một số nguyên", "Tính chất «Làm tròn lên sau khi làm tròn xuống một số nguyên» được biểu diễn bởi: ⌈⌊n⌋⌉ = n")
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

impl SqrtOfSquareEqualsAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Square root of a square", "The principal square root of a real square is the absolute value of its base: sqrt(a²) = abs(a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("平方的平方根", "实数平方的算术平方根等于该实数的绝对值，即 sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("平方的平方根", "實數平方的算術平方根等於該實數的絕對值，即 sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Racine carrée d’un carré", "La racine carrée principale du carré d’un réel est sa valeur absolue: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Квадратный корень из квадрата", "Главный квадратный корень из квадрата вещественного числа равен его модулю: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Raíz cuadrada de un cuadrado", "La raíz cuadrada principal del cuadrado de un real es su valor absoluto: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجذر التربيعي للمربع", "الجذر التربيعي الرئيسي لمربع عدد حقيقي يساوي قيمته المطلقة: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("平方の平方根", "実数の平方の主平方根は、その実数の絶対値です：sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("제곱의 제곱근", "실수 제곱의 주제곱근은 그 실수의 절댓값입니다: sqrt(a²) = abs(a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Căn bậc hai của một bình phương", "Căn bậc hai chính của bình phương một số thực bằng giá trị tuyệt đối của số đó: sqrt(a²) = abs(a)")
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

impl QuotByOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Integer quotient by one", "The Integer quotient by one law gives: a quot 1 = a")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数除以一的商", "整数除以一的商可写为：a quot 1 = a")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("整數除以一的商", "整數除以一的商可寫為：a quot 1 = a")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Quotient entier par un", "La propriété « Quotient entier par un » donne: a quot 1 = a")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Целочисленное частное при делении на единицу", "Свойство «Целочисленное частное при делении на единицу» выражается равенством: a quot 1 = a")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Cociente entero entre uno", "La propiedad «Cociente entero entre uno» se expresa como: a quot 1 = a")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خارج القسمة الصحيح على واحد", "تُكتب خاصية «خارج القسمة الصحيح على واحد» كما يلي: a quot 1 = a")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一による整数除算", "一による整数除算は次の式で表されます：a quot 1 = a")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일로 나눈 정수 몫", "일로 나눈 정수 몫은 다음 식으로 나타납니다: a quot 1 = a")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Thương nguyên khi chia cho một", "Tính chất «Thương nguyên khi chia cho một» được biểu diễn bởi: a quot 1 = a")
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

impl QuotSelfOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Integer quotient by the same nonzero integer", "The Integer quotient by the same nonzero integer law gives: a quot a = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非零整数除以自身的商", "非零整数除以自身的商可写为：a quot a = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("非零整數除以自身的商", "非零整數除以自身的商可寫為：a quot a = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Quotient d’un entier non nul par lui-même", "La propriété « Quotient d’un entier non nul par lui-même » donne: a quot a = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Частное ненулевого целого при делении на себя", "Свойство «Частное ненулевого целого при делении на себя» выражается равенством: a quot a = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Cociente de un entero no nulo entre sí mismo", "La propiedad «Cociente de un entero no nulo entre sí mismo» se expresa como: a quot a = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خارج قسمة عدد صحيح غير صفري على نفسه", "تُكتب خاصية «خارج قسمة عدد صحيح غير صفري على نفسه» كما يلي: a quot a = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零でない整数の自身による整数除算", "零でない整数の自身による整数除算は次の式で表されます：a quot a = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영이 아닌 정수를 자기 자신으로 나눈 정수 몫", "영이 아닌 정수를 자기 자신으로 나눈 정수 몫은 다음 식으로 나타납니다: a quot a = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Thương nguyên của số nguyên khác không chia cho chính nó", "Tính chất «Thương nguyên của số nguyên khác không chia cho chính nó» được biểu diễn bởi: a quot a = 1")
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

impl LcmCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Commutativity of least common multiple", "Swapping the two arguments of least common multiple leaves the result unchanged: lcm(a,b) = lcm(b,a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最小公倍数的交换律", "交换最小公倍数的两个参数，结果不变，即 lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最小公倍數的交換律", "交換最小公倍數的兩個引數，結果不變，即 lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : plus petit commun multiple",
            "Permuter les arguments de l’opération « plus petit commun multiple » ne change pas le résultat: lcm(a,b) = lcm(b,a)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: наименьшее общее кратное",
            "Перестановка аргументов операции «наименьшее общее кратное» не меняет результат: lcm(a,b) = lcm(b,a)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: mínimo común múltiplo",
            "Intercambiar los argumentos de la operación «mínimo común múltiplo» no cambia el resultado: lcm(a,b) = lcm(b,a)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: المضاعف المشترك الأصغر", "تبديل وسيطي عملية «المضاعف المشترك الأصغر» لا يغيّر النتيجة: lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最小公倍数の交換法則", "最小公倍数の二つの引数を交換しても結果は変わりません：lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최소공배수의 교환법칙", "최소공배수의 두 인수를 바꾸어도 결과는 같습니다: lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính giao hoán của bội chung nhỏ nhất", "Đổi chỗ hai đối số của phép bội chung nhỏ nhất không làm thay đổi kết quả: lcm(a,b) = lcm(b,a)")
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

impl LcmIdempotentAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Least common multiple of equal integers", "The Least common multiple of equal integers law gives: lcm(a,a) = |a|")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("相同整数的最小公倍数", "相同整数的最小公倍数可写为：lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("相同整數的最小公倍數", "相同整數的最小公倍數可寫為：lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Plus petit commun multiple d’entiers égaux", "La propriété « Plus petit commun multiple d’entiers égaux » donne: lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Наименьшее общее кратное одинаковых целых чисел", "Свойство «Наименьшее общее кратное одинаковых целых чисел» выражается равенством: lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Mínimo común múltiplo de enteros iguales", "La propiedad «Mínimo común múltiplo de enteros iguales» se expresa como: lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المضاعف المشترك الأصغر لعددين صحيحين متساويين", "تُكتب خاصية «المضاعف المشترك الأصغر لعددين صحيحين متساويين» كما يلي: lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("等しい整数の最小公倍数", "等しい整数の最小公倍数は次の式で表されます：lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("같은 정수의 최소공배수", "같은 정수의 최소공배수은 다음 식으로 나타납니다: lcm(a,a) = |a|")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Bội chung nhỏ nhất của hai số nguyên bằng nhau", "Tính chất «Bội chung nhỏ nhất của hai số nguyên bằng nhau» được biểu diễn bởi: lcm(a,a) = |a|")
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

impl GcdCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Commutativity of greatest common divisor", "Swapping the two arguments of greatest common divisor leaves the result unchanged: gcd(a,b) = gcd(b,a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最大公约数的交换律", "交换最大公约数的两个参数，结果不变，即 gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最大公約數的交換律", "交換最大公約數的兩個引數，結果不變，即 gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : plus grand commun diviseur",
            "Permuter les arguments de l’opération « plus grand commun diviseur » ne change pas le résultat: gcd(a,b) = gcd(b,a)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: наибольший общий делитель",
            "Перестановка аргументов операции «наибольший общий делитель» не меняет результат: gcd(a,b) = gcd(b,a)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: máximo común divisor",
            "Intercambiar los argumentos de la operación «máximo común divisor» no cambia el resultado: gcd(a,b) = gcd(b,a)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: القاسم المشترك الأكبر", "تبديل وسيطي عملية «القاسم المشترك الأكبر» لا يغيّر النتيجة: gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最大公約数の交換法則", "最大公約数の二つの引数を交換しても結果は変わりません：gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최대공약수의 교환법칙", "최대공약수의 두 인수를 바꾸어도 결과는 같습니다: gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính giao hoán của ước chung lớn nhất", "Đổi chỗ hai đối số của phép ước chung lớn nhất không làm thay đổi kết quả: gcd(a,b) = gcd(b,a)")
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

impl GcdIdempotentAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Greatest common divisor of equal integers", "The Greatest common divisor of equal integers law gives: gcd(a,a) = |a|")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("相同整数的最大公约数", "相同整数的最大公约数可写为：gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("相同整數的最大公約數", "相同整數的最大公約數可寫為：gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Plus grand commun diviseur d’entiers égaux", "La propriété « Plus grand commun diviseur d’entiers égaux » donne: gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Наибольший общий делитель одинаковых целых чисел", "Свойство «Наибольший общий делитель одинаковых целых чисел» выражается равенством: gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Máximo común divisor de enteros iguales", "La propiedad «Máximo común divisor de enteros iguales» se expresa como: gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القاسم المشترك الأكبر لعددين صحيحين متساويين", "تُكتب خاصية «القاسم المشترك الأكبر لعددين صحيحين متساويين» كما يلي: gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("等しい整数の最大公約数", "等しい整数の最大公約数は次の式で表されます：gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("같은 정수의 최대공약수", "같은 정수의 최대공약수은 다음 식으로 나타납니다: gcd(a,a) = |a|")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Ước chung lớn nhất của hai số nguyên bằng nhau", "Tính chất «Ước chung lớn nhất của hai số nguyên bằng nhau» được biểu diễn bởi: gcd(a,a) = |a|")
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

impl GcdRightZeroAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Greatest common divisor with second argument zero", "The Greatest common divisor with second argument zero law gives: gcd(a,0) = |a|")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("第二参数为零的最大公约数", "第二参数为零的最大公约数可写为：gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("第二引數為零的最大公約數", "第二引數為零的最大公約數可寫為：gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Plus grand commun diviseur avec second argument nul", "La propriété « Plus grand commun diviseur avec second argument nul » donne: gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Наибольший общий делитель с нулевым вторым аргументом", "Свойство «Наибольший общий делитель с нулевым вторым аргументом» выражается равенством: gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Máximo común divisor con segundo argumento cero", "La propiedad «Máximo común divisor con segundo argumento cero» se expresa como: gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القاسم المشترك الأكبر مع وسيط ثانٍ صفري", "تُكتب خاصية «القاسم المشترك الأكبر مع وسيط ثانٍ صفري» كما يلي: gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("第二引数が零の最大公約数", "第二引数が零の最大公約数は次の式で表されます：gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("두 번째 인수가 영인 최대공약수", "두 번째 인수가 영인 최대공약수은 다음 식으로 나타납니다: gcd(a,0) = |a|")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Ước chung lớn nhất với đối số thứ hai bằng không", "Tính chất «Ước chung lớn nhất với đối số thứ hai bằng không» được biểu diễn bởi: gcd(a,0) = |a|")
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

impl GcdLeftZeroAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Greatest common divisor with first argument zero", "The Greatest common divisor with first argument zero law gives: gcd(0,a) = |a|")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("第一参数为零的最大公约数", "第一参数为零的最大公约数可写为：gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("第一引數為零的最大公約數", "第一引數為零的最大公約數可寫為：gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Plus grand commun diviseur avec premier argument nul", "La propriété « Plus grand commun diviseur avec premier argument nul » donne: gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Наибольший общий делитель с нулевым первым аргументом", "Свойство «Наибольший общий делитель с нулевым первым аргументом» выражается равенством: gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Máximo común divisor con primer argumento cero", "La propiedad «Máximo común divisor con primer argumento cero» se expresa como: gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القاسم المشترك الأكبر مع وسيط أول صفري", "تُكتب خاصية «القاسم المشترك الأكبر مع وسيط أول صفري» كما يلي: gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("第一引数が零の最大公約数", "第一引数が零の最大公約数は次の式で表されます：gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("첫 번째 인수가 영인 최대공약수", "첫 번째 인수가 영인 최대공약수은 다음 식으로 나타납니다: gcd(0,a) = |a|")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Ước chung lớn nhất với đối số thứ nhất bằng không", "Tính chất «Ước chung lớn nhất với đối số thứ nhất bằng không» được biểu diễn bởi: gcd(0,a) = |a|")
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

impl FactorialSuccessorBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Factorial recurrence", "The Factorial recurrence law gives: (n+1)! = (n+1)·n!")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("阶乘递推", "阶乘递推可写为：(n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("階乘遞推", "階乘遞推可寫為：(n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Récurrence de la factorielle", "La propriété « Récurrence de la factorielle » donne: (n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Рекуррентная формула факториала", "Свойство «Рекуррентная формула факториала» выражается равенством: (n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Recurrencia del factorial", "La propiedad «Recurrencia del factorial» se expresa como: (n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("العلاقة التكرارية للمضروب", "تُكتب خاصية «العلاقة التكرارية للمضروب» كما يلي: (n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("階乗の漸化式", "階乗の漸化式は次の式で表されます：(n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("계승의 점화식", "계승의 점화식은 다음 식으로 나타납니다: (n+1)! = (n+1)·n!")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Công thức truy hồi của giai thừa", "Tính chất «Công thức truy hồi của giai thừa» được biểu diễn bởi: (n+1)! = (n+1)·n!")
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

impl AbsNonnegEqualsSelfBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Absolute value of a nonnegative real", "The Absolute value of a nonnegative real law gives: abs(a) = a (a ≥ 0)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非负实数的绝对值", "非负实数的绝对值可写为，即 abs(a) = a (a ≥ 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非負實數的絕對值",
            "非負實數的絕對值可寫為，即 abs(a) = a (a ≥ 0)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur absolue d’un réel positif ou nul", "La propriété « Valeur absolue d’un réel positif ou nul » donne: abs(a) = a (a ≥ 0)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Модуль неотрицательного вещественного числа", "Свойство «Модуль неотрицательного вещественного числа» выражается равенством: abs(a) = a (a ≥ 0)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor absoluto de un real no negativo", "La propiedad «Valor absoluto de un real no negativo» se expresa como: abs(a) = a (a ≥ 0)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القيمة المطلقة لعدد حقيقي غير سالب", "تُكتب خاصية «القيمة المطلقة لعدد حقيقي غير سالب» كما يلي: abs(a) = a (a ≥ 0)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負の実数の絶対値",
            "非負の実数の絶対値は次の式で表されます：abs(a) = a (a ≥ 0)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음이 아닌 실수의 절댓값",
            "음이 아닌 실수의 절댓값은 다음 식으로 나타납니다：abs(a) = a (a ≥ 0)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị tuyệt đối của số thực không âm", "Tính chất «Giá trị tuyệt đối của số thực không âm» được biểu diễn bởi: abs(a) = a (a ≥ 0)")
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

impl AbsNonposEqualsNegationBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Absolute value of a nonpositive real",
            "The Absolute value of a nonpositive real law gives: abs(a) = -a (a ≤ 0)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非正实数的绝对值",
            "非正实数的绝对值可写为，即 abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非正實數的絕對值",
            "非正實數的絕對值可寫為，即 abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Valeur absolue d’un réel négatif ou nul",
            "La propriété « Valeur absolue d’un réel négatif ou nul » donne: abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Модуль неположительного вещественного числа",
            "Свойство «Модуль неположительного вещественного числа» выражается равенством: abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Valor absoluto de un real no positivo",
            "La propiedad «Valor absoluto de un real no positivo» se expresa como: abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة المطلقة لعدد حقيقي غير موجب",
            "تُكتب خاصية «القيمة المطلقة لعدد حقيقي غير موجب» كما يلي: abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非正の実数の絶対値",
            "非正の実数の絶対値は次の式で表されます：abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양이 아닌 실수의 절댓값",
            "양이 아닌 실수의 절댓값은 다음 식으로 나타납니다：abs(a) = -a (a ≤ 0)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị tuyệt đối của số thực không dương",
            "Tính chất «Giá trị tuyệt đối của số thực không dương» được biểu diễn bởi: abs(a) = -a (a ≤ 0)",
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

impl SignOfPositiveBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sign of a positive real number",
            "The Sign of a positive real number law gives: sign(a) = 1 (a > 0)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正实数的符号", "正实数的符号可写为，即 sign(a) = 1 (a > 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正實數的符號", "正實數的符號可寫為，即 sign(a) = 1 (a > 0)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Signe d’un réel positif",
            "La propriété « Signe d’un réel positif » donne: sign(a) = 1 (a > 0)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Знак положительного вещественного числа",
            "Свойство «Знак положительного вещественного числа» выражается равенством: sign(a) = 1 (a > 0)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Signo de un real positivo",
            "La propiedad «Signo de un real positivo» se expresa como: sign(a) = 1 (a > 0)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("إشارة عدد حقيقي موجب", "تُكتب خاصية «إشارة عدد حقيقي موجب» كما يلي: sign(a) = 1 (a > 0)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の実数の符号",
            "正の実数の符号は次の式で表されます：sign(a) = 1 (a > 0)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("양의 실수의 부호", "양의 실수의 부호은 다음 식으로 나타납니다：sign(a) = 1 (a > 0)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Dấu của số thực dương",
            "Tính chất «Dấu của số thực dương» được biểu diễn bởi: sign(a) = 1 (a > 0)",
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

impl SignOfNegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sign of a negative real number",
            "The Sign of a negative real number law gives: sign(a) = -1 (a < 0)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("负实数的符号", "负实数的符号可写为，即 sign(a) = -1 (a < 0)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("負實數的符號", "負實數的符號可寫為，即 sign(a) = -1 (a < 0)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Signe d’un réel négatif",
            "La propriété « Signe d’un réel négatif » donne: sign(a) = -1 (a < 0)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Знак отрицательного вещественного числа",
            "Свойство «Знак отрицательного вещественного числа» выражается равенством: sign(a) = -1 (a < 0)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Signo de un real negativo",
            "La propiedad «Signo de un real negativo» se expresa como: sign(a) = -1 (a < 0)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("إشارة عدد حقيقي سالب", "تُكتب خاصية «إشارة عدد حقيقي سالب» كما يلي: sign(a) = -1 (a < 0)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "負の実数の符号",
            "負の実数の符号は次の式で表されます：sign(a) = -1 (a < 0)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("음의 실수의 부호", "음의 실수의 부호은 다음 식으로 나타납니다：sign(a) = -1 (a < 0)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Dấu của số thực âm", "Tính chất «Dấu của số thực âm» được biểu diễn bởi: sign(a) = -1 (a < 0)")
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

impl MaxRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Maximum selects the larger right operand",
            "The Maximum selects the larger right operand law gives: a ≤ b ⇒ max(a,b) = b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最大值选取较大的右操作数",
            "最大值选取较大的右操作数可写为，即 a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最大值選取較大的右運算元",
            "最大值選取較大的右運算元可寫為，即 a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Maximum égal à l’opérande droit plus grand",
            "La propriété « Maximum égal à l’opérande droit plus grand » donne: a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Максимум выбирает больший правый операнд",
            "Свойство «Максимум выбирает больший правый операнд» выражается равенством: a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Máximo selecciona el operando derecho mayor",
            "La propiedad «Máximo selecciona el operando derecho mayor» se expresa como: a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة العظمى تختار المعامل الأيمن الأكبر",
            "تُكتب خاصية «القيمة العظمى تختار المعامل الأيمن الأكبر» كما يلي: a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最大値として大きい右の項を選択",
            "最大値として大きい右の項を選択は次の式で表されます：a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최댓값으로 더 큰 오른쪽 피연산자 선택",
            "최댓값으로 더 큰 오른쪽 피연산자 선택은 다음 식으로 나타납니다：a ≤ b ⇒ max(a,b) = b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị lớn nhất chọn toán hạng phải lớn hơn",
            "Tính chất «Giá trị lớn nhất chọn toán hạng phải lớn hơn» được biểu diễn bởi: a ≤ b ⇒ max(a,b) = b",
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

impl MaxLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Maximum selects the larger left operand",
            "The Maximum selects the larger left operand law gives: b ≤ a ⇒ max(a,b) = a",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最大值选取较大的左操作数",
            "最大值选取较大的左操作数可写为，即 b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最大值選取較大的左運算元",
            "最大值選取較大的左運算元可寫為，即 b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Maximum égal à l’opérande gauche plus grand",
            "La propriété « Maximum égal à l’opérande gauche plus grand » donne: b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Максимум выбирает больший левый операнд",
            "Свойство «Максимум выбирает больший левый операнд» выражается равенством: b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Máximo selecciona el operando izquierdo mayor",
            "La propiedad «Máximo selecciona el operando izquierdo mayor» se expresa como: b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة العظمى تختار المعامل الأيسر الأكبر",
            "تُكتب خاصية «القيمة العظمى تختار المعامل الأيسر الأكبر» كما يلي: b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最大値として大きい左の項を選択",
            "最大値として大きい左の項を選択は次の式で表されます：b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최댓값으로 더 큰 왼쪽 피연산자 선택",
            "최댓값으로 더 큰 왼쪽 피연산자 선택은 다음 식으로 나타납니다：b ≤ a ⇒ max(a,b) = a",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị lớn nhất chọn toán hạng trái lớn hơn",
            "Tính chất «Giá trị lớn nhất chọn toán hạng trái lớn hơn» được biểu diễn bởi: b ≤ a ⇒ max(a,b) = a",
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

impl MinLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Minimum selects the smaller left operand",
            "The Minimum selects the smaller left operand law gives: a ≤ b ⇒ min(a,b) = a",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最小值选取较小的左操作数",
            "最小值选取较小的左操作数可写为，即 a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最小值選取較小的左運算元",
            "最小值選取較小的左運算元可寫為，即 a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Minimum égal à l’opérande gauche plus petit",
            "La propriété « Minimum égal à l’opérande gauche plus petit » donne: a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Минимум выбирает меньший левый операнд",
            "Свойство «Минимум выбирает меньший левый операнд» выражается равенством: a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Mínimo selecciona el operando izquierdo menor",
            "La propiedad «Mínimo selecciona el operando izquierdo menor» se expresa como: a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة الصغرى تختار المعامل الأيسر الأصغر",
            "تُكتب خاصية «القيمة الصغرى تختار المعامل الأيسر الأصغر» كما يلي: a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最小値として小さい左の項を選択",
            "最小値として小さい左の項を選択は次の式で表されます：a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최솟값으로 더 작은 왼쪽 피연산자 선택",
            "최솟값으로 더 작은 왼쪽 피연산자 선택은 다음 식으로 나타납니다：a ≤ b ⇒ min(a,b) = a",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị nhỏ nhất chọn toán hạng trái nhỏ hơn",
            "Tính chất «Giá trị nhỏ nhất chọn toán hạng trái nhỏ hơn» được biểu diễn bởi: a ≤ b ⇒ min(a,b) = a",
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

impl MinRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Minimum selects the smaller right operand",
            "The Minimum selects the smaller right operand law gives: b ≤ a ⇒ min(a,b) = b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最小值选取较小的右操作数",
            "最小值选取较小的右操作数可写为，即 b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最小值選取較小的右運算元",
            "最小值選取較小的右運算元可寫為，即 b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Minimum égal à l’opérande droit plus petit",
            "La propriété « Minimum égal à l’opérande droit plus petit » donne: b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Минимум выбирает меньший правый операнд",
            "Свойство «Минимум выбирает меньший правый операнд» выражается равенством: b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Mínimo selecciona el operando derecho menor",
            "La propiedad «Mínimo selecciona el operando derecho menor» se expresa como: b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة الصغرى تختار المعامل الأيمن الأصغر",
            "تُكتب خاصية «القيمة الصغرى تختار المعامل الأيمن الأصغر» كما يلي: b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最小値として小さい右の項を選択",
            "最小値として小さい右の項を選択は次の式で表されます：b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최솟값으로 더 작은 오른쪽 피연산자 선택",
            "최솟값으로 더 작은 오른쪽 피연산자 선택은 다음 식으로 나타납니다：b ≤ a ⇒ min(a,b) = b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị nhỏ nhất chọn toán hạng phải nhỏ hơn",
            "Tính chất «Giá trị nhỏ nhất chọn toán hạng phải nhỏ hơn» được biểu diễn bởi: b ≤ a ⇒ min(a,b) = b",
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

impl GcdDividesArgumentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Greatest common divisor divides both arguments",
            "The greatest common divisor divides each of the two integer arguments",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "gcd 整除",
            "gcd(a,b) 整除 a（以及 b）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("gcd 整除", "gcd(a,b) 整除 a 及 b")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Divisibilité par gcd",
            "gcd(a,b) divise a et b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Делимость на gcd",
            "gcd(a,b) делит a и b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Divisibilidad por gcd",
            "gcd(a,b) divide a y b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("القسمة على gcd", "gcd(a,b) يقسم a وb")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "gcd による整除",
            "gcd(a,b) は a と b を割り切ります",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "gcd 나눔",
            "gcd(a,b)는 a와 b를 나눕니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Chia hết bởi gcd",
            "gcd(a,b) chia hết a và b",
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

impl ProductModFactorZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Remainder of an integer multiple",
            "The Remainder of an integer multiple law gives: (k·n) mod n = 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数倍除以因子的余数", "整数倍除以因子的余数可写为：(k·n) mod n = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("整數倍除以因子的餘數", "整數倍除以因子的餘數可寫為：(k·n) mod n = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Reste d’un multiple entier",
            "La propriété « Reste d’un multiple entier » donne: (k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Остаток целого кратного",
            "Свойство «Остаток целого кратного» выражается равенством: (k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Resto de un múltiplo entero",
            "La propiedad «Resto de un múltiplo entero» se expresa como: (k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "باقي قسمة مضاعف صحيح",
            "تُكتب خاصية «باقي قسمة مضاعف صحيح» كما يلي: (k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "整数倍の剰余",
            "整数倍の剰余は次の式で表されます：(k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "정수 배수의 나머지",
            "정수 배수의 나머지은 다음 식으로 나타납니다: (k·n) mod n = 0",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số dư của một bội nguyên",
            "Tính chất «Số dư của một bội nguyên» được biểu diễn bởi: (k·n) mod n = 0",
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

impl EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Antisymmetry of real order",
            "The Antisymmetry of real order law gives: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实数顺序的反对称性",
            "实数顺序的反对称性可写为：a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "實數順序的反對稱性",
            "實數順序的反對稱性可寫為：a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Antisymétrie de l’ordre réel",
            "La propriété « Antisymétrie de l’ordre réel » donne: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Антисимметричность вещественного порядка",
            "Свойство «Антисимметричность вещественного порядка» выражается равенством: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Antisimetría del orden real",
            "La propiedad «Antisimetría del orden real» se expresa como: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "خاصية ضد التناظر للترتيب الحقيقي",
            "تُكتب خاصية «خاصية ضد التناظر للترتيب الحقيقي» كما يلي: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "実数の順序の反対称性",
            "実数の順序の反対称性は次の式で表されます：a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "실수 순서의 반대칭성",
            "실수 순서의 반대칭성은 다음 식으로 나타납니다: a ≤ b ∧ b ≤ a ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phản đối xứng của thứ tự thực",
            "Tính chất «Tính phản đối xứng của thứ tự thực» được biểu diễn bởi: a ≤ b ∧ b ≤ a ⇒ a = b",
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

impl DiffZeroFromEqualOperandsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Difference of equal operands is zero",
            "The Difference of equal operands is zero law gives: a = b ⇒ a − b = 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "相等的数之差为零",
            "相等的数之差为零可写为：a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "相等的數之差為零",
            "相等的數之差為零可寫為：a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence nulle d’opérandes égaux",
            "La propriété « Différence nulle d’opérandes égaux » donne: a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Разность равных чисел равна нулю",
            "Свойство «Разность равных чисел равна нулю» выражается равенством: a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia de operandos iguales es cero",
            "La propiedad «Diferencia de operandos iguales es cero» se expresa como: a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فرق عددين متساويين يساوي صفرًا",
            "تُكتب خاصية «فرق عددين متساويين يساوي صفرًا» كما يلي: a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "等しい数の差は零",
            "等しい数の差は零は次の式で表されます：a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "같은 수의 차는 영",
            "같은 수의 차는 영은 다음 식으로 나타납니다: a = b ⇒ a − b = 0",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu của hai toán hạng bằng nhau là không",
            "Tính chất «Hiệu của hai toán hạng bằng nhau là không» được biểu diễn bởi: a = b ⇒ a − b = 0",
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

impl EqualFromKnownDifferenceZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Zero difference implies equality",
            "The Zero difference implies equality law gives: a − b = 0 ⇒ a = b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "差为零推出相等",
            "差为零推出相等可写为：a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "差為零推出相等",
            "差為零推出相等可寫為：a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence nulle et égalité",
            "La propriété « Différence nulle et égalité » donne: a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нулевая разность влечёт равенство",
            "Свойство «Нулевая разность влечёт равенство» выражается равенством: a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia cero implica igualdad",
            "La propiedad «Diferencia cero implica igualdad» se expresa como: a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الفرق الصفري يستلزم التساوي",
            "تُكتب خاصية «الفرق الصفري يستلزم التساوي» كما يلي: a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "差が零なら等しい",
            "差が零なら等しいは次の式で表されます：a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "차가 영이면 같음",
            "차가 영이면 같음은 다음 식으로 나타납니다: a − b = 0 ⇒ a = b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu bằng không suy ra bằng nhau",
            "Tính chất «Hiệu bằng không suy ra bằng nhau» được biểu diễn bởi: a − b = 0 ⇒ a = b",
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

impl ZeroProductCancelBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "zero product",
            "a·b = 0 with a≠0 gives b = 0 (and symmetrically)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "零因子消元",
            "a·b = 0 且 a≠0 则 b = 0（对称亦然）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "零乘積",
            "a·b = 0 且 a≠0 推出 b = 0（對稱情況亦然）",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit nul",
            "a·b = 0 avec a≠0 implique b = 0 (et symétriquement)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нулевое произведение",
            "a·b = 0 при a≠0 влечёт b = 0 (и симметрично)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto cero",
            "a·b = 0 con a≠0 implica b = 0 (y simétricamente)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل ضرب صفري",
            "a·b = 0 مع a≠0 تستلزم b = 0 (وبالتناظر أيضًا)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "積がゼロ",
            "a·b = 0 かつ a≠0 なら b = 0 です（対称の場合も同様）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "곱이 0",
            "a·b = 0이고 a≠0이면 b = 0입니다(대칭적으로도 성립)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích bằng không",
            "a·b = 0 với a≠0 suy ra b = 0 (và đối xứng)",
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

impl SignOfNegationBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Sign of an opposite number", "The Sign of an opposite number law gives: sign(-a) = -sign(a)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("相反数的符号", "相反数的符号可写为：sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("相反數的符號", "相反數的符號可寫為：sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Signe d’un opposé", "La propriété « Signe d’un opposé » donne: sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Знак противоположного числа", "Свойство «Знак противоположного числа» выражается равенством: sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Signo de un opuesto", "La propiedad «Signo de un opuesto» se expresa como: sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("إشارة العدد المعاكس", "تُكتب خاصية «إشارة العدد المعاكس» كما يلي: sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("符号反転した数の符号", "符号反転した数の符号は次の式で表されます：sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("반대 수의 부호", "반대 수의 부호은 다음 식으로 나타납니다: sign(-a) = -sign(a)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Dấu của số đối", "Tính chất «Dấu của số đối» được biểu diễn bởi: sign(-a) = -sign(a)")
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

impl SignTimesAbsEqualsArgBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Recovering a real number from its sign and absolute value", "The Recovering a real number from its sign and absolute value law gives: sign(a)·|a| = a")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由符号和绝对值还原实数", "由符号和绝对值还原实数可写为：sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("由符號和絕對值還原實數", "由符號和絕對值還原實數可寫為：sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Reconstitution d’un réel par son signe et sa valeur absolue", "La propriété « Reconstitution d’un réel par son signe et sa valeur absolue » donne: sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Восстановление числа по знаку и модулю", "Свойство «Восстановление числа по знаку и модулю» выражается равенством: sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Recuperación de un real mediante signo y valor absoluto", "La propiedad «Recuperación de un real mediante signo y valor absoluto» se expresa como: sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("استعادة العدد الحقيقي من إشارته وقيمته المطلقة", "تُكتب خاصية «استعادة العدد الحقيقي من إشارته وقيمته المطلقة» كما يلي: sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("符号と絶対値による実数の復元", "符号と絶対値による実数の復元は次の式で表されます：sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("부호와 절댓값으로 실수 복원", "부호와 절댓값으로 실수 복원은 다음 식으로 나타납니다: sign(a)·|a| = a")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Khôi phục số thực từ dấu và giá trị tuyệt đối", "Tính chất «Khôi phục số thực từ dấu và giá trị tuyệt đối» được biểu diễn bởi: sign(a)·|a| = a")
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

impl AbsEqualsSignTimesArgBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Absolute value as sign times the real argument",
            "The Absolute value as sign times the real argument law gives: |a| = sign(a)·a",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "绝对值等于符号乘以原实数",
            "绝对值等于符号乘以原实数可写为：|a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "絕對值等於符號乘以原實數",
            "絕對值等於符號乘以原實數可寫為：|a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Valeur absolue comme signe multiplié par le réel",
            "La propriété « Valeur absolue comme signe multiplié par le réel » donne: |a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Модуль как произведение знака и аргумента",
            "Свойство «Модуль как произведение знака и аргумента» выражается равенством: |a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Valor absoluto como signo por el argumento real",
            "La propiedad «Valor absoluto como signo por el argumento real» se expresa como: |a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة المطلقة كحاصل ضرب الإشارة في العدد الحقيقي",
            "تُكتب خاصية «القيمة المطلقة كحاصل ضرب الإشارة في العدد الحقيقي» كما يلي: |a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "符号と元の実数の積による絶対値",
            "符号と元の実数の積による絶対値は次の式で表されます：|a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "부호와 원래 실수의 곱으로 표현한 절댓값",
            "부호와 원래 실수의 곱으로 표현한 절댓값은 다음 식으로 나타납니다: |a| = sign(a)·a",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị tuyệt đối bằng dấu nhân với đối số thực",
            "Tính chất «Giá trị tuyệt đối bằng dấu nhân với đối số thực» được biểu diễn bởi: |a| = sign(a)·a",
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

impl SignOfProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Sign of a product", "The Sign of a product law gives: sign(a·b) = sign(a)·sign(b)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("积的符号", "积的符号可写为：sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("積的符號", "積的符號可寫為：sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Signe d’un produit", "La propriété « Signe d’un produit » donne: sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Знак произведения", "Свойство «Знак произведения» выражается равенством: sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Signo de un producto", "La propiedad «Signo de un producto» se expresa como: sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("إشارة حاصل الضرب", "تُكتب خاصية «إشارة حاصل الضرب» كما يلي: sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("積の符号", "積の符号は次の式で表されます：sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("곱의 부호", "곱의 부호은 다음 식으로 나타납니다: sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Dấu của một tích", "Tính chất «Dấu của một tích» được biểu diễn bởi: sign(a·b) = sign(a)·sign(b)")
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

impl SubtractionFromKnownAdditionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Recovering an addend by subtraction",
            "The Recovering an addend by subtraction law gives: a = b + c ⇒ c = a − b",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由加法关系求差",
            "由加法关系求差可写为：a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由加法關係求差",
            "由加法關係求差可寫為：a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Récupération d’un terme par soustraction",
            "La propriété « Récupération d’un terme par soustraction » donne: a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Восстановление слагаемого вычитанием",
            "Свойство «Восстановление слагаемого вычитанием» выражается равенством: a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Recuperación de un sumando por resta",
            "La propiedad «Recuperación de un sumando por resta» se expresa como: a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "استعادة حد الجمع بالطرح",
            "تُكتب خاصية «استعادة حد الجمع بالطرح» كما يلي: a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "減算による加数の復元",
            "減算による加数の復元は次の式で表されます：a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "뺄셈으로 덧셈 항 복원",
            "뺄셈으로 덧셈 항 복원은 다음 식으로 나타납니다: a = b + c ⇒ c = a − b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khôi phục số hạng bằng phép trừ",
            "Tính chất «Khôi phục số hạng bằng phép trừ» được biểu diễn bởi: a = b + c ⇒ c = a − b",
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

impl QuotEuclideanDecompositionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Euclidean quotient and remainder decomposition",
            "The Euclidean quotient and remainder decomposition law gives: a = (a quot n)·n + (a mod n)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "欧几里得商余分解",
            "欧几里得商余分解可写为：a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "歐幾里得商餘分解",
            "歐幾里得商餘分解可寫為：a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Décomposition euclidienne en quotient et reste",
            "La propriété « Décomposition euclidienne en quotient et reste » donne: a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Разложение через евклидовы частное и остаток",
            "Свойство «Разложение через евклидовы частное и остаток» выражается равенством: a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Descomposición euclídea en cociente y resto",
            "La propiedad «Descomposición euclídea en cociente y resto» se expresa como: a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التحليل الإقليدي إلى خارج القسمة والباقي",
            "تُكتب خاصية «التحليل الإقليدي إلى خارج القسمة والباقي» كما يلي: a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ユークリッド除算の商と余りによる分解",
            "ユークリッド除算の商と余りによる分解は次の式で表されます：a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유클리드 몫과 나머지 분해",
            "유클리드 몫과 나머지 분해은 다음 식으로 나타납니다: a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phân tích Euclid theo thương và số dư",
            "Tính chất «Phân tích Euclid theo thương và số dư» được biểu diễn bởi: a = (a quot n)·n + (a mod n)",
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

impl ModDividendMinusRemainderZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "mod remainder",
            "a − (a mod n) is divisible by n",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "模余数",
            "a − (a mod n) 可被 n 整除",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "模運算餘數",
            "a − (a mod n) 可被 n 整除",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Reste modulaire",
            "a − (a mod n) est divisible par n",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Остаток по модулю",
            "a − (a mod n) делится на n",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Resto modular",
            "a − (a mod n) es divisible por n",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "باقي القسمة",
            "a − (a mod n) يقبل القسمة على n",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "剰余",
            "a − (a mod n) は n で割り切れます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "나머지",
            "a − (a mod n)은 n으로 나누어집니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số dư",
            "a − (a mod n) chia hết cho n",
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

impl SquareSumComponentZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "square-sum zero",
            "a² + b² = 0 forces a = 0 and b = 0 (over reals)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "平方和为零",
            "在实数上 a² + b² = 0 蕴含 a = 0 且 b = 0",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "平方和為零",
            "對實數，a² + b² = 0 推出 a = 0 且 b = 0",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme de carrés nulle",
            "Sur les réels, a² + b² = 0 implique a = 0 et b = 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нулевая сумма квадратов",
            "Для вещественных a² + b² = 0 влечёт a = 0 и b = 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma de cuadrados cero",
            "En los reales, a² + b² = 0 implica a = 0 y b = 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع مربعات صفري",
            "للأعداد الحقيقية a² + b² = 0 تستلزم a = 0 وb = 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "平方和がゼロ",
            "実数では a² + b² = 0 から a = 0 かつ b = 0 を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "제곱합이 0",
            "실수에서 a² + b² = 0이면 a = 0 및 b = 0입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tổng bình phương bằng không",
            "Trên số thực, a² + b² = 0 suy ra a = 0 và b = 0",
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

impl MinusOneOddNaturalPowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Odd natural power of minus one",
            "(-1)^n = -1 for odd natural n",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "负一的奇自然数次幂",
            "对奇自然数 n，(-1)^n = -1",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "(-1) 的奇數次方",
            "(-1)^n = -1（n 為奇自然數）",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance impaire de (-1)",
            "(-1)^n = -1 pour n naturel impair",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нечётная степень (-1)",
            "(-1)^n = -1 для нечётного натурального n",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia impar de (-1)",
            "(-1)^n = -1 para n natural impar",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قوة فردية لـ (-1)",
            "(-1)^n = -1 للعدد الطبيعي الفردي n",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "(-1) の奇数乗",
            "(-1)^n = -1（n は奇数の自然数）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "(-1)의 홀수 거듭제곱",
            "(-1)^n = -1(n은 홀수 자연수)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa lẻ của (-1)",
            "(-1)^n = -1 với n tự nhiên lẻ",
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

impl LcmGcdProductAbsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Product of least common multiple and greatest common divisor", "The Product of least common multiple and greatest common divisor law gives: lcm(a,b)·gcd(a,b) = |a·b|")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("最小公倍数与最大公约数的乘积", "最小公倍数与最大公约数的乘积可写为：lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("最小公倍數與最大公約數的乘積", "最小公倍數與最大公約數的乘積可寫為：lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Produit du PPCM et du PGCD", "La propriété « Produit du PPCM et du PGCD » donne: lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Произведение НОК и НОД", "Свойство «Произведение НОК и НОД» выражается равенством: lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Producto del mínimo común múltiplo y el máximo común divisor", "La propiedad «Producto del mínimo común múltiplo y el máximo común divisor» se expresa como: lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("حاصل ضرب المضاعف المشترك الأصغر والقاسم المشترك الأكبر", "تُكتب خاصية «حاصل ضرب المضاعف المشترك الأصغر والقاسم المشترك الأكبر» كما يلي: lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("最小公倍数と最大公約数の積", "最小公倍数と最大公約数の積は次の式で表されます：lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("최소공배수와 최대공약수의 곱", "최소공배수와 최대공약수의 곱은 다음 식으로 나타납니다: lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tích của bội chung nhỏ nhất và ước chung lớn nhất", "Tính chất «Tích của bội chung nhỏ nhất và ước chung lớn nhất» được biểu diễn bởi: lcm(a,b)·gcd(a,b) = |a·b|")
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

impl UnionEmptyRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("union with the empty set", "Union with the empty set leaves the other set unchanged: A ∪ ∅ = A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("与空集作并集", "一个集合与空集的并集等于原集合，即 A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("與空集作聯集", "一個集合與空集的聯集等於原集合，即 A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("union avec l’ensemble vide", "L’union avec l’ensemble vide redonne l’autre ensemble: A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Операция «объединение» с пустым множеством", "Объединение с пустым множеством равно исходному множеству: A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("unión con el conjunto vacío", "La unión con el conjunto vacío devuelve el otro conjunto: A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عملية «الاتحاد» مع المجموعة الخالية", "اتحاد مجموعة مع المجموعة الخالية يساوي المجموعة الأصلية: A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合との和集合", "空集合との和集合は元の集合です：A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합과의 합집합", "공집합과의 합집합은 원래 집합입니다: A ∪ ∅ = A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phép hợp với tập rỗng", "Hợp với tập rỗng bằng tập ban đầu: A ∪ ∅ = A")
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

impl UnionEmptyLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("union with the empty set", "Union with the empty set leaves the other set unchanged: ∅ ∪ A = A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("与空集作并集", "一个集合与空集的并集等于原集合，即 ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("與空集作聯集", "一個集合與空集的聯集等於原集合，即 ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("union avec l’ensemble vide", "L’union avec l’ensemble vide redonne l’autre ensemble: ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Операция «объединение» с пустым множеством", "Объединение с пустым множеством равно исходному множеству: ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("unión con el conjunto vacío", "La unión con el conjunto vacío devuelve el otro conjunto: ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عملية «الاتحاد» مع المجموعة الخالية", "اتحاد مجموعة مع المجموعة الخالية يساوي المجموعة الأصلية: ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合との和集合", "空集合との和集合は元の集合です：∅ ∪ A = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합과의 합집합", "공집합과의 합집합은 원래 집합입니다: ∅ ∪ A = A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phép hợp với tập rỗng", "Hợp với tập rỗng bằng tập ban đầu: ∅ ∪ A = A")
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

impl IntersectEmptyRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("intersection with the empty set", "Intersection with the empty set is empty: A ∩ ∅ = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("与空集作交集", "任何集合与空集的交集都是空集，即 A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("與空集作交集", "任何集合與空集的交集都是空集，即 A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("intersection avec l’ensemble vide", "L’intersection avec l’ensemble vide est vide: A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Операция «пересечение» с пустым множеством", "Пересечение с пустым множеством пусто: A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("intersección con el conjunto vacío", "La intersección con el conjunto vacío es vacía: A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عملية «التقاطع» مع المجموعة الخالية", "تقاطع أي مجموعة مع المجموعة الخالية هو المجموعة الخالية: A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合との共通部分", "空集合との共通部分は空集合です：A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합과의 교집합", "공집합과의 교집합은 공집합입니다: A ∩ ∅ = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phép giao với tập rỗng", "Giao với tập rỗng là tập rỗng: A ∩ ∅ = ∅")
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

impl IntersectEmptyLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("intersection with the empty set", "Intersection with the empty set is empty: ∅ ∩ A = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("与空集作交集", "任何集合与空集的交集都是空集，即 ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("與空集作交集", "任何集合與空集的交集都是空集，即 ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("intersection avec l’ensemble vide", "L’intersection avec l’ensemble vide est vide: ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Операция «пересечение» с пустым множеством", "Пересечение с пустым множеством пусто: ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("intersección con el conjunto vacío", "La intersección con el conjunto vacío es vacía: ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عملية «التقاطع» مع المجموعة الخالية", "تقاطع أي مجموعة مع المجموعة الخالية هو المجموعة الخالية: ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合との共通部分", "空集合との共通部分は空集合です：∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합과의 교집합", "공집합과의 교집합은 공집합입니다: ∅ ∩ A = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phép giao với tập rỗng", "Giao với tập rỗng là tập rỗng: ∅ ∩ A = ∅")
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

impl SetMinusSelfEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Difference of a set with itself", "Removing all elements of a set leaves the empty set: A \\ A = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("集合减去自身", "从集合中去掉它的全部元素，得到空集，即 A \\ A = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("集合減去自身", "從集合中去掉它的全部元素，得到空集，即 A \\ A = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Différence d’un ensemble avec lui-même", "Retirer tous les éléments d’un ensemble donne l’ensemble vide: A \\ A = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Разность множества с самим собой", "Удаление всех элементов множества даёт пустое множество: A \\ A = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Diferencia de un conjunto consigo mismo", "Eliminar todos los elementos de un conjunto deja el conjunto vacío: A \\ A = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("طرح المجموعة من نفسها", "إزالة جميع عناصر مجموعة تترك المجموعة الخالية: A \\ A = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("集合自身との差集合", "集合からすべての要素を除くと空集合になります：A \\ A = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("집합에서 자기 자신을 뺀 차집합", "집합의 모든 원소를 제거하면 공집합이 됩니다: A \\ A = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hiệu của một tập với chính nó", "Loại bỏ mọi phần tử của một tập để lại tập rỗng: A \\ A = ∅")
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

impl SetMinusEmptyRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Removing the empty set", "Removing no elements leaves the original set: A \\ ∅ = A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("减去空集", "去掉空集中的元素不会改变原集合，即 A \\ ∅ = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("減去空集", "去掉空集中的元素不會改變原集合，即 A \\ ∅ = A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Retrait de l’ensemble vide", "Ne retirer aucun élément laisse l’ensemble initial: A \\ ∅ = A")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Вычитание пустого множества", "Удаление элементов пустого множества не меняет исходное множество: A \\ ∅ = A")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Eliminación del conjunto vacío", "No eliminar ningún elemento deja el conjunto original: A \\ ∅ = A")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("طرح المجموعة الخالية", "عدم إزالة أي عنصر يبقي المجموعة الأصلية: A \\ ∅ = A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合との差集合", "空集合の要素を除いても元の集合は変わりません：A \\ ∅ = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합을 뺀 차집합", "공집합의 원소를 제거해도 원래 집합은 같습니다: A \\ ∅ = A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Trừ tập rỗng", "Không loại bỏ phần tử nào giữ nguyên tập ban đầu: A \\ ∅ = A")
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

impl SetMinusEmptyLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Removing a set from the empty set", "Removing elements from an empty set still leaves it empty: ∅ \\ A = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("从空集减去集合", "从空集中去掉元素，结果仍是空集，即 ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("從空集減去集合", "從空集中去掉元素，結果仍是空集，即 ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Retrait d’un ensemble de l’ensemble vide", "Retirer des éléments de l’ensemble vide le laisse vide: ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Вычитание множества из пустого", "Удаление элементов из пустого множества оставляет его пустым: ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Eliminación de un conjunto del conjunto vacío", "Eliminar elementos del conjunto vacío lo deja vacío: ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("طرح مجموعة من المجموعة الخالية", "إزالة عناصر من المجموعة الخالية تبقيها خالية: ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合からの差集合", "空集合から要素を除いても空集合のままです：∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합에서 집합을 뺀 차집합", "공집합에서 원소를 제거해도 공집합입니다: ∅ \\ A = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Trừ một tập khỏi tập rỗng", "Loại bỏ phần tử khỏi tập rỗng vẫn để lại tập rỗng: ∅ \\ A = ∅")
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

impl UnionCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Commutativity of union", "Swapping the two arguments of union leaves the result unchanged: A ∪ B = B ∪ A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("并集的交换律", "交换并集的两个参数，结果不变，即 A ∪ B = B ∪ A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("聯集的交換律", "交換聯集的兩個引數，結果不變，即 A ∪ B = B ∪ A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : union",
            "Permuter les arguments de l’opération « union » ne change pas le résultat: A ∪ B = B ∪ A",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: объединение",
            "Перестановка аргументов операции «объединение» не меняет результат: A ∪ B = B ∪ A",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: unión",
            "Intercambiar los argumentos de la operación «unión» no cambia el resultado: A ∪ B = B ∪ A",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: الاتحاد", "تبديل وسيطي عملية «الاتحاد» لا يغيّر النتيجة: A ∪ B = B ∪ A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("和集合の交換法則", "和集合の二つの引数を交換しても結果は変わりません：A ∪ B = B ∪ A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("합집합의 교환법칙", "합집합의 두 인수를 바꾸어도 결과는 같습니다: A ∪ B = B ∪ A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính giao hoán của hợp", "Đổi chỗ hai đối số của phép hợp không làm thay đổi kết quả: A ∪ B = B ∪ A")
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

impl IntersectCommutativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Commutativity of intersection",
            "Swapping the two arguments of intersection leaves the result unchanged: A ∩ B = B ∩ A",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("交集的交换律", "交换交集的两个参数，结果不变，即 A ∩ B = B ∩ A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("交集的交換律", "交換交集的兩個引數，結果不變，即 A ∩ B = B ∩ A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Commutativité : intersection",
            "Permuter les arguments de l’opération « intersection » ne change pas le résultat: A ∩ B = B ∩ A",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Коммутативность: пересечение",
            "Перестановка аргументов операции «пересечение» не меняет результат: A ∩ B = B ∩ A",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conmutatividad: intersección",
            "Intercambiar los argumentos de la operación «intersección» no cambia el resultado: A ∩ B = B ∩ A",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية الإبدال: التقاطع", "تبديل وسيطي عملية «التقاطع» لا يغيّر النتيجة: A ∩ B = B ∩ A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("共通部分の交換法則", "共通部分の二つの引数を交換しても結果は変わりません：A ∩ B = B ∩ A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("교집합의 교환법칙", "교집합의 두 인수를 바꾸어도 결과는 같습니다: A ∩ B = B ∩ A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính giao hoán của giao",
            "Đổi chỗ hai đối số của phép giao không làm thay đổi kết quả: A ∩ B = B ∩ A",
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

impl UnionIdempotentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Idempotence of union", "Applying union to two identical arguments returns that argument: A ∪ A = A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("并集的幂等性", "并集的两个参数相同时，结果就是该参数，即 A ∪ A = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("聯集的冪等性", "聯集的兩個引數相同時，結果就是該引數，即 A ∪ A = A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Idempotence : union", "L’opération « union » appliquée à deux arguments identiques restitue cet argument: A ∪ A = A")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Идемпотентность: объединение", "Операция «объединение» с одинаковыми аргументами возвращает этот аргумент: A ∪ A = A")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Idempotencia: unión", "La operación «unión» con dos argumentos iguales devuelve ese argumento: A ∪ A = A")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية التكرار: الاتحاد", "تطبيق عملية «الاتحاد» على وسيطين متساويين يعيد الوسيط نفسه: A ∪ A = A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("和集合の冪等性", "和集合に同じ引数を二つ与えると、その引数が得られます：A ∪ A = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("합집합의 멱등성", "합집합의 두 인수가 같으면 그 인수가 결과입니다: A ∪ A = A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính lũy đẳng của hợp", "Phép hợp với hai đối số giống nhau trả về chính đối số đó: A ∪ A = A")
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

impl IntersectIdempotentBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Idempotence of intersection", "Applying intersection to two identical arguments returns that argument: A ∩ A = A")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("交集的幂等性", "交集的两个参数相同时，结果就是该参数，即 A ∩ A = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("交集的冪等性", "交集的兩個引數相同時，結果就是該引數，即 A ∩ A = A")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Idempotence : intersection", "L’opération « intersection » appliquée à deux arguments identiques restitue cet argument: A ∩ A = A")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Идемпотентность: пересечение", "Операция «пересечение» с одинаковыми аргументами возвращает этот аргумент: A ∩ A = A")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Idempotencia: intersección", "La operación «intersección» con dos argumentos iguales devuelve ese argumento: A ∩ A = A")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("خاصية التكرار: التقاطع", "تطبيق عملية «التقاطع» على وسيطين متساويين يعيد الوسيط نفسه: A ∩ A = A")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("共通部分の冪等性", "共通部分に同じ引数を二つ与えると、その引数が得られます：A ∩ A = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("교집합의 멱등성", "교집합의 두 인수가 같으면 그 인수가 결과입니다: A ∩ A = A")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tính lũy đẳng của giao", "Phép giao với hai đối số giống nhau trả về chính đối số đó: A ∩ A = A")
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

impl IntersectFromSubsetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersection with a containing set",
            "The Intersection with a containing set law gives: A ⊆ B ⇒ A ∩ B = A",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("子集与包含它的集合相交", "子集与包含它的集合相交可写为：A ⊆ B ⇒ A ∩ B = A")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "子集與包含它的集合相交",
            "子集與包含它的集合相交可寫為：A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intersection avec un ensemble contenant",
            "La propriété « Intersection avec un ensemble contenant » donne: A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пересечение с содержащим множеством",
            "Свойство «Пересечение с содержащим множеством» выражается равенством: A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intersección con un conjunto que contiene al otro",
            "La propiedad «Intersección con un conjunto que contiene al otro» se expresa como: A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التقاطع مع مجموعة حاوية",
            "تُكتب خاصية «التقاطع مع مجموعة حاوية» كما يلي: A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("包含する集合との共通部分", "包含する集合との共通部分は次の式で表されます：A ⊆ B ⇒ A ∩ B = A")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "포함하는 집합과의 교집합",
            "포함하는 집합과의 교집합은 다음 식으로 나타납니다: A ⊆ B ⇒ A ∩ B = A",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giao với tập chứa nó",
            "Tính chất «Giao với tập chứa nó» được biểu diễn bởi: A ⊆ B ⇒ A ∩ B = A",
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

impl EmptySetFromNotNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "A set that is not nonempty is empty",
            "If a set is not nonempty, it has no elements and equals the empty set: ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非非空集合就是空集",
            "集合不满足非空性质时，没有任何元素，因而等于空集，即 ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非非空集合就是空集",
            "集合不滿足非空性質時，沒有任何元素，因而等於空集，即 ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Un ensemble non non vide est vide",
            "Si un ensemble n’est pas non vide, il n’a aucun élément et est l’ensemble vide: ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Множество, не являющееся непустым, пусто",
            "Если множество не является непустым, оно не содержит элементов и равно пустому множеству: ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Un conjunto que no es no vacío es vacío",
            "Si un conjunto no es no vacío, no tiene elementos y es el conjunto vacío: ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "المجموعة التي ليست غير خالية تكون خالية",
            "إذا لم تكن المجموعة غير خالية فلا عناصر فيها وتساوي المجموعة الخالية: ¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非空でない集合は空集合",
            "集合が非空でなければ要素はなく、空集合に等しくなります：¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비어 있지 않다는 성질이 부정된 집합은 공집합",
            "집합이 비어 있지 않은 것이 아니면 원소가 없으므로 공집합입니다：¬$is_nonempty_set(A) ⇒ A = ∅",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập không có tính chất khác rỗng là tập rỗng",
            "Nếu một tập không khác rỗng thì nó không có phần tử và bằng tập rỗng: ¬$is_nonempty_set(A) ⇒ A = ∅",
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

impl PowerSetFiniteSetSizeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cardinality of a finite power set",
            "The Cardinality of a finite power set law gives: |pow(A)| = 2^|A|",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合幂集的基数",
            "有限集合幂集的基数可写为：|pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合冪集的基數",
            "有限集合冪集的基數可寫為：|pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal des parties d’un ensemble fini",
            "La propriété « Cardinal des parties d’un ensemble fini » donne: |pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Мощность булеана конечного множества",
            "Свойство «Мощность булеана конечного множества» выражается равенством: |pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad de un conjunto potencia finito",
            "La propiedad «Cardinalidad de un conjunto potencia finito» se expresa como: |pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد عناصر مجموعة أجزاء مجموعة منتهية",
            "تُكتب خاصية «عدد عناصر مجموعة أجزاء مجموعة منتهية» كما يلي: |pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の冪集合の要素数",
            "有限集合の冪集合の要素数は次の式で表されます：|pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한집합 멱집합의 원소 수",
            "유한집합 멱집합의 원소 수은 다음 식으로 나타납니다: |pow(A)| = 2^|A|",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng của tập lũy thừa của tập hữu hạn",
            "Tính chất «Lực lượng của tập lũy thừa của tập hữu hạn» được biểu diễn bởi: |pow(A)| = 2^|A|",
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

impl UnionAssociativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Associativity of union",
            "Regrouping three operands of union leaves the result unchanged: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("并集的结合律", "改变并集三个操作数的分组方式，结果不变，即 (A ∪ B) ∪ C = A ∪ (B ∪ C)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "聯集的結合律",
            "改變聯集三個運算元的分組方式，結果不變，即 (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Associativité : union",
            "Regrouper autrement trois opérandes de l’opération « union » ne change pas le résultat: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ассоциативность: объединение",
            "Изменение группировки трёх операндов операции «объединение» не меняет результат: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Asociatividad: unión",
            "Cambiar la agrupación de tres operandos de la operación «unión» no cambia el resultado: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "خاصية التجميع: الاتحاد",
            "تغيير تجميع ثلاثة معاملات لعملية «الاتحاد» لا يغيّر النتيجة: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和集合の結合法則",
            "和集合の三つの項の括り方を変えても結果は変わりません：(A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합집합의 결합법칙",
            "합집합의 세 피연산자를 묶는 방식을 바꾸어도 결과는 같습니다: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính kết hợp của hợp",
            "Thay đổi cách nhóm ba toán hạng của phép hợp không làm thay đổi kết quả: (A ∪ B) ∪ C = A ∪ (B ∪ C)",
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

impl IntersectAssociativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Associativity of intersection",
            "Regrouping three operands of intersection leaves the result unchanged: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "交集的结合律",
            "改变交集三个操作数的分组方式，结果不变，即 (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集的結合律",
            "改變交集三個運算元的分組方式，結果不變，即 (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Associativité : intersection",
            "Regrouper autrement trois opérandes de l’opération « intersection » ne change pas le résultat: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ассоциативность: пересечение",
            "Изменение группировки трёх операндов операции «пересечение» не меняет результат: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Asociatividad: intersección",
            "Cambiar la agrupación de tres operandos de la operación «intersección» no cambia el resultado: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "خاصية التجميع: التقاطع",
            "تغيير تجميع ثلاثة معاملات لعملية «التقاطع» لا يغيّر النتيجة: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "共通部分の結合法則",
            "共通部分の三つの項の括り方を変えても結果は変わりません：(A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "교집합의 결합법칙",
            "교집합의 세 피연산자를 묶는 방식을 바꾸어도 결과는 같습니다: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính kết hợp của giao",
            "Thay đổi cách nhóm ba toán hạng của phép giao không làm thay đổi kết quả: (A ∩ B) ∩ C = A ∩ (B ∩ C)",
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

impl IntersectUnionDistributiveBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersection distributes over union",
            "The Intersection distributes over union law gives: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "交集对并集的分配律",
            "交集对并集的分配律可写为：A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集對聯集的分配律",
            "交集對聯集的分配律可寫為：A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Distributivité de l’intersection sur l’union",
            "La propriété « Distributivité de l’intersection sur l’union » donne: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Дистрибутивность пересечения относительно объединения",
            "Свойство «Дистрибутивность пересечения относительно объединения» выражается равенством: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Distributividad de la intersección sobre la unión",
            "La propiedad «Distributividad de la intersección sobre la unión» se expresa como: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توزيع التقاطع على الاتحاد",
            "تُكتب خاصية «توزيع التقاطع على الاتحاد» كما يلي: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和集合に対する共通部分の分配法則",
            "和集合に対する共通部分の分配法則は次の式で表されます：A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합집합에 대한 교집합의 분배법칙",
            "합집합에 대한 교집합의 분배법칙은 다음 식으로 나타납니다: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phân phối của giao đối với hợp",
            "Tính chất «Tính phân phối của giao đối với hợp» được biểu diễn bởi: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
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

impl SetMinusUnionDeMorganBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "De Morgan’s law for difference with a union",
            "The De Morgan’s law for difference with a union law gives: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "对并集求差的德摩根律",
            "对并集求差的德摩根律可写为：A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "對聯集求差的德摩根律",
            "對聯集求差的德摩根律可寫為：A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi de De Morgan pour la différence avec une union",
            "La propriété « Loi de De Morgan pour la différence avec une union » donne: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Закон де Моргана для разности с объединением",
            "Свойство «Закон де Моргана для разности с объединением» выражается равенством: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley de De Morgan para diferencia con una unión",
            "La propiedad «Ley de De Morgan para diferencia con una unión» se expresa como: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون دي مورغان للفرق مع اتحاد",
            "تُكتب خاصية «قانون دي مورغان للفرق مع اتحاد» كما يلي: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和集合との差集合のド・モルガンの法則",
            "和集合との差集合のド・モルガンの法則は次の式で表されます：A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합집합과의 차집합에 대한 드 모르간 법칙",
            "합집합과의 차집합에 대한 드 모르간 법칙은 다음 식으로 나타납니다: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Định luật De Morgan cho hiệu với hợp",
            "Tính chất «Định luật De Morgan cho hiệu với hợp» được biểu diễn bởi: A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
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

impl SetMinusIntersectDeMorganBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "De Morgan’s law for difference with an intersection",
            "The De Morgan’s law for difference with an intersection law gives: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "对交集求差的德摩根律",
            "对交集求差的德摩根律可写为：A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "對交集求差的德摩根律",
            "對交集求差的德摩根律可寫為：A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Loi de De Morgan pour la différence avec une intersection",
            "La propriété « Loi de De Morgan pour la différence avec une intersection » donne: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Закон де Моргана для разности с пересечением",
            "Свойство «Закон де Моргана для разности с пересечением» выражается равенством: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Ley de De Morgan para diferencia con una intersección",
            "La propiedad «Ley de De Morgan para diferencia con una intersección» se expresa como: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قانون دي مورغان للفرق مع تقاطع",
            "تُكتب خاصية «قانون دي مورغان للفرق مع تقاطع» كما يلي: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "共通部分との差集合のド・モルガンの法則",
            "共通部分との差集合のド・モルガンの法則は次の式で表されます：A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "교집합과의 차집합에 대한 드 모르간 법칙",
            "교집합과의 차집합에 대한 드 모르간 법칙은 다음 식으로 나타납니다: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Định luật De Morgan cho hiệu với giao",
            "Tính chất «Định luật De Morgan cho hiệu với giao» được biểu diễn bởi: A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
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

impl IntersectSetMinusSelfEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersection with a difference excluding the same set",
            "No element belongs both to A and to B with A removed: A ∩ (B \\ A) = ∅",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "与排除自身的差集相交",
            "A 与 B 中去掉 A 后剩余的集合没有共同元素，即 A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "與排除自身的差集相交",
            "A 與 B 中去掉 A 後剩餘的集合沒有共同元素，即 A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intersection avec une différence excluant le même ensemble",
            "Aucun élément n’appartient à la fois à A et à B privé de A: A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пересечение с разностью, исключающей это же множество",
            "Ни один элемент не принадлежит одновременно A и B после удаления A: A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intersección con una diferencia que excluye el mismo conjunto",
            "Ningún elemento pertenece a la vez a A y a B tras eliminar A: A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التقاطع مع فرق يستبعد المجموعة نفسها",
            "لا يوجد عنصر ينتمي إلى A وإلى B بعد إزالة A منها معًا: A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "自身を除いた差集合との共通部分",
            "A と、B から A を除いた集合には共通の要素がありません：A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "자기 집합을 제외한 차집합과의 교집합",
            "A와 B에서 A를 제외한 집합에는 공통 원소가 없습니다: A ∩ (B \\ A) = ∅",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giao với hiệu loại bỏ chính tập đó",
            "Không có phần tử nào vừa thuộc A vừa thuộc B sau khi loại A: A ∩ (B \\ A) = ∅",
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

impl FiniteSetSumEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Sum over the empty set", "A sum with no terms equals zero: ∑_{x∈∅} f(x) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空集上的求和", "没有求和项时，和等于零，即 ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空集上的求和", "沒有求和項時，和等於零，即 ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Somme sur l’ensemble vide", "Une somme sans termes vaut zéro: ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Сумма по пустому множеству", "Сумма без слагаемых равна нулю: ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Suma sobre el conjunto vacío", "Una suma sin términos vale cero: ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المجموع على المجموعة الخالية", "المجموع دون حدود يساوي صفرًا: ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合上の総和", "項のない和は零です：∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합에 대한 합", "항이 없는 합은 영입니다: ∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tổng trên tập rỗng", "Tổng không có số hạng bằng không: ∑_{x∈∅} f(x) = 0")
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

impl FiniteSetProductEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Product over the empty set",
            "A product with no factors equals one: ∏_{x∈∅} f(x) = 1",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空集上的连乘", "没有乘法因子时，积等于一，即 ∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空集上的連乘", "沒有乘法因子時，積等於一，即 ∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Produit sur l’ensemble vide", "Un produit sans facteurs vaut un: ∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Произведение по пустому множеству",
            "Произведение без множителей равно единице: ∏_{x∈∅} f(x) = 1",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto sobre el conjunto vacío",
            "Un producto sin factores vale uno: ∏_{x∈∅} f(x) = 1",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل الضرب على المجموعة الخالية",
            "حاصل الضرب دون عوامل يساوي واحدًا: ∏_{x∈∅} f(x) = 1",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合上の総積", "因子のない積は一です：∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합에 대한 곱", "인수가 없는 곱은 일입니다: ∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tích trên tập rỗng", "Tích không có thừa số bằng một: ∏_{x∈∅} f(x) = 1")
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

impl FiniteSetReduceEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "reduce over ∅",
            "reduce over the empty set is the unit",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空集上归约", "空集上的归约是单位元")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "空集合折疊",
            "空集合上的折疊為單位元",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Pli sur ∅",
            "Le pli sur l'ensemble vide est l'unité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Свёртка по ∅",
            "Свёртка по пустому множеству равна единице",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pliegue sobre ∅",
            "El pliegue sobre conjunto vacío es la unidad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طي على ∅",
            "الطي على المجموعة الخالية هو الوحدة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "∅ 上の畳み込み",
            "空集合上の畳み込みは単位元です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "∅ 위의 접기",
            "공집합 위의 접기는 단위원입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Gấp trên ∅",
            "Gấp trên tập rỗng là đơn vị",
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

impl ReduceEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "reduce empty",
            "reduce on an empty range is the unit",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空归约", "空范围上的归约是单位元")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空折疊", "空區間上的折疊為單位元")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Pli vide",
            "Le pli sur un intervalle vide est l'unité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пустая свёртка",
            "Свёртка по пустому интервалу равна единице",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pliegue vacío",
            "El pliegue sobre intervalo vacío es la unidad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("طي خالٍ", "الطي على فترة خالية هو الوحدة")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の畳み込み",
            "空区間上の畳み込みは単位元です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("빈 접기", "빈 구간 위의 접기는 단위원입니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Gấp rỗng", "Gấp trên khoảng rỗng là đơn vị")
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

impl SumEmptyRangeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "sum empty range",
            "∑ over an empty range is 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空范围求和", "空范围求和为 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空區間和", "空區間上的 ∑ 為 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme sur intervalle vide",
            "∑ sur un intervalle vide vaut 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сумма по пустому интервалу",
            "∑ по пустому интервалу равно 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma de intervalo vacío",
            "∑ sobre intervalo vacío es 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع فترة خالية",
            "∑ على فترة خالية يساوي 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空区間の和", "空区間上の ∑ は 0 です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("빈 구간의 합", "빈 구간 위의 ∑는 0입니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tổng khoảng rỗng",
            "∑ trên khoảng rỗng bằng 0",
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

impl ProductEmptyRangeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "product empty range",
            "∏ over an empty range is 1",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空范围求积", "空范围求积为 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空區間乘積", "空區間上的 ∏ 為 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit sur intervalle vide",
            "∏ sur un intervalle vide vaut 1",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Произведение по пустому интервалу",
            "∏ по пустому интервалу равно 1",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto de intervalo vacío",
            "∏ sobre intervalo vacío es 1",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل ضرب فترة خالية",
            "∏ على فترة خالية يساوي 1",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空区間の積", "空区間上の ∏ は 1 です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 구간의 곱",
            "빈 구간 위의 ∏는 1입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích khoảng rỗng",
            "∏ trên khoảng rỗng bằng 1",
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

impl UnionAbsorptionFromSubsetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union with a containing set",
            "The Union with a containing set law gives: A ⊆ B ⇒ A ∪ B = B",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("子集与包含它的集合求并", "子集与包含它的集合求并可写为：A ⊆ B ⇒ A ∪ B = B")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "子集與包含它的集合求聯集",
            "子集與包含它的集合求聯集可寫為：A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Union avec un ensemble contenant",
            "La propriété « Union avec un ensemble contenant » donne: A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Объединение с содержащим множеством",
            "Свойство «Объединение с содержащим множеством» выражается равенством: A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Unión con un conjunto que contiene al otro",
            "La propiedad «Unión con un conjunto que contiene al otro» se expresa como: A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الاتحاد مع مجموعة حاوية",
            "تُكتب خاصية «الاتحاد مع مجموعة حاوية» كما يلي: A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "包含する集合との和集合",
            "包含する集合との和集合は次の式で表されます：A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "포함하는 집합과의 합집합",
            "포함하는 집합과의 합집합은 다음 식으로 나타납니다: A ⊆ B ⇒ A ∪ B = B",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp với tập chứa nó",
            "Tính chất «Hợp với tập chứa nó» được biểu diễn bởi: A ⊆ B ⇒ A ∪ B = B",
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

impl SetMinusRecoversSubsetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Removing a complement recovers the subset",
            "The Removing a complement recovers the subset law gives: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "减去相对补集还原子集",
            "减去相对补集还原子集可写为：A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "減去相對補集還原子集",
            "減去相對補集還原子集可寫為：A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Retrait du complément et récupération du sous-ensemble",
            "La propriété « Retrait du complément et récupération du sous-ensemble » donne: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вычитание дополнения восстанавливает подмножество",
            "Свойство «Вычитание дополнения восстанавливает подмножество» выражается равенством: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Eliminar el complemento recupera el subconjunto",
            "La propiedad «Eliminar el complemento recupera el subconjunto» se expresa como: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طرح المتممة يستعيد المجموعة الجزئية",
            "تُكتب خاصية «طرح المتممة يستعيد المجموعة الجزئية» كما يلي: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "補集合の除去による部分集合の復元",
            "補集合の除去による部分集合の復元は次の式で表されます：A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "여집합 제거로 부분집합 복원",
            "여집합 제거로 부분집합 복원은 다음 식으로 나타납니다: A ⊆ B ⇒ B \\ (B \\ A) = A",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Trừ phần bù để khôi phục tập con",
            "Tính chất «Trừ phần bù để khôi phục tập con» được biểu diễn bởi: A ⊆ B ⇒ B \\ (B \\ A) = A",
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

impl EmptySetFromSizeZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Zero cardinality implies an empty finite set",
            "The Zero cardinality implies an empty finite set law gives: |S| = 0 ⇒ S = ∅",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合基数为零则为空集",
            "有限集合基数为零则为空集可写为：|S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("有限集合基數為零則為空集", "有限集合基數為零則為空集可寫為：|S| = 0 ⇒ S = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal nul et ensemble fini vide",
            "La propriété « Cardinal nul et ensemble fini vide » donne: |S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нулевая мощность означает пустое конечное множество",
            "Свойство «Нулевая мощность означает пустое конечное множество» выражается равенством: |S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad cero implica conjunto finito vacío",
            "La propiedad «Cardinalidad cero implica conjunto finito vacío» se expresa como: |S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد العناصر الصفري يعني مجموعة منتهية خالية",
            "تُكتب خاصية «عدد العناصر الصفري يعني مجموعة منتهية خالية» كما يلي: |S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "要素数が零の有限集合は空集合",
            "要素数が零の有限集合は空集合は次の式で表されます：|S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "원소 수가 영인 유한집합은 공집합",
            "원소 수가 영인 유한집합은 공집합은 다음 식으로 나타납니다: |S| = 0 ⇒ S = ∅",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng bằng không suy ra tập hữu hạn rỗng",
            "Tính chất «Lực lượng bằng không suy ra tập hữu hạn rỗng» được biểu diễn bởi: |S| = 0 ⇒ S = ∅",
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


impl FiniteSetSizeSetMinusBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cardinality of a finite set difference",
            "The Cardinality of a finite set difference law gives: |A \\ B| = |A| − |A ∩ B|",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合差集的基数",
            "有限集合差集的基数可写为：|A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合差集的基數",
            "有限集合差集的基數可寫為：|A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal d’une différence d’ensembles finis",
            "La propriété « Cardinal d’une différence d’ensembles finis » donne: |A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Мощность разности конечных множеств",
            "Свойство «Мощность разности конечных множеств» выражается равенством: |A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad de una diferencia de conjuntos finitos",
            "La propiedad «Cardinalidad de una diferencia de conjuntos finitos» se expresa como: |A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد عناصر فرق مجموعتين منتهيتين",
            "تُكتب خاصية «عدد عناصر فرق مجموعتين منتهيتين» كما يلي: |A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の差集合の要素数",
            "有限集合の差集合の要素数は次の式で表されます：|A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한집합 차집합의 원소 수",
            "유한집합 차집합의 원소 수은 다음 식으로 나타납니다: |A \\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng của hiệu các tập hữu hạn",
            "Tính chất «Lực lượng của hiệu các tập hữu hạn» được biểu diễn bởi: |A \\ B| = |A| − |A ∩ B|",
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

impl FiniteSetSizeUnionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Inclusion–exclusion for two finite sets",
            "The Inclusion–exclusion for two finite sets law gives: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "两个有限集合的容斥公式",
            "两个有限集合的容斥公式可写为：|A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "兩個有限集合的容斥公式",
            "兩個有限集合的容斥公式可寫為：|A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion–exclusion pour deux ensembles finis",
            "La propriété « Inclusion–exclusion pour deux ensembles finis » donne: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включения–исключения для двух конечных множеств",
            "Свойство «Включения–исключения для двух конечных множеств» выражается равенством: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión–exclusión para dos conjuntos finitos",
            "La propiedad «Inclusión–exclusión para dos conjuntos finitos» se expresa como: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مبدأ الاحتواء والاستبعاد لمجموعتين منتهيتين",
            "تُكتب خاصية «مبدأ الاحتواء والاستبعاد لمجموعتين منتهيتين» كما يلي: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "二つの有限集合の包除原理",
            "二つの有限集合の包除原理は次の式で表されます：|A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "두 유한집합의 포함배제 원리",
            "두 유한집합의 포함배제 원리은 다음 식으로 나타납니다: |A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Nguyên lý bao hàm–loại trừ cho hai tập hữu hạn",
            "Tính chất «Nguyên lý bao hàm–loại trừ cho hai tập hữu hạn» được biểu diễn bởi: |A ∪ B| = |A| + |B| − |A ∩ B|",
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

impl ClosedRangeSingletonListSetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closed integer range with equal endpoints",
            "The Closed integer range with equal endpoints law gives: {n..n} = {n}",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("端点相同的整数闭区间", "端点相同的整数闭区间可写为：{n..n} = {n}")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "端點相同的整數閉區間",
            "端點相同的整數閉區間可寫為：{n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intervalle entier fermé à extrémités égales",
            "La propriété « Intervalle entier fermé à extrémités égales » donne: {n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутый целочисленный диапазон с равными концами",
            "Свойство «Замкнутый целочисленный диапазон с равными концами» выражается равенством: {n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intervalo entero cerrado con extremos iguales",
            "La propiedad «Intervalo entero cerrado con extremos iguales» se expresa como: {n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجال صحيح مغلق ذو طرفين متساويين",
            "تُكتب خاصية «مجال صحيح مغلق ذو طرفين متساويين» كما يلي: {n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "両端が等しい整数の閉区間",
            "両端が等しい整数の閉区間は次の式で表されます：{n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양 끝점이 같은 정수 닫힌 구간",
            "양 끝점이 같은 정수 닫힌 구간은 다음 식으로 나타납니다: {n..n} = {n}",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khoảng nguyên đóng có hai đầu mút bằng nhau",
            "Tính chất «Khoảng nguyên đóng có hai đầu mút bằng nhau» được biểu diễn bởi: {n..n} = {n}",
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

impl SumSingleTermBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "sum one term",
            "∑ with a single term equals that term",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("单项目求和", "单项求和等于该项")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單項和", "單項 ∑ 等於該項")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme à terme unique",
            "∑ à terme unique vaut ce terme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сумма одного члена",
            "∑ одного члена равно этому члену",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma de un término",
            "∑ de un término equivale a ese término",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع حد واحد",
            "∑ بحد واحد يساوي ذلك الحد",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一項の和", "一項の ∑ はその項に等しいです")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한 항의 합",
            "한 항의 ∑는 그 항과 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tổng một hạng", "∑ một hạng bằng hạng đó")
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

impl ProductSingleTermBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "product one term",
            "∏ with a single term equals that term",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("单项目求积", "单项求积等于该项")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單項乘積", "單項 ∏ 等於該項")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit à terme unique",
            "∏ à terme unique vaut ce terme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Произведение одного члена",
            "∏ одного члена равно этому члену",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto de un término",
            "∏ de un término equivale a ese término",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل ضرب حد واحد",
            "∏ بحد واحد يساوي ذلك الحد",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "一項の積",
            "一項の ∏ はその項に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한 항의 곱",
            "한 항의 ∏는 그 항과 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích một hạng",
            "∏ một hạng bằng hạng đó",
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

impl ReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Left fold with addition and zero equals summation",
            "reduce with add and 0 equals a sum",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "归约 +0 即求和",
            "以加法与 0 归约等于求和",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "+0 折疊視為和",
            "加法以 0 為初值的折疊等於和",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Pli +0 comme somme",
            "Le pli avec addition et 0 est égal à une somme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Свёртка +0 как сумма",
            "Свёртка со сложением и 0 равна сумме",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pliegue +0 como suma",
            "El pliegue con suma y 0 equivale a una suma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طي +0 كمجموع",
            "الطي بالجمع و0 يساوي مجموعًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和としての +0 畳み込み",
            "加算と 0 による畳み込みは和に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합으로서의 +0 접기",
            "덧셈과 0으로 접으면 합과 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Gấp +0 là tổng",
            "Gấp với phép cộng và 0 bằng tổng",
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

impl FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "finite-set reduce as sum",
            "finite-set reduce with + and 0 equals a sum",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集归约即求和",
            "有限集上以 + 与 0 归约等于求和",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合折疊視為和",
            "以 + 和 0 折疊有限集合等於和",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Pli sur ensemble fini comme somme",
            "Un pli sur ensemble fini avec + et 0 est égal à une somme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Свёртка конечного множества как сумма",
            "Свёртка конечного множества с + и 0 равна сумме",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pliegue de conjunto finito como suma",
            "Un pliegue de conjunto finito con + y 0 equivale a una suma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طي مجموعة منتهية كمجموع",
            "طي مجموعة منتهية مع + و0 يساوي مجموعًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和としての有限集合の畳み込み",
            "有限集合を + と 0 で畳み込むと和に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합으로서의 유한 집합 접기",
            "유한 집합을 +와 0으로 접으면 합과 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Gấp tập hữu hạn là tổng",
            "Gấp tập hữu hạn với + và 0 bằng tổng",
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

impl PowOfLogInverseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Cancellation of same-base power and logarithm", "The Cancellation of same-base power and logarithm law gives: a^(log_a(b)) = b")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("同底幂与对数的消去", "同底幂与对数的消去可写为：a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("同底冪與對數的消去", "同底冪與對數的消去可寫為：a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Annulation d’une puissance et d’un logarithme de même base", "La propriété « Annulation d’une puissance et d’un logarithme de même base » donne: a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Сокращение степени и логарифма с тем же основанием", "Свойство «Сокращение степени и логарифма с тем же основанием» выражается равенством: a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Cancelación de la potencia y el logaritmo de la misma base", "La propiedad «Cancelación de la potencia y el logaritmo de la misma base» se expresa como: a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("اختزال القوة واللوغاريتم ذوي الأساس نفسه", "تُكتب خاصية «اختزال القوة واللوغاريتم ذوي الأساس نفسه» كما يلي: a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("同じ底の累乗と対数の相殺", "同じ底の累乗と対数の相殺は次の式で表されます：a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("밑이 같은 거듭제곱과 로그의 소거", "밑이 같은 거듭제곱과 로그의 소거은 다음 식으로 나타납니다: a^(log_a(b)) = b")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Khử lũy thừa và logarit cùng cơ số", "Tính chất «Khử lũy thừa và logarit cùng cơ số» được biểu diễn bởi: a^(log_a(b)) = b")
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

impl UnionSetMinusDecompositionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union decomposition by set difference",
            "The Union decomposition by set difference law gives: A ∪ B = A ∪ (B \\ A)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "并集的差集分解",
            "并集的差集分解可写为：A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "聯集的差集分解",
            "聯集的差集分解可寫為：A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Décomposition d’une union par différence",
            "La propriété « Décomposition d’une union par différence » donne: A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Разложение объединения через разность",
            "Свойство «Разложение объединения через разность» выражается равенством: A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Descomposición de la unión mediante diferencia",
            "La propiedad «Descomposición de la unión mediante diferencia» se expresa como: A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تحليل الاتحاد باستخدام فرق المجموعات",
            "تُكتب خاصية «تحليل الاتحاد باستخدام فرق المجموعات» كما يلي: A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "差集合による和集合の分解",
            "差集合による和集合の分解は次の式で表されます：A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "차집합을 이용한 합집합 분해",
            "차집합을 이용한 합집합 분해은 다음 식으로 나타납니다: A ∪ B = A ∪ (B \\ A)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phân tích hợp bằng hiệu tập hợp",
            "Tính chất «Phân tích hợp bằng hiệu tập hợp» được biểu diễn bởi: A ∪ B = A ∪ (B \\ A)",
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

impl SetMinusIntersectSelfBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Removing the intersection with another set",
            "The Removing the intersection with another set law gives: A \\ (A ∩ B) = A \\ B",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "减去与另一集合的交集",
            "减去与另一集合的交集可写为：A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "減去與另一集合的交集",
            "減去與另一集合的交集可寫為：A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Retrait de l’intersection avec un autre ensemble",
            "La propriété « Retrait de l’intersection avec un autre ensemble » donne: A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вычитание пересечения с другим множеством",
            "Свойство «Вычитание пересечения с другим множеством» выражается равенством: A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Eliminación de la intersección con otro conjunto",
            "La propiedad «Eliminación de la intersección con otro conjunto» se expresa como: A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طرح التقاطع مع مجموعة أخرى",
            "تُكتب خاصية «طرح التقاطع مع مجموعة أخرى» كما يلي: A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "他の集合との共通部分の除去",
            "他の集合との共通部分の除去は次の式で表されます：A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "다른 집합과의 교집합 제거",
            "다른 집합과의 교집합 제거은 다음 식으로 나타납니다: A \\ (A ∩ B) = A \\ B",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Trừ phần giao với một tập khác",
            "Tính chất «Trừ phần giao với một tập khác» được biểu diễn bởi: A \\ (A ∩ B) = A \\ B",
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

impl ReOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Real part of i", "The Real part of i equals 0: re(i) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("i 的实部", "i 的实部等于 0，即 re(i) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("i 的實部", "i 的實部等於 0，即 re(i) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie réelle de i", "La valeur « Partie réelle » de i est 0: re(i) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Вещественная часть числа i", "Для i величина «Вещественная часть» равна 0: re(i) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte real de i", "El valor «Parte real» de i es 0: re(i) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء الحقيقي لـ i", "قيمة «الجزء الحقيقي» لـ i تساوي 0: re(i) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("i の実部", "i の実部は 0 です：re(i) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("i의 실수부", "i의 실수부는 0입니다: re(i) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần thực của i", "Giá trị «Phần thực» của i bằng 0: re(i) = 0")
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

impl ImgOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Imaginary part of i", "The Imaginary part of i equals 1: img(i) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("i 的虚部", "i 的虚部等于 1，即 img(i) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("i 的虛部", "i 的虛部等於 1，即 img(i) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie imaginaire de i", "La valeur « Partie imaginaire » de i est 1: img(i) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Мнимая часть числа i", "Для i величина «Мнимая часть» равна 1: img(i) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte imaginaria de i", "El valor «Parte imaginaria» de i es 1: img(i) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء التخيلي لـ i", "قيمة «الجزء التخيلي» لـ i تساوي 1: img(i) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("i の虚部", "i の虚部は 1 です：img(i) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("i의 허수부", "i의 허수부는 1입니다: img(i) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần ảo của i", "Giá trị «Phần ảo» của i bằng 1: img(i) = 1")
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

impl ReOfRealEmbeddingBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Real part of embed(x)", "The Real part of embed(x) equals x: re(embed(x)) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("embed(x) 的实部", "embed(x) 的实部等于 x，即 re(embed(x)) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("embed(x) 的實部", "embed(x) 的實部等於 x，即 re(embed(x)) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Partie réelle de embed(x)",
            "La valeur « Partie réelle » de embed(x) est x: re(embed(x)) = x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вещественная часть числа embed(x)",
            "Для embed(x) величина «Вещественная часть» равна x: re(embed(x)) = x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Parte real de embed(x)",
            "El valor «Parte real» de embed(x) es x: re(embed(x)) = x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الجزء الحقيقي لـ embed(x)",
            "قيمة «الجزء الحقيقي» لـ embed(x) تساوي x: re(embed(x)) = x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("embed(x) の実部", "embed(x) の実部は x です：re(embed(x)) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("embed(x)의 실수부", "embed(x)의 실수부는 x입니다: re(embed(x)) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phần thực của embed(x)",
            "Giá trị «Phần thực» của embed(x) bằng x: re(embed(x)) = x",
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

impl ImgOfRealEmbeddingBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Imaginary part of embed(x)", "The Imaginary part of embed(x) equals 0: img(embed(x)) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("embed(x) 的虚部", "embed(x) 的虚部等于 0，即 img(embed(x)) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("embed(x) 的虛部", "embed(x) 的虛部等於 0，即 img(embed(x)) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Partie imaginaire de embed(x)",
            "La valeur « Partie imaginaire » de embed(x) est 0: img(embed(x)) = 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Мнимая часть числа embed(x)",
            "Для embed(x) величина «Мнимая часть» равна 0: img(embed(x)) = 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Parte imaginaria de embed(x)",
            "El valor «Parte imaginaria» de embed(x) es 0: img(embed(x)) = 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الجزء التخيلي لـ embed(x)",
            "قيمة «الجزء التخيلي» لـ embed(x) تساوي 0: img(embed(x)) = 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("embed(x) の虚部", "embed(x) の虚部は 0 です：img(embed(x)) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("embed(x)의 허수부", "embed(x)의 허수부는 0입니다: img(embed(x)) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phần ảo của embed(x)",
            "Giá trị «Phần ảo» của embed(x) bằng 0: img(embed(x)) = 0",
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

impl ReOfRealPlusIBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Real part of x + i", "The Real part of x + i equals x: re(x + i) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("x + i 的实部", "x + i 的实部等于 x，即 re(x + i) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("x + i 的實部", "x + i 的實部等於 x，即 re(x + i) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie réelle de x + i", "La valeur « Partie réelle » de x + i est x: re(x + i) = x")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Вещественная часть числа x + i", "Для x + i величина «Вещественная часть» равна x: re(x + i) = x")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte real de x + i", "El valor «Parte real» de x + i es x: re(x + i) = x")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء الحقيقي لـ x + i", "قيمة «الجزء الحقيقي» لـ x + i تساوي x: re(x + i) = x")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("x + i の実部", "x + i の実部は x です：re(x + i) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("x + i의 실수부", "x + i의 실수부는 x입니다: re(x + i) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần thực của x + i", "Giá trị «Phần thực» của x + i bằng x: re(x + i) = x")
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

impl ImgOfRealPlusIBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Imaginary part of x + i", "The Imaginary part of x + i equals 1: img(x + i) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("x + i 的虚部", "x + i 的虚部等于 1，即 img(x + i) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("x + i 的虛部", "x + i 的虛部等於 1，即 img(x + i) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie imaginaire de x + i", "La valeur « Partie imaginaire » de x + i est 1: img(x + i) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Мнимая часть числа x + i", "Для x + i величина «Мнимая часть» равна 1: img(x + i) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte imaginaria de x + i", "El valor «Parte imaginaria» de x + i es 1: img(x + i) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء التخيلي لـ x + i", "قيمة «الجزء التخيلي» لـ x + i تساوي 1: img(x + i) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("x + i の虚部", "x + i の虚部は 1 です：img(x + i) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("x + i의 허수부", "x + i의 허수부는 1입니다: img(x + i) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần ảo của x + i", "Giá trị «Phần ảo» của x + i bằng 1: img(x + i) = 1")
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

impl ComplexAbsOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Complex modulus of i", "The Complex modulus of i equals 1: C_abs(i) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("i 的复数模", "i 的复数模等于 1，即 C_abs(i) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("i 的複數模", "i 的複數模等於 1，即 C_abs(i) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Module complexe de i", "La valeur « Module complexe » de i est 1: C_abs(i) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Модуль комплексного числа числа i", "Для i величина «Модуль комплексного числа» равна 1: C_abs(i) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Módulo complejo de i", "El valor «Módulo complejo» de i es 1: C_abs(i) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المقياس المركب لـ i", "قيمة «المقياس المركب» لـ i تساوي 1: C_abs(i) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("i の複素数の絶対値", "i の複素数の絶対値は 1 です：C_abs(i) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("i의 복소수의 절댓값", "i의 복소수 절댓값은 1입니다: C_abs(i) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Môđun phức của i", "Giá trị «Môđun phức» của i bằng 1: C_abs(i) = 1")
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

impl ModNestedDivisibleAbsorptionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Reduction to a divisor of the modulus",
            "The Reduction to a divisor of the modulus law gives: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "向模数的约数约化余数",
            "向模数的约数约化余数可写为：m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "向模數的約數約化餘數",
            "向模數的約數約化餘數可寫為：m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réduction à un diviseur du module",
            "La propriété « Réduction à un diviseur du module » donne: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сведение к делителю модуля",
            "Свойство «Сведение к делителю модуля» выражается равенством: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reducción a un divisor del módulo",
            "La propiedad «Reducción a un divisor del módulo» se expresa como: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الاختزال إلى قاسم الترديد",
            "تُكتب خاصية «الاختزال إلى قاسم الترديد» كما يلي: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "法の約数への剰余の縮約",
            "法の約数への剰余の縮約は次の式で表されます：m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "법의 약수로 나머지 축소",
            "법의 약수로 나머지 축소은 다음 식으로 나타납니다: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Rút gọn theo ước của môđun",
            "Tính chất «Rút gọn theo ước của môđun» được biểu diễn bởi: m mod d = 0 ⇒ (a mod m) mod d = a mod d",
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

impl SumSplitLastTermBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "sum split last",
            "Sum splits off its last term",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("求和拆末项", "求和可拆出最后一项")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("和拆出末項", "和拆出最後一項")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Séparation du dernier terme de la somme",
            "La somme sépare son dernier terme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Отделение последнего члена суммы",
            "Сумма отделяет последний член",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Separación del último término de suma",
            "La suma separa su último término",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فصل الحد الأخير للمجموع",
            "المجموع يفصل حده الأخير",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和の最後の項の分離",
            "和から最後の項を分離します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합의 마지막 항 분리",
            "합에서 마지막 항을 분리합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tổng tách hạng cuối",
            "Tổng tách hạng cuối",
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

impl ProductSplitLastTermBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "product split last",
            "Product splits off its last term",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("求积拆末项", "求积可拆出最后一项")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("乘積拆出末項", "乘積拆出最後一項")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Séparation du dernier terme du produit",
            "Le produit sépare son dernier terme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Отделение последнего множителя",
            "Произведение отделяет последний множитель",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Separación del último término del producto",
            "El producto separa su último término",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فصل الحد الأخير لحاصل الضرب",
            "حاصل الضرب يفصل حده الأخير",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "積の最後の項の分離",
            "積から最後の項を分離します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "곱의 마지막 항 분리",
            "곱에서 마지막 항을 분리합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích tách hạng cuối",
            "Tích tách hạng cuối",
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

impl FiniteSetSumListExpansionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "finite-set sum expand",
            "Sum over a list-set expands to an explicit sum",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集求和展开",
            "列表集上的求和展开为显式和",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合和展開",
            "列表集合上的和展開為明確加總",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Développement de somme sur ensemble fini",
            "La somme sur un ensemble liste se développe en somme explicite",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Раскрытие суммы по конечному множеству",
            "Сумма по списочному множеству раскрывается в явную сумму",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Expansión de suma de conjunto finito",
            "La suma sobre conjunto de lista se expande a suma explícita",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توسيع مجموع مجموعة منتهية",
            "المجموع على مجموعة قائمة يتوسع إلى مجموع صريح",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の和の展開",
            "リスト集合上の和を明示的な和に展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한 집합 합 전개",
            "목록 집합 위의 합을 명시적 합으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khai triển tổng tập hữu hạn",
            "Tổng trên tập danh sách khai triển thành tổng tường minh",
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

impl FiniteSetProductListExpansionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "finite-set product expand",
            "Product over a list-set expands to an explicit product",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集求积展开",
            "列表集上的求积展开为显式积",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合乘積展開",
            "列表集合上的乘積展開為明確乘積",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Développement du produit sur ensemble fini",
            "Le produit sur un ensemble liste se développe en produit explicite",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Раскрытие произведения по конечному множеству",
            "Произведение по списочному множеству раскрывается в явное произведение",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Expansión de producto de conjunto finito",
            "El producto sobre conjunto de lista se expande a producto explícito",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توسيع حاصل ضرب مجموعة منتهية",
            "حاصل الضرب على مجموعة قائمة يتوسع إلى حاصل ضرب صريح",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の積の展開",
            "リスト集合上の積を明示的な積に展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한 집합 곱 전개",
            "목록 집합 위의 곱을 명시적 곱으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khai triển tích tập hữu hạn",
            "Tích trên tập danh sách khai triển thành tích tường minh",
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

impl EulerEqualsExpOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Euler constant as the exponential of one", "The Euler constant as the exponential of one law gives: e = exp(1)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("欧拉数等于一的指数函数值", "欧拉数等于一的指数函数值可写为：e = exp(1)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("歐拉數等於一的指數函數值", "歐拉數等於一的指數函數值可寫為：e = exp(1)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Constante d’Euler comme exponentielle de un", "La propriété « Constante d’Euler comme exponentielle de un » donne: e = exp(1)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Число Эйлера как экспонента единицы", "Свойство «Число Эйлера как экспонента единицы» выражается равенством: e = exp(1)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Constante de Euler como exponencial de uno", "La propiedad «Constante de Euler como exponencial de uno» se expresa como: e = exp(1)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("ثابت أويلر كقيمة الدالة الأسية عند واحد", "تُكتب خاصية «ثابت أويلر كقيمة الدالة الأسية عند واحد» كما يلي: e = exp(1)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("一における指数関数とオイラー数", "一における指数関数とオイラー数は次の式で表されます：e = exp(1)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("일에서의 지수함수 값과 오일러 수", "일에서의 지수함수 값과 오일러 수은 다음 식으로 나타납니다: e = exp(1)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hằng số Euler bằng hàm mũ tại một", "Tính chất «Hằng số Euler bằng hàm mũ tại một» được biểu diễn bởi: e = exp(1)")
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

impl LnOfEulerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Natural logarithm of the Euler constant", "The Natural logarithm of the Euler constant law gives: ln(e) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("欧拉数的自然对数", "欧拉数的自然对数可写为：ln(e) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("歐拉數的自然對數", "歐拉數的自然對數可寫為：ln(e) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Logarithme naturel de la constante d’Euler", "La propriété « Logarithme naturel de la constante d’Euler » donne: ln(e) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Натуральный логарифм числа Эйлера", "Свойство «Натуральный логарифм числа Эйлера» выражается равенством: ln(e) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Logaritmo natural de la constante de Euler", "La propiedad «Logaritmo natural de la constante de Euler» se expresa como: ln(e) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("اللوغاريتم الطبيعي لثابت أويلر", "تُكتب خاصية «اللوغاريتم الطبيعي لثابت أويلر» كما يلي: ln(e) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("オイラー数の自然対数", "オイラー数の自然対数は次の式で表されます：ln(e) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("오일러 수의 자연로그", "오일러 수의 자연로그은 다음 식으로 나타납니다: ln(e) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Logarit tự nhiên của hằng số Euler", "Tính chất «Logarit tự nhiên của hằng số Euler» được biểu diễn bởi: ln(e) = 1")
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

impl ReOfRealBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Re(x) for real x", "Re(x) = x for real x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数的 Re", "对实数 x，Re(x) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("Re(x)（x 為實數）", "Re(x) = x（x 為實數）")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Re(x) pour x réel", "Re(x) = x pour x réel")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Re(x) для вещественного x",
            "Re(x) = x для вещественного x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Re(x) para x real", "Re(x) = x para x real")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "Re(x) للعدد الحقيقي x",
            "Re(x) = x للعدد الحقيقي x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("Re(x)（x は実数）", "Re(x) = x（x は実数）")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("Re(x)(x는 실수)", "Re(x) = x(x는 실수)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Re(x) với x thực", "Re(x) = x với x thực")
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

impl ImgOfRealBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Im(x) for real x", "Im(x) = 0 for real x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数的 Im", "对实数 x，Im(x) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("Im(x)（x 為實數）", "Im(x) = 0（x 為實數）")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Im(x) pour x réel", "Im(x) = 0 pour x réel")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Im(x) для вещественного x",
            "Im(x) = 0 для вещественного x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Im(x) para x real", "Im(x) = 0 para x real")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "Im(x) للعدد الحقيقي x",
            "Im(x) = 0 للعدد الحقيقي x",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("Im(x)（x は実数）", "Im(x) = 0（x は実数）")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("Im(x)(x는 실수)", "Im(x) = 0(x는 실수)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Im(x) với x thực", "Im(x) = 0 với x thực")
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

impl ReOfRealPlusImagScaledBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Real part of x + y·i", "The Real part of x + y·i equals x: re(x + y·i) = x")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("x + y·i 的实部", "x + y·i 的实部等于 x，即 re(x + y·i) = x")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("x + y·i 的實部", "x + y·i 的實部等於 x，即 re(x + y·i) = x")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie réelle de x + y·i", "La valeur « Partie réelle » de x + y·i est x: re(x + y·i) = x")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Вещественная часть числа x + y·i", "Для x + y·i величина «Вещественная часть» равна x: re(x + y·i) = x")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte real de x + y·i", "El valor «Parte real» de x + y·i es x: re(x + y·i) = x")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء الحقيقي لـ x + y·i", "قيمة «الجزء الحقيقي» لـ x + y·i تساوي x: re(x + y·i) = x")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("x + y·i の実部", "x + y·i の実部は x です：re(x + y·i) = x")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("x + y·i의 실수부", "x + y·i의 실수부는 x입니다: re(x + y·i) = x")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần thực của x + y·i", "Giá trị «Phần thực» của x + y·i bằng x: re(x + y·i) = x")
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

impl ImgOfRealPlusImagScaledBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Imaginary part of x + y·i", "The Imaginary part of x + y·i equals y: img(x + y·i) = y")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("x + y·i 的虚部", "x + y·i 的虚部等于 y，即 img(x + y·i) = y")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("x + y·i 的虛部", "x + y·i 的虛部等於 y，即 img(x + y·i) = y")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Partie imaginaire de x + y·i", "La valeur « Partie imaginaire » de x + y·i est y: img(x + y·i) = y")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Мнимая часть числа x + y·i", "Для x + y·i величина «Мнимая часть» равна y: img(x + y·i) = y")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Parte imaginaria de x + y·i", "El valor «Parte imaginaria» de x + y·i es y: img(x + y·i) = y")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الجزء التخيلي لـ x + y·i", "قيمة «الجزء التخيلي» لـ x + y·i تساوي y: img(x + y·i) = y")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("x + y·i の虚部", "x + y·i の虚部は y です：img(x + y·i) = y")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("x + y·i의 허수부", "x + y·i의 허수부는 y입니다: img(x + y·i) = y")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Phần ảo của x + y·i", "Giá trị «Phần ảo» của x + y·i bằng y: img(x + y·i) = y")
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

impl ComplexAbsOfNonnegRealBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "|x| for x≥0 real",
            "|embed(x)| = x for x ≥ 0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非负实数模",
            "对 x ≥ 0，|embed(x)| = x",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非負實數 x 的 |x|",
            "|embed(x)| = x（x ≥ 0 時）",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "|x| pour x réel non négatif",
            "|embed(x)| = x pour x ≥ 0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "|x| для неотрицательного вещественного x",
            "|embed(x)| = x для x ≥ 0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "|x| para x real no negativo",
            "|embed(x)| = x para x ≥ 0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "|x| للعدد الحقيقي غير السالب x",
            "|embed(x)| = x لـ x ≥ 0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負実数 x の |x|",
            "|embed(x)| = x（x ≥ 0 の場合）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음이 아닌 실수 x의 |x|",
            "|embed(x)| = x(x ≥ 0일 때)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "|x| với x thực không âm",
            "|embed(x)| = x với x ≥ 0",
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

impl ComplexAbsOfImagScaledBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Complex modulus of y·i", "The Complex modulus of y·i equals abs(y): C_abs(y·i) = abs(y)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("y·i 的复数模", "y·i 的复数模等于 abs(y)，即 C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("y·i 的複數模", "y·i 的複數模等於 abs(y)，即 C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Module complexe de y·i", "La valeur « Module complexe » de y·i est abs(y): C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Модуль комплексного числа числа y·i", "Для y·i величина «Модуль комплексного числа» равна abs(y): C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Módulo complejo de y·i", "El valor «Módulo complejo» de y·i es abs(y): C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المقياس المركب لـ y·i", "قيمة «المقياس المركب» لـ y·i تساوي abs(y): C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("y·i の複素数の絶対値", "y·i の複素数の絶対値は abs(y) です：C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("y·i의 복소수의 절댓값", "y·i의 복소수 절댓값은 abs(y)입니다: C_abs(y·i) = abs(y)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Môđun phức của y·i", "Giá trị «Môđun phức» của y·i bằng abs(y): C_abs(y·i) = abs(y)")
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

impl ClosedRangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "closed range expand",
            "A numeric closed range expands to an explicit list set",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "闭区间展开",
            "数值闭区间展开为显式列表集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "封閉區間展開",
            "數值封閉區間展開為明確列表集合",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Développement d'intervalle fermé",
            "Un intervalle numérique fermé se développe en ensemble liste explicite",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Раскрытие замкнутого интервала",
            "Числовой замкнутый интервал раскрывается в явное списочное множество",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Expansión de intervalo cerrado",
            "Un intervalo numérico cerrado se expande a conjunto de lista explícito",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توسيع فترة مغلقة",
            "تتوسع الفترة العددية المغلقة إلى مجموعة قائمة صريحة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉区間の展開",
            "数値の閉区間を明示的なリスト集合に展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 구간 전개",
            "수치 닫힌 구간을 명시적 목록 집합으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khai triển khoảng đóng",
            "Khoảng đóng dạng số khai triển thành tập danh sách tường minh",
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

impl RangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "range expand",
            "A numeric range expands to an explicit list set",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "区间展开",
            "数值区间展开为显式列表集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "區間展開",
            "數值區間展開為明確列表集合",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Développement d'intervalle",
            "Un intervalle numérique se développe en ensemble liste explicite",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Раскрытие интервала",
            "Числовой интервал раскрывается в явное списочное множество",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Expansión de intervalo",
            "Un intervalo numérico se expande a conjunto de lista explícito",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توسيع فترة",
            "تتوسع الفترة العددية إلى مجموعة قائمة صريحة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "区間の展開",
            "数値区間を明示的なリスト集合に展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "구간 전개",
            "수치 구간을 명시적 목록 집합으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khai triển khoảng",
            "Khoảng dạng số khai triển thành tập danh sách tường minh",
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

impl PowerSetOfEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power set of the empty set", "The Power set of the empty set law gives: pow(∅) = {∅}")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空集的幂集", "空集的幂集可写为：pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空集的冪集", "空集的冪集可寫為：pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Ensemble des parties de l’ensemble vide", "La propriété « Ensemble des parties de l’ensemble vide » donne: pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Булеан пустого множества", "Свойство «Булеан пустого множества» выражается равенством: pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Conjunto potencia del conjunto vacío", "La propiedad «Conjunto potencia del conjunto vacío» se expresa como: pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("مجموعة أجزاء المجموعة الخالية", "تُكتب خاصية «مجموعة أجزاء المجموعة الخالية» كما يلي: pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合の冪集合", "空集合の冪集合は次の式で表されます：pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합의 멱집합", "공집합의 멱집합은 다음 식으로 나타납니다: pow(∅) = {∅}")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tập lũy thừa của tập rỗng", "Tính chất «Tập lũy thừa của tập rỗng» được biểu diễn bởi: pow(∅) = {∅}")
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

impl PowerSetOfSingletonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Power set of a singleton", "The Power set of a singleton law gives: pow({a}) = {∅, {a}}")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("单元素集合的幂集", "单元素集合的幂集可写为：pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單元素集合的冪集", "單元素集合的冪集可寫為：pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Ensemble des parties d’un singleton", "La propriété « Ensemble des parties d’un singleton » donne: pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Булеан одноэлементного множества", "Свойство «Булеан одноэлементного множества» выражается равенством: pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Conjunto potencia de un conjunto unitario", "La propiedad «Conjunto potencia de un conjunto unitario» se expresa como: pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("مجموعة أجزاء مجموعة أحادية العنصر", "تُكتب خاصية «مجموعة أجزاء مجموعة أحادية العنصر» كما يلي: pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("単集合の冪集合", "単集合の冪集合は次の式で表されます：pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("한원소 집합의 멱집합", "한원소 집합의 멱집합은 다음 식으로 나타납니다: pow({a}) = {∅, {a}}")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tập lũy thừa của tập đơn", "Tính chất «Tập lũy thừa của tập đơn» được biểu diễn bởi: pow({a}) = {∅, {a}}")
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

impl FamilyUnionOfEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Union of an empty family", "The Union of an empty family law gives: ⋃∅ = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空集合族的并集", "空集合族的并集可写为：⋃∅ = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空集合族的聯集", "空集合族的聯集可寫為：⋃∅ = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Union d’une famille vide", "La propriété « Union d’une famille vide » donne: ⋃∅ = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Объединение пустого семейства", "Свойство «Объединение пустого семейства» выражается равенством: ⋃∅ = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Unión de una familia vacía", "La propiedad «Unión de una familia vacía» se expresa como: ⋃∅ = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("اتحاد عائلة خالية", "تُكتب خاصية «اتحاد عائلة خالية» كما يلي: ⋃∅ = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空の集合族の和集合", "空の集合族の和集合は次の式で表されます：⋃∅ = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("빈 집합족의 합집합", "빈 집합족의 합집합은 다음 식으로 나타납니다: ⋃∅ = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hợp của họ rỗng", "Tính chất «Hợp của họ rỗng» được biểu diễn bởi: ⋃∅ = ∅")
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

impl CartWithEmptyFactorBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Cartesian product with an empty factor", "The Cartesian product with an empty factor law gives: A × ∅ = ∅")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("含空因子的笛卡尔积", "含空因子的笛卡尔积可写为：A × ∅ = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("含空因子的笛卡兒積", "含空因子的笛卡兒積可寫為：A × ∅ = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Produit cartésien avec un facteur vide", "La propriété « Produit cartésien avec un facteur vide » donne: A × ∅ = ∅")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Декартово произведение с пустым множителем", "Свойство «Декартово произведение с пустым множителем» выражается равенством: A × ∅ = ∅")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Producto cartesiano con un factor vacío", "La propiedad «Producto cartesiano con un factor vacío» se expresa como: A × ∅ = ∅")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الضرب الديكارتي بعامل خالٍ", "تُكتب خاصية «الضرب الديكارتي بعامل خالٍ» كما يلي: A × ∅ = ∅")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空集合を因子に持つ直積", "空集合を因子に持つ直積は次の式で表されます：A × ∅ = ∅")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("공집합 인수를 갖는 데카르트 곱", "공집합 인수를 갖는 데카르트 곱은 다음 식으로 나타납니다: A × ∅ = ∅")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Tích Descartes có một thừa số rỗng", "Tính chất «Tích Descartes có một thừa số rỗng» được biểu diễn bởi: A × ∅ = ∅")
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

impl UnionOverIntersectDistributiveBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union distributes over intersection",
            "The Union distributes over intersection law gives: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "并集对交集的分配律",
            "并集对交集的分配律可写为：A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "聯集對交集的分配律",
            "聯集對交集的分配律可寫為：A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Distributivité de l’union sur l’intersection",
            "La propriété « Distributivité de l’union sur l’intersection » donne: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Дистрибутивность объединения относительно пересечения",
            "Свойство «Дистрибутивность объединения относительно пересечения» выражается равенством: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Distributividad de la unión sobre la intersección",
            "La propiedad «Distributividad de la unión sobre la intersección» se expresa como: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "توزيع الاتحاد على التقاطع",
            "تُكتب خاصية «توزيع الاتحاد على التقاطع» كما يلي: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "共通部分に対する和集合の分配法則",
            "共通部分に対する和集合の分配法則は次の式で表されます：A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "교집합에 대한 합집합의 분배법칙",
            "교집합에 대한 합집합의 분배법칙은 다음 식으로 나타납니다: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phân phối của hợp đối với giao",
            "Tính chất «Tính phân phối của hợp đối với giao» được biểu diễn bởi: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
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

impl SetMinusChainToUnionBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "chained difference",
            "A \\ B \\ C expands via union of removed sets",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "链式差集",
            "A \\\\ B \\\\ C 通过被去掉集合的并展开",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "連續差集",
            "A \\ B \\ C 以被移除集合之聯集展開",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence en chaîne",
            "A \\ B \\ C se développe par l'union des ensembles retirés",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Последовательная разность",
            "A \\ B \\ C раскрывается через объединение удаляемых множеств",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia encadenada",
            "A \\ B \\ C se expande por la unión de conjuntos retirados",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فرق متسلسل",
            "يتوسع A \\ B \\ C باتحاد المجموعات المحذوفة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "連続する差集合",
            "A \\ B \\ C を除かれる集合の和で展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "연속 차집합",
            "A \\ B \\ C를 제거되는 집합의 합집합으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu liên tiếp",
            "A \\ B \\ C khai triển qua hợp các tập bị loại",
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

impl FnRangeOfConstantAnonymousFnBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "range of constant fn",
            "A constant function with nonempty complete domain has singleton image",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "常值函数值域",
            "完整定义域非空的常值函数，其像是单点集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "常數函數值域",
            "完整定義域非空的常值函數，其像為單元素集合",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Image d'une fonction constante",
            "Une fonction constante de domaine complet non vide a une image singleton",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Область значений постоянной функции",
            "Образ постоянной функции с непустой полной областью определения является одноэлементным множеством",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Rango de función constante",
            "La imagen de una función constante con dominio completo no vacío es un conjunto unitario",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مدى دالة ثابتة",
            "صورة الدالة الثابتة ذات مجال التعريف الكامل غير الفارغ مجموعة أحادية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "定数関数の値域",
            "完全な定義域が空でない定数関数の像は一要素集合です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "상수 함수의 치역",
            "전체 정의역이 비어 있지 않은 상수 함수의 상은 한 원소 집합입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Miền giá trị hàm hằng",
            "Hàm hằng có miền xác định đầy đủ không rỗng có ảnh gồm một phần tử",
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

impl SeqEqualsFnOnNPosBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "seq as fn on N+",
            "A sequence equals its function on positive integers",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "序列即 N+ 上函数",
            "序列等于其在正整数上的函数",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "N+ 上的序列函數",
            "序列等於其在正整數上的函數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Suite comme fonction sur N+",
            "Une suite est égale à sa fonction sur les entiers positifs",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Последовательность как функция на N+",
            "Последовательность равна своей функции на положительных целых",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Secuencia como función en N+",
            "Una secuencia equivale a su función en enteros positivos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "متتالية كدالة على N+",
            "المتتالية تساوي دالتها على الأعداد الصحيحة الموجبة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "N+ 上の関数としての列",
            "列は正の整数上の関数に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "N+ 위의 함수로서의 수열",
            "수열은 양의 정수 위의 함수와 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Dãy là hàm trên N+",
            "Dãy bằng hàm trên các số nguyên dương",
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

impl FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "finite seq as fn",
            "A finite sequence equals its function on indices 1 through its length",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限序列即函数",
            "有限序列等于其在 1 至长度上的函数",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限序列視為函數",
            "有限序列等於在索引 1 至其長度上的函數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Suite finie comme fonction",
            "Une suite finie est égale à sa fonction sur les indices de 1 à sa longueur",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Конечная последовательность как функция",
            "Конечная последовательность равна своей функции на индексах от 1 до её длины",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Secuencia finita como función",
            "Una secuencia finita equivale a su función en índices de 1 hasta su longitud",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "متتالية منتهية كدالة",
            "المتتالية المنتهية تساوي دالتها على الفهارس من 1 إلى طولها",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "関数としての有限列",
            "有限列は添字 1 からその長さまでの関数に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "함수로서의 유한 수열",
            "유한 수열은 인덱스 1부터 길이까지의 함수와 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Dãy hữu hạn là hàm",
            "Dãy hữu hạn bằng hàm trên chỉ số từ 1 đến độ dài của nó",
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

impl IndexUnionEmptyIndexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Indexed union over an empty index set",
            "The Indexed union over an empty index set law gives: index_union(∅, X, A) = ∅",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空索引集上的指标并集", "空索引集上的指标并集可写为：index_union(∅, X, A) = ∅")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空索引集上的指標聯集", "空索引集上的指標聯集可寫為：index_union(∅, X, A) = ∅")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Union indexée par un ensemble vide",
            "La propriété « Union indexée par un ensemble vide » donne: index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Объединение по пустому множеству индексов",
            "Свойство «Объединение по пустому множеству индексов» выражается равенством: index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Unión indexada por el conjunto vacío",
            "La propiedad «Unión indexada por el conjunto vacío» se expresa como: index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اتحاد مفهرس على مجموعة فهارس خالية",
            "تُكتب خاصية «اتحاد مفهرس على مجموعة فهارس خالية» كما يلي: index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の添字集合上の和集合",
            "空の添字集合上の和集合は次の式で表されます：index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 첨자 집합에 대한 합집합",
            "빈 첨자 집합에 대한 합집합은 다음 식으로 나타납니다: index_union(∅, X, A) = ∅",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp có tập chỉ số rỗng",
            "Tính chất «Hợp có tập chỉ số rỗng» được biểu diễn bởi: index_union(∅, X, A) = ∅",
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

impl IndexIntersectEmptyIndexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Indexed intersection over an empty index set", "With no indexed constraints, the intersection equals the supplied ambient set X: index_intersect(∅, X, A) = X")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "空索引集上的指标交集",
            "索引集为空时没有成员约束，交集等于给定的背景集合 X，即 index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "空索引集上的指標交集",
            "索引集為空時沒有成員約束，交集等於給定的背景集合 X，即 index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intersection indexée par un ensemble vide",
            "Sans contrainte indexée, l’intersection est l’ensemble ambiant X fourni: index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Пересечение по пустому множеству индексов", "Без индексированных ограничений пересечение равно заданному объемлющему множеству X: index_intersect(∅, X, A) = X")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intersección indexada por el conjunto vacío",
            "Sin restricciones indexadas, la intersección es el conjunto ambiente X indicado: index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تقاطع مفهرس على مجموعة فهارس خالية",
            "عند غياب القيود المفهرسة يساوي التقاطع المجموعة المحيطة X المعطاة: index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の添字集合上の共通部分",
            "添字による制約がないため、共通部分は指定された全体集合 X です：index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 첨자 집합에 대한 교집합",
            "첨자에 따른 제약이 없으므로 교집합은 주어진 전체 집합 X입니다: index_intersect(∅, X, A) = X",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giao có tập chỉ số rỗng",
            "Khi không có ràng buộc theo chỉ số, giao bằng tập nền X đã cho: index_intersect(∅, X, A) = X",
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

impl IndexCartEmptyIndexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "indexed cart empty",
            "Indexed Cartesian product over an empty index is a unit",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "空指标笛卡尔积",
            "空指标上的指标笛卡尔积是单位",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "空索引笛卡兒積",
            "空索引上的帶索引笛卡兒積為單位元",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit cartésien à indice vide",
            "Le produit cartésien indexé sur un indice vide est une unité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Декартово произведение по пустому индексу",
            "Индексированное декартово произведение по пустому индексу является единицей",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto cartesiano de índice vacío",
            "El producto cartesiano indexado sobre índice vacío es una unidad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل ضرب ديكارتي بفهرس خالٍ",
            "حاصل الضرب الديكارتي المفهرس على فهرس خالٍ هو وحدة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の添字集合の直積",
            "空の添字集合上の直積は単位です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 인덱스 데카르트 곱",
            "빈 인덱스 위의 데카르트 곱은 단위원입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích Descartes chỉ số rỗng",
            "Tích Descartes theo chỉ số rỗng là đơn vị",
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

impl IndexUnionSingletonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Indexed union over a singleton index set",
            "The Indexed union over a singleton index set law gives: index_union({i}, X, A) = A(i)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "单元素索引集上的指标并集",
            "单元素索引集上的指标并集可写为：index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "單元素索引集上的指標聯集",
            "單元素索引集上的指標聯集可寫為：index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Union indexée par un singleton",
            "La propriété « Union indexée par un singleton » donne: index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Объединение по одному индексу",
            "Свойство «Объединение по одному индексу» выражается равенством: index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Unión indexada por un conjunto unitario",
            "La propiedad «Unión indexada por un conjunto unitario» se expresa como: index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اتحاد مفهرس على مجموعة فهارس أحادية",
            "تُكتب خاصية «اتحاد مفهرس على مجموعة فهارس أحادية» كما يلي: index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "添字が一つの和集合",
            "添字が一つの和集合は次の式で表されます：index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한원소 첨자 집합에 대한 합집합",
            "한원소 첨자 집합에 대한 합집합은 다음 식으로 나타납니다: index_union({i}, X, A) = A(i)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp có tập chỉ số đơn",
            "Tính chất «Hợp có tập chỉ số đơn» được biểu diễn bởi: index_union({i}, X, A) = A(i)",
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

impl FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "empty finite seq",
            "The length-0 finite sequence equals the function on the empty range",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "空有限序列",
            "长度为 0 的有限序列等于空区间上的函数",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "空有限序列",
            "長度為零的有限序列等於空區間上的函數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Suite finie vide",
            "La suite finie de longueur zéro est égale à la fonction sur l'intervalle vide",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пустая конечная последовательность",
            "Конечная последовательность длины ноль равна функции на пустом интервале",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Secuencia finita vacía",
            "La secuencia finita de longitud cero equivale a la función en rango vacío",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "متتالية منتهية خالية",
            "المتتالية المنتهية بطول صفر تساوي الدالة على الفترة الخالية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の有限列",
            "長さゼロの有限列は空区間上の関数に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 유한 수열",
            "길이 0인 유한 수열은 빈 구간 위의 함수와 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Dãy hữu hạn rỗng",
            "Dãy hữu hạn độ dài không bằng hàm trên khoảng rỗng",
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

impl SetBuilderObviouslyEmptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "empty set-builder",
            "A contradictory set-builder equals ∅",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "空集合构造器",
            "矛盾的集合构造器等于 ∅",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "空集合構造",
            "條件矛盾的集合構造等於 ∅",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Compréhension vide",
            "Un ensemble en compréhension contradictoire est égal à ∅",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пустое множество по условию",
            "Множество с противоречивым условием равно ∅",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Comprensión vacía",
            "Un conjunto por comprensión contradictorio es igual a ∅",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "بناء مجموعة خالية",
            "المجموعة المبنية بشرط متناقض تساوي ∅",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "空の内包表記集合",
            "矛盾する条件の内包表記集合は ∅ です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "빈 조건제시 집합",
            "조건이 모순인 조건제시 집합은 ∅입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập dựng rỗng",
            "Tập dựng có điều kiện mâu thuẫn bằng ∅",
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

impl ComplexAbsSquaredOfRectFormBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Squared modulus of a complex number in rectangular form",
            "The Squared modulus of a complex number in rectangular form law gives: C_abs(x + y·i)² = x² + y²",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "直角坐标形式复数的模平方",
            "直角坐标形式复数的模平方可写为：C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "直角座標形式複數的模平方",
            "直角座標形式複數的模平方可寫為：C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Carré du module d’un complexe en forme cartésienne",
            "La propriété « Carré du module d’un complexe en forme cartésienne » donne: C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Квадрат модуля комплексного числа в алгебраической форме",
            "Свойство «Квадрат модуля комплексного числа в алгебраической форме» выражается равенством: C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Módulo al cuadrado de un complejo en forma cartesiana",
            "La propiedad «Módulo al cuadrado de un complejo en forma cartesiana» se expresa como: C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مربع مقياس عدد مركب بالصورة الديكارتية",
            "تُكتب خاصية «مربع مقياس عدد مركب بالصورة الديكارتية» كما يلي: C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "直交形式の複素数の絶対値の二乗",
            "直交形式の複素数の絶対値の二乗は次の式で表されます：C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "직교형 복소수 절댓값의 제곱",
            "직교형 복소수 절댓값의 제곱은 다음 식으로 나타납니다: C_abs(x + y·i)² = x² + y²",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bình phương môđun của số phức dạng đại số",
            "Tính chất «Bình phương môđun của số phức dạng đại số» được biểu diễn bởi: C_abs(x + y·i)² = x² + y²",
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

impl ExpOfSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Exponential of a sum", "The Exponential of a sum law gives: exp(x+y) = exp(x)·exp(y)")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("和的指数运算", "和的指数运算可写为：exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("和的指數運算", "和的指數運算可寫為：exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Exponentielle d’une somme", "La propriété « Exponentielle d’une somme » donne: exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Экспонента суммы", "Свойство «Экспонента суммы» выражается равенством: exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Exponencial de una suma", "La propiedad «Exponencial de una suma» se expresa como: exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("الدالة الأسية لمجموع", "تُكتب خاصية «الدالة الأسية لمجموع» كما يلي: exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("和の指数関数", "和の指数関数は次の式で表されます：exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("합의 지수함수", "합의 지수함수은 다음 식으로 나타납니다: exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Hàm mũ của một tổng", "Tính chất «Hàm mũ của một tổng» được biểu diễn bởi: exp(x+y) = exp(x)·exp(y)")
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

impl LogBasePowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Power in the logarithm base",
            "The Power in the logarithm base law gives: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "对数底数中的幂",
            "对数底数中的幂可写为：log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "對數底數中的冪",
            "對數底數中的冪可寫為：log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance dans la base du logarithme",
            "La propriété « Puissance dans la base du logarithme » donne: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Степень в основании логарифма",
            "Свойство «Степень в основании логарифма» выражается равенством: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia en la base del logaritmo",
            "La propiedad «Potencia en la base del logaritmo» se expresa como: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القوة في أساس اللوغاريتم",
            "تُكتب خاصية «القوة في أساس اللوغاريتم» كما يلي: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "対数の底の累乗",
            "対数の底の累乗は次の式で表されます：log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "로그 밑의 거듭제곱",
            "로그 밑의 거듭제곱은 다음 식으로 나타납니다: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa trong cơ số logarit",
            "Tính chất «Lũy thừa trong cơ số logarit» được biểu diễn bởi: log_(a^n)(b) = (1/n)·log_a(b); a>0; a!=1; n in R; n!=0; b>0",
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

impl ReOfProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real part of a complex product",
            "The Real part of a complex product law gives: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("复数乘积的实部", "复数乘积的实部可写为：re(z·w) = re(z)·re(w) - img(z)·img(w)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("複數乘積的實部", "複數乘積的實部可寫為：re(z·w) = re(z)·re(w) - img(z)·img(w)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Partie réelle d’un produit complexe",
            "La propriété « Partie réelle d’un produit complexe » donne: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вещественная часть произведения комплексных чисел",
            "Свойство «Вещественная часть произведения комплексных чисел» выражается равенством: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Parte real de un producto complejo",
            "La propiedad «Parte real de un producto complejo» se expresa como: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الجزء الحقيقي لحاصل ضرب مركب",
            "تُكتب خاصية «الجزء الحقيقي لحاصل ضرب مركب» كما يلي: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "複素数の積の実部",
            "複素数の積の実部は次の式で表されます：re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "복소수 곱의 실수부",
            "복소수 곱의 실수부은 다음 식으로 나타납니다: re(z·w) = re(z)·re(w) - img(z)·img(w)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phần thực của tích số phức",
            "Tính chất «Phần thực của tích số phức» được biểu diễn bởi: re(z·w) = re(z)·re(w) - img(z)·img(w)",
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

impl ImgOfProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Imaginary part of a complex product",
            "The Imaginary part of a complex product law gives: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("复数乘积的虚部", "复数乘积的虚部可写为：img(z·w) = re(z)·img(w) + img(z)·re(w)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("複數乘積的虛部", "複數乘積的虛部可寫為：img(z·w) = re(z)·img(w) + img(z)·re(w)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Partie imaginaire d’un produit complexe",
            "La propriété « Partie imaginaire d’un produit complexe » donne: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Мнимая часть произведения комплексных чисел",
            "Свойство «Мнимая часть произведения комплексных чисел» выражается равенством: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Parte imaginaria de un producto complejo",
            "La propiedad «Parte imaginaria de un producto complejo» se expresa como: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الجزء التخيلي لحاصل ضرب مركب",
            "تُكتب خاصية «الجزء التخيلي لحاصل ضرب مركب» كما يلي: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "複素数の積の虚部",
            "複素数の積の虚部は次の式で表されます：img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "복소수 곱의 허수부",
            "복소수 곱의 허수부은 다음 식으로 나타납니다: img(z·w) = re(z)·img(w) + img(z)·re(w)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phần ảo của tích số phức",
            "Tính chất «Phần ảo của tích số phức» được biểu diễn bởi: img(z·w) = re(z)·img(w) + img(z)·re(w)",
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

impl SinOfSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sine addition formula",
            "The Sine addition formula law gives: sin(x+y) = sin x cos y + cos x sin y",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "正弦和角公式",
            "正弦和角公式可写为：sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正弦和角公式",
            "正弦和角公式可寫為：sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Formule d’addition du sinus",
            "La propriété « Formule d’addition du sinus » donne: sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Формула синуса суммы",
            "Свойство «Формула синуса суммы» выражается равенством: sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Fórmula de suma del seno",
            "La propiedad «Fórmula de suma del seno» se expresa como: sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "صيغة جيب مجموع زاويتين",
            "تُكتب خاصية «صيغة جيب مجموع زاويتين» كما يلي: sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正弦の加法定理",
            "正弦の加法定理は次の式で表されます：sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "사인 덧셈 공식",
            "사인 덧셈 공식은 다음 식으로 나타납니다: sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Công thức sin của tổng",
            "Tính chất «Công thức sin của tổng» được biểu diễn bởi: sin(x+y) = sin x cos y + cos x sin y",
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

impl CosOfSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cosine addition formula",
            "The Cosine addition formula law gives: cos(x+y) = cos x cos y − sin x sin y",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "余弦和角公式",
            "余弦和角公式可写为：cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "餘弦和角公式",
            "餘弦和角公式可寫為：cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Formule d’addition du cosinus",
            "La propriété « Formule d’addition du cosinus » donne: cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Формула косинуса суммы",
            "Свойство «Формула косинуса суммы» выражается равенством: cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Fórmula de suma del coseno",
            "La propiedad «Fórmula de suma del coseno» se expresa como: cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "صيغة جيب تمام مجموع زاويتين",
            "تُكتب خاصية «صيغة جيب تمام مجموع زاويتين» كما يلي: cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "余弦の加法定理",
            "余弦の加法定理は次の式で表されます：cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "코사인 덧셈 공식",
            "코사인 덧셈 공식은 다음 식으로 나타납니다: cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Công thức cos của tổng",
            "Tính chất «Công thức cos của tổng» được biểu diễn bởi: cos(x+y) = cos x cos y − sin x sin y",
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

impl ReduceSingleTermWithAddZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "reduce one term",
            "Reduce with a single term and +0 equals that term",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "单项归约",
            "单项并以 +0 归约等于该项",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "單項折疊",
            "單項且以 +0 折疊時等於該項",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Pli à terme unique",
            "Un pli à terme unique avec +0 est égal à ce terme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Свёртка одного члена",
            "Свёртка одного члена с +0 равна этому члену",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pliegue de un término",
            "Un pliegue de un término con +0 equivale a ese término",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "طي حد واحد",
            "طي حد واحد مع +0 يساوي ذلك الحد",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "一項の畳み込み",
            "一項を +0 で畳み込むとその項に等しいです",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한 항 접기",
            "한 항을 +0으로 접으면 그 항과 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Gấp một hạng",
            "Gấp một hạng với +0 bằng hạng đó",
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

impl FiniteSetSumFubiniSwapBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Fubini swap for sums",
            "Finite double sums may swap summation order",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限双重和 Fubini",
            "有限双重和可交换求和次序",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "求和的 Fubini 交換",
            "有限二重和可交換求和順序",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Échange de Fubini pour les sommes",
            "Les sommes doubles finies permettent d'échanger l'ordre de sommation",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Перестановка сумм по Фубини",
            "В конечных двойных суммах можно менять порядок суммирования",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intercambio de Fubini para sumas",
            "Las sumas dobles finitas permiten intercambiar el orden de suma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تبديل فوبيني للمجاميع",
            "يمكن تبديل ترتيب الجمع في المجاميع المزدوجة المنتهية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "総和のフビニの交換",
            "有限二重和では総和の順序を交換できます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합의 푸비니 교환",
            "유한 이중 합은 합산 순서를 바꿀 수 있습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đổi tổng theo Fubini",
            "Tổng kép hữu hạn có thể đổi thứ tự lấy tổng",
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

impl FiniteSetSumOverCartesianProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "sum over A×B",
            "Sum over a Cartesian product expands as an iterated sum",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "A×B 上求和",
            "笛卡尔积上的求和展开为迭代和",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "A×B 上的和",
            "笛卡兒積上的和展開為疊代和",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme sur A×B",
            "La somme sur un produit cartésien se développe en somme itérée",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сумма по A×B",
            "Сумма по декартову произведению раскрывается в повторную сумму",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma sobre A×B",
            "La suma sobre producto cartesiano se expande a suma iterada",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع على A×B",
            "المجموع على حاصل ضرب ديكارتي يتوسع إلى مجموع متكرر",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "A×B 上の和",
            "直積上の和を反復和に展開します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "A×B 위의 합",
            "데카르트 곱 위의 합을 반복 합으로 전개합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tổng trên A×B",
            "Tổng trên tích Descartes khai triển thành tổng lặp",
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

impl SinOfZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of sine at zero", "The value of sine at zero is zero: sin(0) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正弦函数在零处的值", "正弦函数在零处的值为零，即 sin(0) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正弦函數在零處的值", "正弦函數在零處的值為零，即 sin(0) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur du sinus en zéro", "La valeur du sinus en zéro est zéro: sin(0) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «синус» при аргументе нуль", "При аргументе нуль функция «синус» принимает значение нуль: sin(0) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de seno en cero", "El valor de seno en cero es cero: sin(0) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب عند الصفر", "قيمة دالة الجيب عند الصفر تساوي الصفر: sin(0) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における正弦関数の値", "零における正弦関数の値は零です：sin(0) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 사인 함수 값", "영에서의 사인 함수 값은 영입니다: sin(0) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm sin tại không", "Giá trị của hàm sin tại không bằng không: sin(0) = 0")
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

impl CosOfZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of cosine at zero", "The value of cosine at zero is one: cos(0) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("余弦函数在零处的值", "余弦函数在零处的值为一，即 cos(0) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("餘弦函數在零處的值", "餘弦函數在零處的值為一，即 cos(0) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur du cosinus en zéro", "La valeur du cosinus en zéro est un: cos(0) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «косинус» при аргументе нуль", "При аргументе нуль функция «косинус» принимает значение единица: cos(0) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de coseno en cero", "El valor de coseno en cero es uno: cos(0) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة جيب التمام عند الصفر", "قيمة دالة جيب التمام عند الصفر تساوي الواحد: cos(0) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における余弦関数の値", "零における余弦関数の値は一です：cos(0) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 코사인 함수 값", "영에서의 코사인 함수 값은 일입니다: cos(0) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm cos tại không", "Giá trị của hàm cos tại không bằng một: cos(0) = 1")
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

impl TanOfZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of tangent at zero", "The value of tangent at zero is zero: tan(0) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正切函数在零处的值", "正切函数在零处的值为零，即 tan(0) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正切函數在零處的值", "正切函數在零處的值為零，即 tan(0) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de la tangente en zéro", "La valeur de la tangente en zéro est zéro: tan(0) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «тангенс» при аргументе нуль", "При аргументе нуль функция «тангенс» принимает значение нуль: tan(0) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de tangente en cero", "El valor de tangente en cero es cero: tan(0) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الظل عند الصفر", "قيمة دالة الظل عند الصفر تساوي الصفر: tan(0) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("零における正接関数の値", "零における正接関数の値は零です：tan(0) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("영에서의 탄젠트 함수 값", "영에서의 탄젠트 함수 값은 영입니다: tan(0) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm tan tại không", "Giá trị của hàm tan tại không bằng không: tan(0) = 0")
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

impl SinOfHalfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of sine at π/2", "The value of sine at π/2 is one: sin(π/2) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正弦函数在π/2处的值", "正弦函数在π/2处的值为一，即 sin(π/2) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正弦函數在π/2處的值", "正弦函數在π/2處的值為一，即 sin(π/2) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur du sinus en π/2", "La valeur du sinus en π/2 est un: sin(π/2) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «синус» при аргументе π/2", "При аргументе π/2 функция «синус» принимает значение единица: sin(π/2) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de seno en π/2", "El valor de seno en π/2 es uno: sin(π/2) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب عند π/2", "قيمة دالة الجيب عند π/2 تساوي الواحد: sin(π/2) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("π/2における正弦関数の値", "π/2における正弦関数の値は一です：sin(π/2) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("π/2에서의 사인 함수 값", "π/2에서의 사인 함수 값은 일입니다: sin(π/2) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm sin tại π/2", "Giá trị của hàm sin tại π/2 bằng một: sin(π/2) = 1")
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

impl CosOfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of cosine at π", "The value of cosine at π is minus one: cos(π) = -1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("余弦函数在π处的值", "余弦函数在π处的值为负一，即 cos(π) = -1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("餘弦函數在π處的值", "餘弦函數在π處的值為負一，即 cos(π) = -1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur du cosinus en π", "La valeur du cosinus en π est moins un: cos(π) = -1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «косинус» при аргументе π", "При аргументе π функция «косинус» принимает значение минус единица: cos(π) = -1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de coseno en π", "El valor de coseno en π es menos uno: cos(π) = -1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة جيب التمام عند π", "قيمة دالة جيب التمام عند π تساوي سالب واحد: cos(π) = -1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("πにおける余弦関数の値", "πにおける余弦関数の値は負の一です：cos(π) = -1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("π에서의 코사인 함수 값", "π에서의 코사인 함수 값은 음의 일입니다: cos(π) = -1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm cos tại π", "Giá trị của hàm cos tại π bằng âm một: cos(π) = -1")
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

impl SinOfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of sine at π", "The value of sine at π is zero: sin(π) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("正弦函数在π处的值", "正弦函数在π处的值为零，即 sin(π) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("正弦函數在π處的值", "正弦函數在π處的值為零，即 sin(π) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur du sinus en π", "La valeur du sinus en π est zéro: sin(π) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «синус» при аргументе π", "При аргументе π функция «синус» принимает значение нуль: sin(π) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de seno en π", "El valor de seno en π es cero: sin(π) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة الجيب عند π", "قيمة دالة الجيب عند π تساوي الصفر: sin(π) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("πにおける正弦関数の値", "πにおける正弦関数の値は零です：sin(π) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("π에서의 사인 함수 값", "π에서의 사인 함수 값은 영입니다: sin(π) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm sin tại π", "Giá trị của hàm sin tại π bằng không: sin(π) = 0")
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

impl CotOfHalfPiBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Value of cotangent at π/2", "The value of cotangent at π/2 is zero: cot(π/2) = 0")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("余切函数在π/2处的值", "余切函数在π/2处的值为零，即 cot(π/2) = 0")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("餘切函數在π/2處的值", "餘切函數在π/2處的值為零，即 cot(π/2) = 0")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Valeur de la cotangente en π/2", "La valeur de la cotangente en π/2 est zéro: cot(π/2) = 0")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Значение функции «котангенс» при аргументе π/2", "При аргументе π/2 функция «котангенс» принимает значение нуль: cot(π/2) = 0")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Valor de cotangente en π/2", "El valor de cotangente en π/2 es cero: cot(π/2) = 0")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة دالة ظل التمام عند π/2", "قيمة دالة ظل التمام عند π/2 تساوي الصفر: cot(π/2) = 0")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("π/2における余接関数の値", "π/2における余接関数の値は零です：cot(π/2) = 0")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("π/2에서의 코탄젠트 함수 값", "π/2에서의 코탄젠트 함수 값은 영입니다: cot(π/2) = 0")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị của hàm cot tại π/2", "Giá trị của hàm cot tại π/2 bằng không: cot(π/2) = 0")
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

impl PythagoreanIdentityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Trigonometric Pythagorean identity", "The Trigonometric Pythagorean identity law gives: sin²(x) + cos²(x) = 1")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("三角函数平方和恒等式", "三角函数平方和恒等式可写为：sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("三角函數平方和恆等式", "三角函數平方和恆等式可寫為：sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Identité trigonométrique de Pythagore", "La propriété « Identité trigonométrique de Pythagore » donne: sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Основное тригонометрическое тождество", "Свойство «Основное тригонометрическое тождество» выражается равенством: sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Identidad trigonométrica de Pitágoras", "La propiedad «Identidad trigonométrica de Pitágoras» se expresa como: sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("المتطابقة المثلثية لفيثاغورس", "تُكتب خاصية «المتطابقة المثلثية لفيثاغورس» كما يلي: sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("三角関数の二乗和の恒等式", "三角関数の二乗和の恒等式は次の式で表されます：sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("삼각함수 제곱합 항등식", "삼각함수 제곱합 항등식은 다음 식으로 나타납니다: sin²(x) + cos²(x) = 1")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Đồng nhất thức lượng giác Pythagore", "Tính chất «Đồng nhất thức lượng giác Pythagore» được biểu diễn bởi: sin²(x) + cos²(x) = 1")
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

impl FamilyUnionOfSingletonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union of a singleton family",
            "The union of a singleton family of sets is its member.",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "单元素集合族的并",
            "只包含集合 A 的集合族，其并集等于 A。",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "單元素集合族的聯集",
            "單元素集合族的聯集等於其成員。",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Union d'une famille singleton",
            "L'union d'une famille singleton d'ensembles est son membre.",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Объединение одноэлементного семейства",
            "Объединение одноэлементного семейства множеств равно его элементу.",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Unión de familia unitaria",
            "La unión de una familia unitaria de conjuntos es su miembro.",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اتحاد عائلة أحادية",
            "اتحاد عائلة أحادية من المجموعات يساوي عنصرها.",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "一要素の集合族の和",
            "一要素の集合族の和はその要素です。",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한 원소 집합족의 합집합",
            "한 원소 집합족의 합집합은 그 원소입니다.",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp của họ đơn phần tử",
            "Hợp của họ tập hợp đơn phần tử là phần tử của nó.",
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

impl FamilyUnionOfPowerSetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union of a power set",
            "The union of the power set of a set is that set.",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "幂集的并",
            "集合 A 的幂集中所有集合的并等于 A。",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "冪集的聯集",
            "集合冪集中所有集合的聯集等於該集合。",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Union de l'ensemble des parties",
            "L'union de l'ensemble des parties d'un ensemble est cet ensemble.",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Объединение множества подмножеств",
            "Объединение множества подмножеств множества равно этому множеству.",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Unión de conjunto potencia",
            "La unión del conjunto potencia de un conjunto es ese conjunto.",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اتحاد مجموعة القوى",
            "اتحاد مجموعة القوى لمجموعة يساوي تلك المجموعة.",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "べき集合の和",
            "集合のべき集合の和はその集合です。",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "멱집합의 합집합",
            "집합의 멱집합의 합집합은 그 집합입니다.",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hợp của tập lũy thừa",
            "Hợp của tập lũy thừa của một tập là chính tập đó.",
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_first_step::ReduceFirstStepProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "First left-fold step".into(), message: "A nonempty left fold moves its first term into the seed, preserving operand order".into() }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "左折叠的首项递推" .into(), message: "非空左折叠按原运算顺序将首项并入初值" .into() }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "左折疊的首項遞推".into(), message: "非空左折疊依原運算順序將首項併入初值".into() }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Première étape du pli gauche".into(), message: "Un pli gauche non vide incorpore son premier terme à la valeur initiale en préservant l'ordre des opérandes".into() }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Первый шаг левой свёртки".into(), message: "Непустая левая свёртка включает первый член в начальное значение, сохраняя порядок операндов".into() }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Primer paso del pliegue izquierdo".into(), message: "Un pliegue izquierdo no vacío incorpora el primer término a la semilla conservando el orden de operandos".into() }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "الخطوة الأولى للطي الأيسر".into(), message: "الطي الأيسر غير الخالي يدمج الحد الأول في القيمة الابتدائية مع حفظ ترتيب المعاملات".into() }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "左畳み込みの最初のステップ".into(), message: "空でない左畳み込みは被演算子の順序を保ち、最初の項を初期値に組み込みます".into() }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "왼쪽 접기의 첫 단계".into(), message: "비어 있지 않은 왼쪽 접기는 피연산자 순서를 유지하며 첫 항을 초깃값에 합칩니다".into() }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Bước đầu của phép gấp trái".into(), message: "Phép gấp trái không rỗng gộp hạng đầu vào giá trị khởi tạo, giữ thứ tự toán hạng".into() }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_translation::ReduceTranslationProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Order-preserving fold translation".into(), message: "Translate both integer endpoints equally and check the corresponding terms without changing operation or seed".into() }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "有序折叠的索引平移" .into(), message: "两个整数端点平移同样的量，检查对应项并保持运算和初值一致" .into() }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "有序折疊的索引平移".into(), message: "兩整數端點平移同樣的量，檢查對應項並保持運算和初值一致".into() }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Translation de pli préservant l'ordre".into(), message: "Translater les deux extrémités entières de la même quantité et vérifier les termes correspondants sans changer l'opération ni la valeur initiale".into() }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Сдвиг свёртки с сохранением порядка".into(), message: "Сдвинуть обе целочисленные границы одинаково и проверить соответствующие члены без изменения операции и начального значения".into() }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Traslación del pliegue conservando el orden".into(), message: "Trasladar ambos extremos enteros por igual y comprobar los términos correspondientes sin cambiar la operación ni la semilla".into() }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "إزاحة الطي مع حفظ الترتيب".into(), message: "إزاحة الطرفين الصحيحين بالمقدار نفسه وفحص الحدود المقابلة دون تغيير العملية أو القيمة الابتدائية".into() }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "順序を保つ畳み込みの平行移動".into(), message: "両方の整数端点を等しく移動し、演算と初期値を変えずに対応する項を検査します".into() }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "순서를 보존하는 접기 이동".into(), message: "두 정수 끝점을 같은 만큼 이동하고 연산과 초깃값을 바꾸지 않고 대응하는 항을 검사합니다".into() }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Tịnh tiến phép gấp bảo toàn thứ tự".into(), message: "Tịnh tiến hai đầu mút nguyên cùng lượng và kiểm tra các hạng tương ứng mà không đổi phép toán hay giá trị khởi tạo".into() }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_pointwise::ReducePointwiseProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Pointwise fold congruence".into(), message: "Use a checked pointwise proposition over the same interval, operation and seed".into() }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "有序折叠的逐点相等" .into(), message: "引用已验证的逐点相等命题，保持区间、运算和初值一致" .into() }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "有序折疊的逐點相等".into(), message: "引用已驗證的逐點命題，保持區間、運算和初值一致".into() }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Congruence ponctuelle du pli".into(), message: "Utiliser une proposition ponctuelle vérifiée sur le même intervalle avec la même opération et valeur initiale".into() }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Поточечная конгруэнтность свёртки".into(), message: "Использовать проверенное поточечное утверждение на том же интервале с той же операцией и начальным значением".into() }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Congruencia puntual del pliegue".into(), message: "Usar una proposición puntual comprobada sobre el mismo intervalo, operación y semilla".into() }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "تطابق الطي نقطة بنقطة".into(), message: "استخدام قضية نقطة بنقطة متحقق منها على الفترة والعملية والقيمة الابتدائية نفسها".into() }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "畳み込みの各点での合同性".into(), message: "同じ区間、演算、初期値に対する検証済みの各点の命題を用います".into() }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "접기의 점별 합동".into(), message: "같은 구간, 연산, 초깃값에 대한 검증된 점별 명제를 사용합니다".into() }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText { rule_name: "Tương hợp từng điểm của phép gấp".into(), message: "Dùng mệnh đề từng điểm đã kiểm tra trên cùng khoảng, phép toán và giá trị khởi tạo".into() }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_en(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_en(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "Remove a member from a finite product".into(),
                message: "Check membership, the restricted callback and the removed factor; no division or nonzero premise is needed".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "Fresh insertion into a finite product".into(),
                message: "Checked freshness, agreement of the restricted callback, and the inserted factor".into(),
            },
_ => {
                let (name, message) = ("Finite aggregate identity", "Verified constant, linear, pointwise, partition or reindexing requirements");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_zh(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_zh(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "有限乘积删除已有元素" .into(),
                message: "检查成员关系、限制回调和被删除因子；乘法拆分无需除法或非零前提" .into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "有限乘积插入新元素" .into(),
                message: "已验证元素不在原集合中、限制回调逐点一致及插入因子相等" .into(),
            },
_ => {
                let (name, message) = ("有限聚合恒等式", "已验证常量、线性、逐点相等、分拆或重编号所需的前提");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_zh_hant(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_zh_hant(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "有限乘積刪除已有元素".into(),
                message: "檢查成員關係、限制回呼和被刪除因子；無需除法或非零前提".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "有限乘積插入新元素".into(),
                message: "已驗證元素不在原集合中、限制回呼一致及插入因子".into(),
            },
_ => {
                let (name, message) = ("有限聚合恆等式", "已驗證常量、線性、逐點相等、分段或重編號所需條件");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_fr(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_fr(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "Retrait d'un membre d'un produit fini".into(),
                message: "Vérifier l'appartenance, la fonction restreinte et le facteur retiré ; aucune division ni prémisse de non-nullité n'est nécessaire".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "Insertion nouvelle dans un produit fini".into(),
                message: "Absence initiale vérifiée, concordance de la fonction restreinte et du facteur inséré".into(),
            },
_ => {
                let (name, message) = ("Identité d'agrégat fini", "Conditions vérifiées de constante, linéarité, égalité ponctuelle, partition ou réindexation");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_ru(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_ru(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "Удаление элемента из конечного произведения".into(),
                message: "Проверить принадлежность, ограниченную функцию и удалённый множитель; деление и предпосылка ненулевого значения не нужны".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "Вставка нового элемента в конечное произведение".into(),
                message: "Проверено отсутствие элемента, совпадение ограниченной функции и вставленного множителя".into(),
            },
_ => {
                let (name, message) = ("Тождество конечного агрегата", "Проверены условия константы, линейности, поточечного равенства, разбиения или переиндексации");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_es(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_es(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "Retirada de un miembro de producto finito".into(),
                message: "Comprobar pertenencia, función restringida y factor retirado; no se necesita división ni premisa de no nulidad".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "Inserción nueva en producto finito".into(),
                message: "Ausencia inicial comprobada, concordancia de función restringida y factor insertado".into(),
            },
_ => {
                let (name, message) = ("Identidad de agregado finito", "Requisitos comprobados de constante, linealidad, igualdad puntual, partición o reindexación");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_ar(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_ar(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "حذف عنصر من حاصل ضرب منتهٍ".into(),
                message: "فحص الانتماء والدالة المقيدة والعامل المحذوف؛ لا تلزم قسمة أو مقدمة عدم الصفر".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "إدراج عنصر جديد في حاصل ضرب منتهٍ".into(),
                message: "تم التحقق من جدة العنصر وتوافق الدالة المقيدة والعامل المدرج".into(),
            },
_ => {
                let (name, message) = ("هوية تجميع منتهٍ", "تم التحقق من متطلبات الثابت أو الخطية أو التساوي نقطة بنقطة أو التقسيم أو إعادة الفهرسة");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_ja(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_ja(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "有限積からの要素の削除".into(),
                message: "所属、制限した関数、削除する因子を検査します。除算や非ゼロの前提は不要です".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "有限積への新しい要素の挿入".into(),
                message: "要素の新規性、制限した関数と挿入因子の一致を検査しました".into(),
            },
_ => {
                let (name, message) = ("有限集約の恒等式", "定数、線形性、各点の一致、分割または添字変更の条件を検証しました");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_ko(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_ko(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "유한 곱에서 원소 제거".into(),
                message: "소속, 제한된 함수, 제거된 인자를 검사하며 나눗셈이나 0이 아님 전제는 필요하지 않습니다".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "유한 곱에 새 원소 삽입".into(),
                message: "원소의 신규성, 제한된 함수의 일치와 삽입된 인자를 검사했습니다".into(),
            },
_ => {
                let (name, message) = ("유한 집계 항등식", "상수, 선형성, 점별 일치, 분할 또는 재인덱싱 요건을 검증했습니다");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
match self {
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p) => p.rule_name_and_message_vi(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(p) => p.rule_name_and_message_vi(),
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(_) => BuiltinRuleText {
                rule_name: "Loại phần tử khỏi tích hữu hạn".into(),
                message: "Kiểm tra sự thuộc về, hàm hạn chế và thừa số bị loại; không cần chia hay tiền đề khác không".into(),
            },
crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::aggregate_identity_builtin_rule_proof::AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(_) => BuiltinRuleText {
                rule_name: "Chèn phần tử mới vào tích hữu hạn".into(),
                message: "Đã kiểm tra tính mới, sự khớp của hàm hạn chế và thừa số được chèn".into(),
            },
_ => {
                let (name, message) = ("Đồng nhất thức tổng hợp hữu hạn", "Đã kiểm tra điều kiện hằng, tuyến tính, từng điểm, phân hoạch hoặc đổi chỉ số");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
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
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_cartesian_size::CartesianSizeProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Finite Cartesian cardinality".into(),
                message: "The cardinality of a Cartesian product is the product of the checked finite factor cardinalities".into(),
            }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "有限笛卡尔积的基数" .into(),
                message: "笛卡尔积的基数等于各个已验证有限因子的基数乘积" .into(),
            }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "有限笛卡兒積的基數".into(),
                message: "笛卡兒積的基數等於已驗證的有限因子基數之乘積".into(),
            }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Cardinal du produit cartésien fini".into(),
                message: "Le cardinal d'un produit cartésien est le produit des cardinaux vérifiés de ses facteurs finis".into(),
            }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Мощность конечного декартова произведения".into(),
                message: "Мощность декартова произведения равна произведению проверенных мощностей конечных множителей".into(),
            }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Cardinalidad cartesiana finita".into(),
                message: "La cardinalidad del producto cartesiano es el producto de las cardinalidades comprobadas de sus factores finitos".into(),
            }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "عدد عناصر حاصل الضرب الديكارتي المنتهي".into(),
                message: "عدد عناصر حاصل الضرب الديكارتي يساوي حاصل ضرب أعداد عناصر العوامل المنتهية المتحقق منها".into(),
            }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "有限直積の濃度".into(),
                message: "直積の濃度は検証済みの有限因子の濃度の積です".into(),
            }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "유한 데카르트 곱의 기수".into(),
                message: "데카르트 곱의 기수는 검증된 유한 인자 기수의 곱입니다".into(),
            }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Lực lượng tích Descartes hữu hạn".into(),
                message: "Lực lượng tích Descartes là tích các lực lượng của thừa số hữu hạn đã kiểm tra".into(),
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
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_partition::ReducePartitionProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Adjacent left-fold partition".into(),
                message: "Continue the same left fold from the first segment's result, with checked adjacent bounds and matching functions, operation and seed".into(),
            }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "左折叠的相邻分段" .into(),
                message: "检查相邻边界及一致的函数、运算和初值后，从第一段结果继续同一个左折叠" .into(),
            }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "左折疊的相鄰分段".into(),
                message: "檢查相鄰邊界及一致的函數、運算和初值後，從首段結果繼續同一左折疊".into(),
            }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Partition adjacente du pli gauche".into(),
                message: "Continuer le même pli gauche depuis le résultat du premier segment, avec des bornes adjacentes vérifiées et des fonctions, opération et valeur initiale concordantes".into(),
            }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Разбиение левой свёртки на соседние части".into(),
                message: "Продолжить ту же левую свёртку из результата первого отрезка при проверенных соседних границах и совпадающих функциях, операции и начальном значении".into(),
            }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Partición adyacente del pliegue izquierdo".into(),
                message: "Continuar el mismo pliegue izquierdo desde el resultado del primer segmento con límites adyacentes comprobados y funciones, operación y semilla coincidentes".into(),
            }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "تقسيم متجاور للطي الأيسر".into(),
                message: "متابعة الطي الأيسر نفسه من نتيجة الجزء الأول بحدود متجاورة متحقق منها ودوال وعملية وقيمة ابتدائية متطابقة".into(),
            }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "左畳み込みの隣接分割".into(),
                message: "隣接する境界と関数、演算、初期値の一致を検査し、最初の区間の結果から同じ左畳み込みを続けます".into(),
            }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "왼쪽 접기의 인접 분할".into(),
                message: "인접 경계와 함수, 연산, 초깃값의 일치를 검사하고 첫 구간 결과에서 같은 왼쪽 접기를 이어갑니다".into(),
            }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name: "Phân hoạch kề nhau của phép gấp trái".into(),
                message: "Tiếp tục cùng phép gấp trái từ kết quả đoạn đầu, với biên kề đã kiểm tra và hàm, phép toán, giá trị khởi tạo khớp nhau".into(),
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
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_last_step::ReduceLastStepProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Last fold step".into(),message:"The nonempty left fold applies its operation to the preceding fold and final term".into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"折叠的末端一步".into(),message:"非空左折叠将运算应用于前段折叠结果和最后一项".into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"折疊的末端一步".into(),message:"非空左折疊將運算套用於前段折疊結果與最後一項".into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Dernière étape du pli".into(),message:"Le pli gauche non vide applique son opération au pli précédent et au dernier terme".into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Последний шаг свёртки".into(),message:"Непустая левая свёртка применяет операцию к предыдущей свёртке и последнему члену".into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Último paso del pliegue".into(),message:"El pliegue izquierdo no vacío aplica su operación al pliegue anterior y al último término".into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"الخطوة الأخيرة للطي".into(),message:"الطي الأيسر غير الخالي يطبق عمليته على الطي السابق والحد الأخير".into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"畳み込みの最後のステップ".into(),message:"空でない左畳み込みは前の畳み込みと最後の項に演算を適用します".into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"접기의 마지막 단계".into(),message:"비어 있지 않은 왼쪽 접기는 이전 접기 결과와 마지막 항에 연산을 적용합니다".into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Bước cuối của phép gấp".into(),message:"Phép gấp trái không rỗng áp dụng phép toán cho phép gấp trước và hạng cuối".into()}
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_map_size::FiniteMapSizeProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Finite map cardinality".into(),message:"Consume the stored bijection or injection certificate to compare finite cardinalities".into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"有限映射的基数".into(),message:"消费已存双射或单射证书比较有限基数".into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"有限映射的基數".into(),message:"使用已儲存的雙射或單射證書比較有限基數".into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Cardinalité d'application finie".into(),message:"Utiliser le certificat stocké de bijection ou d'injection pour comparer les cardinaux finis".into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Мощность конечного отображения".into(),message:"Использовать сохранённый сертификат биекции или инъекции для сравнения конечных мощностей".into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Cardinalidad de aplicación finita".into(),message:"Usar el certificado almacenado de biyección o inyección para comparar cardinalidades finitas".into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"عدد عناصر تطبيق منتهٍ".into(),message:"استخدام شهادة التقابل أو الحقن المخزنة لمقارنة أعداد العناصر المنتهية".into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"有限写像の濃度".into(),message:"保存済みの全単射または単射の証明書で有限濃度を比較します".into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"유한 사상의 기수".into(),message:"저장된 전단사 또는 단사 인증서로 유한 기수를 비교합니다".into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Lực lượng ánh xạ hữu hạn".into(),message:"Dùng chứng nhận song ánh hoặc đơn ánh đã lưu để so sánh lực lượng hữu hạn".into()}
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_product::ReduceProductBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Multiplication fold".into(),message:"A multiplication fold with seed one equals the product over the same interval".into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"乘法折叠".into(),message:"初值为一的乘法折叠等于相同区间上的乘积".into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"乘法折疊".into(),message:"初值為一的乘法折疊等於同區間上的乘積".into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Pli multiplicatif".into(),message:"Un pli multiplicatif de valeur initiale un est égal au produit sur le même intervalle".into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Мультипликативная свёртка".into(),message:"Мультипликативная свёртка с начальным значением один равна произведению на том же интервале".into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Pliegue multiplicativo".into(),message:"Un pliegue multiplicativo con semilla uno equivale al producto sobre el mismo intervalo".into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"طي ضربي".into(),message:"الطي الضربي بقيمة ابتدائية واحد يساوي حاصل الضرب على الفترة نفسها".into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"乗法の畳み込み".into(),message:"初期値が一の乗法の畳み込みは同じ区間の積に等しいです".into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"곱셈 접기".into(),message:"초깃값이 1인 곱셈 접기는 같은 구간의 곱과 같습니다".into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Phép gấp nhân".into(),message:"Phép gấp nhân với giá trị khởi tạo một bằng tích trên cùng khoảng".into()}
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"Elementary arithmetic identity".into(),
                message:"Apply the arithmetic identity with checked domains and stored premises".into(),
            }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"基本算术恒等式".into(),
                message:"依据已验证的定义域和已存前提应用算术恒等式".into(),
            }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"基本算術恆等式".into(),
                message:"依已驗證的定義域和已儲存前提套用算術恆等式".into(),
            }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"Identité arithmétique élémentaire".into(),
                message:"Appliquer l'identité arithmétique avec les domaines vérifiés et les prémisses stockées".into(),
            }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"Элементарное арифметическое тождество".into(),
                message:"Применить арифметическое тождество с проверенными областями и сохранёнными предпосылками".into(),
            }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"Identidad aritmética elemental".into(),
                message:"Aplicar la identidad aritmética con dominios comprobados y premisas almacenadas".into(),
            }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"هوية حسابية أولية".into(),
                message:"تطبيق الهوية الحسابية بالمجالات المتحقق منها والمقدمات المخزنة".into(),
            }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"基本的な算術恒等式".into(),
                message:"検証済みの定義域と保存済みの前提で算術恒等式を適用します".into(),
            }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"기본 산술 항등식".into(),
                message:"검증된 정의역과 저장된 전제로 산술 항등식을 적용합니다".into(),
            }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {
                rule_name:"Đồng nhất thức số học cơ bản".into(),
                message:"Áp dụng đồng nhất thức số học với miền đã kiểm tra và tiền đề đã lưu".into(),
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
}

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_integer_range_builder::IntegerRangeBuilderBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Integer range comprehension".into(),message:"Integer membership with the exact lower and upper endpoint conditions".into()}
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"整数区间的集合内包表示" .into(),message:"整数成员及对应的上下界条件".into()}
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"整數區間集合構造".into(),message:"整數成員及精確上下端點條件".into()}
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Compréhension d'intervalle entier".into(),message:"Appartenance entière avec les conditions exactes aux bornes inférieure et supérieure".into()}
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Целочисленное множество по интервалу".into(),message:"Целочисленная принадлежность с точными условиями нижней и верхней границ".into()}
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Comprensión de intervalo entero".into(),message:"Pertenencia entera con las condiciones exactas de los extremos inferior y superior".into()}
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"بناء مجموعة فترة صحيحة".into(),message:"انتماء صحيح مع شروط الطرفين الأدنى والأعلى الدقيقة".into()}
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"整数区間の内包表記".into(),message:"正確な下端と上端の条件を伴う整数の所属".into()}
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"정수 구간 조건제시".into(),message:"정확한 하한과 상한 끝점 조건을 포함한 정수 소속".into()}
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
BuiltinRuleText {rule_name:"Tập dựng khoảng nguyên".into(),message:"Thuộc về số nguyên với điều kiện chính xác của đầu mút dưới và trên".into()}
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_by_aggregate_calculation::AggregateCalculationBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
                let (name, message) = ("Exact finite aggregate calculation", "Enumerate valid arguments, substitute checked function bodies and fold exact values");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
                let (name, message) = ("有限聚合精确计算", "枚举合法指标，代入已检查的函数体，并精确累加或累乘");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
                let (name, message) = ("有限聚合精確計算", "列舉合法引數，代入已檢查的函數體並精確折疊數值");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
                let (name, message) = ("Calcul exact d'agrégat fini", "Énumérer les arguments valides, substituer les corps de fonctions vérifiés et plier les valeurs exactes");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
                let (name, message) = ("Точное вычисление конечного агрегата", "Перебрать допустимые аргументы, подставить проверенные тела функций и свернуть точные значения");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
                let (name, message) = ("Cálculo exacto de agregado finito", "Enumerar argumentos válidos, sustituir cuerpos de función comprobados y plegar valores exactos");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
                let (name, message) = ("حساب دقيق لتجميع منتهٍ", "تعداد الوسائط الصالحة وتعويض متون الدوال المتحقق منها وطي القيم الدقيقة");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
                let (name, message) = ("有限集約の正確な計算", "有効な引数を列挙し、検査済みの関数本体を代入して正確な値を畳み込みます");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
                let (name, message) = ("유한 집계의 정확한 계산", "유효한 인수를 열거하고 검사된 함수 본문을 대입하여 정확한 값을 접습니다");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
                let (name, message) = ("Tính toán chính xác tổng hợp hữu hạn", "Liệt kê đối số hợp lệ, thế thân hàm đã kiểm tra và gấp các giá trị chính xác");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_function_domain_image::FnRangeOfEmptyDomainBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("image of empty-domain function", "A function with an empty complete domain has empty image")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空域函数的像", "完整定义域为空的函数，其像为空集")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空域函數的像", "完整定義域為空的函數，其像為空集")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Image sur un domaine vide", "Une fonction dont le domaine complet est vide a une image vide")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Образ функции на пустой области", "Функция с пустой полной областью определения имеет пустой образ")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Imagen de una función de dominio vacío", "Una función con dominio completo vacío tiene imagen vacía")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("صورة دالة ذات مجال فارغ", "الدالة ذات مجال التعريف الكامل الفارغ صورتها فارغة")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空の定義域を持つ関数の像", "完全な定義域が空の関数の像は空集合です")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("정의역이 빈 함수의 상", "전체 정의역이 빈 함수의 상은 공집합입니다")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Ảnh của hàm có miền rỗng", "Hàm có miền xác định đầy đủ rỗng có ảnh rỗng")
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyFunctionGraphBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Empty function graph", "A function with an empty complete domain is the empty graph")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空函数图", "完整定义域为空的函数等于空函数图")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空函數圖", "完整定義域為空的函數等於空函數圖")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Graphe de fonction vide", "Une fonction dont le domaine complet est vide est le graphe vide")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Пустой график функции", "Функция с пустой полной областью определения имеет пустой график")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Grafo de función vacío", "Una función con dominio completo vacío es el grafo vacío")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("رسم دالة فارغ", "الدالة ذات مجال التعريف الكامل الفارغ هي الرسم الفارغ")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空の関数グラフ", "完全な定義域が空の関数は空のグラフです")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("빈 함수 그래프", "전체 정의역이 빈 함수는 빈 그래프입니다")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Đồ thị hàm rỗng", "Hàm có miền xác định đầy đủ rỗng là đồ thị rỗng")
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

impl crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyDomainFunctionSpaceSingletonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Singleton empty-domain function space", "An empty-domain function space contains exactly the empty function")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("空域函数空间的单例", "完整定义域为空的函数空间恰好包含一个空函数")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("空域函數空間的單例", "完整定義域為空的函數空間恰好包含一個空函數")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Espace de fonctions sur un domaine vide", "Un espace de fonctions sur un domaine vide contient exactement la fonction vide")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Одноэлементное пространство функций", "Пространство функций на пустой области содержит только пустую функцию")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Espacio de funciones de dominio vacío", "Un espacio de funciones de dominio vacío contiene exactamente la función vacía")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("فضاء دوال ذي مجال فارغ", "فضاء الدوال ذي المجال الفارغ يحتوي على الدالة الفارغة وحدها")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("空の定義域上の関数空間", "空の定義域上の関数空間は空関数だけを含みます")
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("빈 정의역의 함수 공간", "빈 정의역의 함수 공간은 빈 함수 하나만 포함합니다")
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Không gian hàm trên miền rỗng", "Không gian hàm trên miền rỗng chỉ chứa hàm rỗng")
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
