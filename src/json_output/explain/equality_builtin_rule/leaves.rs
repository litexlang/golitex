//! Leaf proof structs: rule_id_and_message_en / _zh / (lang).

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
    CartProjFactorBuiltinRuleProof, ClosedRangeSingletonListSetBuiltinRuleProof,
    EmptySetFromSizeZeroBuiltinRuleProof, FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof,
    FiniteSetSizeSetMinusBuiltinRuleProof, FiniteSetSizeUnionBuiltinRuleProof,
    PowOfLogInverseBuiltinRuleProof, ProductSingleTermBuiltinRuleProof,
    ReduceAddZeroEqualsSumBuiltinRuleProof, SetMinusRecoversSubsetBuiltinRuleProof,
    SumSingleTermBuiltinRuleProof, TupleComponentAtIndexBuiltinRuleProof,
    UnionAbsorptionFromSubsetBuiltinRuleProof
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
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl SinArcsinLeftInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SinArcsinLeftInverse",
            "sin ∘ arcsin",
            "sin(arcsin(x)) = x on the arcsin range",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SinArcsinLeftInverse",
            "sin ∘ arcsin",
            "在 arcsin 值域上，sin(arcsin(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x（在 arcsin 值域上）",
            ),
            OutputLanguage::French => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x sur l'image de arcsin",
            ),
            OutputLanguage::Russian => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x на области значений arcsin",
            ),
            OutputLanguage::Spanish => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x en el rango de arcsin",
            ),
            OutputLanguage::Arabic => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x على مدى arcsin",
            ),
            OutputLanguage::Japanese => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x（arcsin の値域上）",
            ),
            OutputLanguage::Korean => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x(arcsin 치역에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "SinArcsinLeftInverse",
                "sin ∘ arcsin",
                "sin(arcsin(x)) = x trên miền giá trị arcsin",
            ),
        }
    }
}

impl CosArccosLeftInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CosArccosLeftInverse",
            "cos ∘ arccos",
            "cos(arccos(x)) = x on the arccos range",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CosArccosLeftInverse",
            "cos ∘ arccos",
            "在 arccos 值域上，cos(arccos(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x（在 arccos 值域上）",
            ),
            OutputLanguage::French => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x sur l'image de arccos",
            ),
            OutputLanguage::Russian => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x на области значений arccos",
            ),
            OutputLanguage::Spanish => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x en el rango de arccos",
            ),
            OutputLanguage::Arabic => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x على مدى arccos",
            ),
            OutputLanguage::Japanese => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x（arccos の値域上）",
            ),
            OutputLanguage::Korean => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x(arccos 치역에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "CosArccosLeftInverse",
                "cos ∘ arccos",
                "cos(arccos(x)) = x trên miền giá trị arccos",
            ),
        }
    }
}

impl TanArctanLeftInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::French => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Russian => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Spanish => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Arabic => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Japanese => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Korean => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
            OutputLanguage::Vietnamese => {
                text("TanArctanLeftInverse", "tan ∘ arctan", "tan(arctan(x)) = x")
            }
        }
    }
}

impl CotArccotLeftInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::French => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Russian => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Spanish => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Arabic => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Japanese => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Korean => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
            OutputLanguage::Vietnamese => {
                text("CotArccotLeftInverse", "cot ∘ arccot", "cot(arccot(x)) = x")
            }
        }
    }
}

impl ArcsinSinRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArcsinSinRightInverse",
            "arcsin ∘ sin",
            "arcsin(sin(x)) = x on the principal interval",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArcsinSinRightInverse",
            "arcsin ∘ sin",
            "在主值区间上，arcsin(sin(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x（在主值區間上）",
            ),
            OutputLanguage::French => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x sur l'intervalle principal",
            ),
            OutputLanguage::Russian => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x на главном интервале",
            ),
            OutputLanguage::Spanish => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x en el intervalo principal",
            ),
            OutputLanguage::Arabic => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x على الفترة الرئيسية",
            ),
            OutputLanguage::Japanese => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x（主値区間上）",
            ),
            OutputLanguage::Korean => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x(주값 구간에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "ArcsinSinRightInverse",
                "arcsin ∘ sin",
                "arcsin(sin(x)) = x trên khoảng chính",
            ),
        }
    }
}

impl ArccosCosRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccosCosRightInverse",
            "arccos ∘ cos",
            "arccos(cos(x)) = x on the principal interval",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccosCosRightInverse",
            "arccos ∘ cos",
            "在主值区间上，arccos(cos(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x（在主值區間上）",
            ),
            OutputLanguage::French => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x sur l'intervalle principal",
            ),
            OutputLanguage::Russian => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x на главном интервале",
            ),
            OutputLanguage::Spanish => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x en el intervalo principal",
            ),
            OutputLanguage::Arabic => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x على الفترة الرئيسية",
            ),
            OutputLanguage::Japanese => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x（主値区間上）",
            ),
            OutputLanguage::Korean => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x(주값 구간에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccosCosRightInverse",
                "arccos ∘ cos",
                "arccos(cos(x)) = x trên khoảng chính",
            ),
        }
    }
}

impl ArctanTanRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArctanTanRightInverse",
            "arctan ∘ tan",
            "arctan(tan(x)) = x on the principal interval",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArctanTanRightInverse",
            "arctan ∘ tan",
            "在主值区间上，arctan(tan(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x（在主值區間上）",
            ),
            OutputLanguage::French => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x sur l'intervalle principal",
            ),
            OutputLanguage::Russian => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x на главном интервале",
            ),
            OutputLanguage::Spanish => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x en el intervalo principal",
            ),
            OutputLanguage::Arabic => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x على الفترة الرئيسية",
            ),
            OutputLanguage::Japanese => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x（主値区間上）",
            ),
            OutputLanguage::Korean => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x(주값 구간에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "ArctanTanRightInverse",
                "arctan ∘ tan",
                "arctan(tan(x)) = x trên khoảng chính",
            ),
        }
    }
}

impl ArccotCotRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccotCotRightInverse",
            "arccot ∘ cot",
            "arccot(cot(x)) = x on the principal interval",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccotCotRightInverse",
            "arccot ∘ cot",
            "在主值区间上，arccot(cot(x)) = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x（在主值區間上）",
            ),
            OutputLanguage::French => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x sur l'intervalle principal",
            ),
            OutputLanguage::Russian => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x на главном интервале",
            ),
            OutputLanguage::Spanish => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x en el intervalo principal",
            ),
            OutputLanguage::Arabic => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x على الفترة الرئيسية",
            ),
            OutputLanguage::Japanese => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x（主値区間上）",
            ),
            OutputLanguage::Korean => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x(주값 구간에서)",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccotCotRightInverse",
                "arccot ∘ cot",
                "arccot(cot(x)) = x trên khoảng chính",
            ),
        }
    }
}

impl ArcsinExactZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0")
            }
            OutputLanguage::French => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Russian => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Spanish => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Arabic => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Japanese => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Korean => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
            OutputLanguage::Vietnamese => text("ArcsinExactZero", "arcsin 0", "arcsin(0) = 0"),
        }
    }
}

impl ArcsinExactOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2")
            }
            OutputLanguage::French => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Russian => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Spanish => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Arabic => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Japanese => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Korean => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
            OutputLanguage::Vietnamese => text("ArcsinExactOne", "arcsin 1", "arcsin(1) = π/2"),
        }
    }
}

impl ArcsinExactNegOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2")
            }
            OutputLanguage::French => text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2"),
            OutputLanguage::Russian => text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2"),
            OutputLanguage::Spanish => text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2"),
            OutputLanguage::Arabic => text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2"),
            OutputLanguage::Japanese => {
                text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2")
            }
            OutputLanguage::Korean => text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2"),
            OutputLanguage::Vietnamese => {
                text("ArcsinExactNegOne", "arcsin(-1)", "arcsin(-1) = -π/2")
            }
        }
    }
}

impl ArccosExactOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccosExactOne", "arccos 1", "arccos(1) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccosExactOne", "arccos 1", "arccos(1) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArccosExactOne", "arccos 1", "arccos(1) = 0")
            }
            OutputLanguage::French => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Russian => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Spanish => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Arabic => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Japanese => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Korean => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
            OutputLanguage::Vietnamese => text("ArccosExactOne", "arccos 1", "arccos(1) = 0"),
        }
    }
}

impl ArccosExactZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccosExactZero", "arccos 0", "arccos(0) = π/2")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccosExactZero", "arccos 0", "arccos(0) = π/2")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArccosExactZero", "arccos 0", "arccos(0) = π/2")
            }
            OutputLanguage::French => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Russian => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Spanish => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Arabic => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Japanese => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Korean => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
            OutputLanguage::Vietnamese => text("ArccosExactZero", "arccos 0", "arccos(0) = π/2"),
        }
    }
}

impl ArccosExactNegOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π")
            }
            OutputLanguage::French => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Russian => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Spanish => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Arabic => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Japanese => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Korean => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
            OutputLanguage::Vietnamese => text("ArccosExactNegOne", "arccos(-1)", "arccos(-1) = π"),
        }
    }
}

impl ArctanExactZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArctanExactZero", "arctan 0", "arctan(0) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArctanExactZero", "arctan 0", "arctan(0) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArctanExactZero", "arctan 0", "arctan(0) = 0")
            }
            OutputLanguage::French => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Russian => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Spanish => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Arabic => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Japanese => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Korean => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
            OutputLanguage::Vietnamese => text("ArctanExactZero", "arctan 0", "arctan(0) = 0"),
        }
    }
}

impl ArccotExactZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccotExactZero", "arccot 0", "arccot(0) = π/2")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccotExactZero", "arccot 0", "arccot(0) = π/2")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ArccotExactZero", "arccot 0", "arccot(0) = π/2")
            }
            OutputLanguage::French => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Russian => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Spanish => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Arabic => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Japanese => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Korean => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
            OutputLanguage::Vietnamese => text("ArccotExactZero", "arccot 0", "arccot(0) = π/2"),
        }
    }
}

impl PowerProductSameBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::French => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Russian => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Spanish => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Arabic => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Japanese => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Korean => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
            OutputLanguage::Vietnamese => {
                text("PowerProductSameBase", "a^m · a^n", "a^m · a^n = a^(m+n)")
            }
        }
    }
}

impl PowerOfPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)")
            }
            OutputLanguage::French => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Russian => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Spanish => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Arabic => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Japanese => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Korean => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
            OutputLanguage::Vietnamese => text("PowerOfPower", "(a^m)^n", "(a^m)^n = a^(m·n)"),
        }
    }
}

impl PowerOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n")
            }
            OutputLanguage::French => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Russian => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Spanish => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Arabic => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Japanese => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Korean => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
            OutputLanguage::Vietnamese => text("PowerOfProduct", "(a·b)^n", "(a·b)^n = a^n · b^n"),
        }
    }
}

impl ReciprocalAsNegOnePowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReciprocalAsNegOnePower", "1/a as a^(-1)", "1/a = a^(-1)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReciprocalAsNegOnePower", "1/a 即 a^(-1)", "1/a = a^(-1)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::French => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Russian => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Spanish => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Arabic => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Japanese => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Korean => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
            OutputLanguage::Vietnamese => {
                text("ReciprocalAsNegOnePower", "1/a = a^(-1)", "1/a = a^(-1)")
            }
        }
    }
}

impl QuotientAsMulNegOnePowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "QuotientAsMulNegOnePower",
            "a/b as a·b^(-1)",
            "a/b = a · b^(-1)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "QuotientAsMulNegOnePower",
            "a/b 即 a·b^(-1)",
            "a/b = a · b^(-1)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::French => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Russian => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Spanish => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Arabic => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Japanese => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Korean => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
            OutputLanguage::Vietnamese => text(
                "QuotientAsMulNegOnePower",
                "a/b = a·b^(-1)",
                "a/b = a · b^(-1)",
            ),
        }
    }
}

impl OneToAnyPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("OneToAnyPower", "1^n", "1^n = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("OneToAnyPower", "1^n", "1^n = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::French => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Russian => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Spanish => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Arabic => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Japanese => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Korean => text("OneToAnyPower", "1^n", "1^n = 1"),
            OutputLanguage::Vietnamese => text("OneToAnyPower", "1^n", "1^n = 1"),
        }
    }
}

impl ZeroToPosNatPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ZeroToPosNatPower",
            "0^n (n>0)",
            "0^n = 0 for positive natural n",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ZeroToPosNatPower", "0^n (n>0)", "对正自然数 n，0^n = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ZeroToPosNatPower", "0^n (n>0)", "0^n = 0（n 為正自然數）")
            }
            OutputLanguage::French => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0 pour n naturel positif",
            ),
            OutputLanguage::Russian => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0 для положительного натурального n",
            ),
            OutputLanguage::Spanish => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0 para n natural positivo",
            ),
            OutputLanguage::Arabic => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0 للعدد الطبيعي الموجب n",
            ),
            OutputLanguage::Japanese => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0（n は正の自然数）",
            ),
            OutputLanguage::Korean => {
                text("ZeroToPosNatPower", "0^n (n>0)", "0^n = 0(n은 양의 자연수)")
            }
            OutputLanguage::Vietnamese => text(
                "ZeroToPosNatPower",
                "0^n (n>0)",
                "0^n = 0 với n tự nhiên dương",
            ),
        }
    }
}

impl SqrtSquareBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtSquare",
            "√(a²)",
            "√(a²) relates to |a| / square-root of a square",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtSquare", "√(a²)", "√(a²) 与 |a| / 平方的平方根相关")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SqrtSquare", "√(a²)", "√(a²) 與 |a| 的關係：平方的平方根")
            }
            OutputLanguage::French => text(
                "SqrtSquare",
                "√(a²)",
                "Relation de √(a²) avec |a| : racine carrée d'un carré",
            ),
            OutputLanguage::Russian => text(
                "SqrtSquare",
                "√(a²)",
                "Связь √(a²) с |a|: квадратный корень квадрата",
            ),
            OutputLanguage::Spanish => text(
                "SqrtSquare",
                "√(a²)",
                "Relación de √(a²) con |a|: raíz cuadrada de un cuadrado",
            ),
            OutputLanguage::Arabic => {
                text("SqrtSquare", "√(a²)", "علاقة √(a²) بـ |a|: جذر تربيعي لمربع")
            }
            OutputLanguage::Japanese => {
                text("SqrtSquare", "√(a²)", "√(a²) と |a| の関係：平方の平方根")
            }
            OutputLanguage::Korean => {
                text("SqrtSquare", "√(a²)", "√(a²)와 |a|의 관계: 제곱의 제곱근")
            }
            OutputLanguage::Vietnamese => text(
                "SqrtSquare",
                "√(a²)",
                "Quan hệ của √(a²) với |a|: căn bậc hai của bình phương",
            ),
        }
    }
}

impl SqrtZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtZero", "√0", "√0 = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtZero", "√0", "√0 = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::French => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Russian => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Spanish => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Arabic => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Japanese => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Korean => text("SqrtZero", "√0", "√0 = 0"),
            OutputLanguage::Vietnamese => text("SqrtZero", "√0", "√0 = 0"),
        }
    }
}

impl SqrtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtOne", "√1", "√1 = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtOne", "√1", "√1 = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::French => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Russian => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Spanish => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Arabic => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Japanese => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Korean => text("SqrtOne", "√1", "√1 = 1"),
            OutputLanguage::Vietnamese => text("SqrtOne", "√1", "√1 = 1"),
        }
    }
}

impl SqrtOfSquareBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::French => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Russian => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Spanish => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Arabic => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Japanese => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Korean => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
            OutputLanguage::Vietnamese => text("SqrtOfSquare", "√(a·a)", "√(a·a) = |a|"),
        }
    }
}

impl SqrtProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtProduct", "√(a·b)", "√(a·b) = √a · √b (when defined)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtProduct", "√(a·b)", "有定义时 √(a·b) = √a · √b")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SqrtProduct", "√(a·b)", "√(a·b) = √a · √b（定義成立時）")
            }
            OutputLanguage::French => text("SqrtProduct", "√(a·b)", "√(a·b) = √a · √b (si défini)"),
            OutputLanguage::Russian => text(
                "SqrtProduct",
                "√(a·b)",
                "√(a·b) = √a · √b (когда определено)",
            ),
            OutputLanguage::Spanish => text(
                "SqrtProduct",
                "√(a·b)",
                "√(a·b) = √a · √b (si está definido)",
            ),
            OutputLanguage::Arabic => text(
                "SqrtProduct",
                "√(a·b)",
                "√(a·b) = √a · √b (عندما يكون معرّفًا)",
            ),
            OutputLanguage::Japanese => text(
                "SqrtProduct",
                "√(a·b)",
                "√(a·b) = √a · √b（定義されている場合）",
            ),
            OutputLanguage::Korean => text(
                "SqrtProduct",
                "√(a·b)",
                "√(a·b) = √a · √b(정의되어 있을 때)",
            ),
            OutputLanguage::Vietnamese => {
                text("SqrtProduct", "√(a·b)", "√(a·b) = √a · √b (khi xác định)")
            }
        }
    }
}

impl SqrtQuotientBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtQuotient", "√(a/b)", "√(a/b) = √a / √b (when defined)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtQuotient", "√(a/b)", "有定义时 √(a/b) = √a / √b")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SqrtQuotient", "√(a/b)", "√(a/b) = √a / √b（定義成立時）")
            }
            OutputLanguage::French => {
                text("SqrtQuotient", "√(a/b)", "√(a/b) = √a / √b (si défini)")
            }
            OutputLanguage::Russian => text(
                "SqrtQuotient",
                "√(a/b)",
                "√(a/b) = √a / √b (когда определено)",
            ),
            OutputLanguage::Spanish => text(
                "SqrtQuotient",
                "√(a/b)",
                "√(a/b) = √a / √b (si está definido)",
            ),
            OutputLanguage::Arabic => text(
                "SqrtQuotient",
                "√(a/b)",
                "√(a/b) = √a / √b (عندما يكون معرّفًا)",
            ),
            OutputLanguage::Japanese => text(
                "SqrtQuotient",
                "√(a/b)",
                "√(a/b) = √a / √b（定義されている場合）",
            ),
            OutputLanguage::Korean => text(
                "SqrtQuotient",
                "√(a/b)",
                "√(a/b) = √a / √b(정의되어 있을 때)",
            ),
            OutputLanguage::Vietnamese => {
                text("SqrtQuotient", "√(a/b)", "√(a/b) = √a / √b (khi xác định)")
            }
        }
    }
}

impl AbsOfNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsOfNegation", "|-a|", "|-a| = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsOfNegation", "|-a|", "|-a| = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::French => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Russian => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Spanish => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Arabic => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Japanese => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Korean => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
            OutputLanguage::Vietnamese => text("AbsOfNegation", "|-a|", "|-a| = |a|"),
        }
    }
}

impl AbsProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::French => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Russian => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Spanish => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Arabic => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Japanese => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Korean => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
            OutputLanguage::Vietnamese => text("AbsProduct", "|a·b|", "|a·b| = |a|·|b|"),
        }
    }
}

impl AbsSquareBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsSquare", "|a|²", "|a|² = a²")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsSquare", "|a|²", "|a|² = a²")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::French => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Russian => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Spanish => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Arabic => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Japanese => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Korean => text("AbsSquare", "|a|²", "|a|² = a²"),
            OutputLanguage::Vietnamese => text("AbsSquare", "|a|²", "|a|² = a²"),
        }
    }
}

impl LogBaseSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogBaseSelf", "log_a(a)", "log_a(a) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogBaseSelf", "log_a(a)", "log_a(a) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::French => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Russian => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Spanish => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Arabic => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Japanese => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Korean => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
            OutputLanguage::Vietnamese => text("LogBaseSelf", "log_a(a)", "log_a(a) = 1"),
        }
    }
}

impl LogOfOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogOfOne", "log_a(1)", "log_a(1) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogOfOne", "log_a(1)", "log_a(1) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::French => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Russian => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Spanish => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Arabic => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Japanese => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Korean => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
            OutputLanguage::Vietnamese => text("LogOfOne", "log_a(1)", "log_a(1) = 0"),
        }
    }
}

impl LogOfPowerSameBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n")
            }
            OutputLanguage::French => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Russian => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Spanish => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Arabic => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Japanese => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Korean => text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n"),
            OutputLanguage::Vietnamese => {
                text("LogOfPowerSameBase", "log_a(a^n)", "log_a(a^n) = n")
            }
        }
    }
}

impl LogArgPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::French => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Russian => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Spanish => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Arabic => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Japanese => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Korean => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
            OutputLanguage::Vietnamese => {
                text("LogArgPower", "log_a(b^n)", "log_a(b^n) = n · log_a(b)")
            }
        }
    }
}

impl LogProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogProduct",
            "log_a(b·c)",
            "log_a(b·c) = log_a(b) + log_a(c)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogProduct",
            "log_a(b·c)",
            "log_a(b·c) = log_a(b) + log_a(c)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::French => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Russian => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Spanish => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Arabic => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Japanese => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Korean => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
            OutputLanguage::Vietnamese => text(
                "LogProduct",
                "log_a(b·c)",
                "log_a(b·c) = log_a(b) + log_a(c)",
            ),
        }
    }
}

impl LogQuotientBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogQuotient",
            "log_a(b/c)",
            "log_a(b/c) = log_a(b) - log_a(c)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogQuotient",
            "log_a(b/c)",
            "log_a(b/c) = log_a(b) - log_a(c)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::French => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Russian => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Spanish => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Arabic => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Japanese => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Korean => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
            OutputLanguage::Vietnamese => text(
                "LogQuotient",
                "log_a(b/c)",
                "log_a(b/c) = log_a(b) - log_a(c)",
            ),
        }
    }
}

impl LogReciprocalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
            }
            OutputLanguage::French => text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)"),
            OutputLanguage::Russian => {
                text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
            }
            OutputLanguage::Spanish => {
                text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
            }
            OutputLanguage::Arabic => text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)"),
            OutputLanguage::Japanese => {
                text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
            }
            OutputLanguage::Korean => text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)"),
            OutputLanguage::Vietnamese => {
                text("LogReciprocal", "log_a(1/b)", "log_a(1/b) = -log_a(b)")
            }
        }
    }
}

impl LogChangeOfBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogChangeOfBase",
            "change of base",
            "log_a(b) = log_c(b) / log_c(a)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogChangeOfBase",
            "换底公式",
            "log_a(b) = log_c(b) / log_c(a)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogChangeOfBase",
                "換底公式",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::French => text(
                "LogChangeOfBase",
                "Changement de base",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Russian => text(
                "LogChangeOfBase",
                "Смена основания",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Spanish => text(
                "LogChangeOfBase",
                "Cambio de base",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Arabic => text(
                "LogChangeOfBase",
                "تغيير الأساس",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Japanese => text(
                "LogChangeOfBase",
                "底の変換",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Korean => text(
                "LogChangeOfBase",
                "밑 변환",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
            OutputLanguage::Vietnamese => text(
                "LogChangeOfBase",
                "Đổi cơ số",
                "log_a(b) = log_c(b) / log_c(a)",
            ),
        }
    }
}

impl ZeroModBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ZeroMod", "0 mod n", "0 mod n = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ZeroMod", "0 mod n", "0 mod n = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::French => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Russian => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Spanish => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Arabic => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Japanese => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Korean => text("ZeroMod", "0 mod n", "0 mod n = 0"),
            OutputLanguage::Vietnamese => text("ZeroMod", "0 mod n", "0 mod n = 0"),
        }
    }
}

impl ModOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ModOne", "a mod 1", "a mod 1 = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModOne", "a mod 1", "a mod 1 = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::French => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Russian => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Spanish => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Arabic => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Japanese => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Korean => text("ModOne", "a mod 1", "a mod 1 = 0"),
            OutputLanguage::Vietnamese => text("ModOne", "a mod 1", "a mod 1 = 0"),
        }
    }
}

impl OneModAtLeastTwoBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OneModAtLeastTwo",
            "1 mod n (n≥2)",
            "1 mod n = 1 when n ≥ 2",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OneModAtLeastTwo",
            "1 mod n (n≥2)",
            "当 n ≥ 2 时 1 mod n = 1",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "OneModAtLeastTwo",
                "1 mod n (n≥2)",
                "1 mod n = 1（n ≥ 2 時）",
            ),
            OutputLanguage::French => {
                text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 si n ≥ 2")
            }
            OutputLanguage::Russian => {
                text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 при n ≥ 2")
            }
            OutputLanguage::Spanish => {
                text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 si n ≥ 2")
            }
            OutputLanguage::Arabic => {
                text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 إذا n ≥ 2")
            }
            OutputLanguage::Japanese => text(
                "OneModAtLeastTwo",
                "1 mod n (n≥2)",
                "1 mod n = 1（n ≥ 2 の場合）",
            ),
            OutputLanguage::Korean => text(
                "OneModAtLeastTwo",
                "1 mod n (n≥2)",
                "1 mod n = 1(n ≥ 2일 때)",
            ),
            OutputLanguage::Vietnamese => {
                text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 khi n ≥ 2")
            }
        }
    }
}

impl NestedSameModAbsorptionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NestedSameModAbsorption",
            "nested same mod",
            "(a mod n) mod n = a mod n",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NestedSameModAbsorption",
            "同模嵌套吸收",
            "(a mod n) mod n = a mod n",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NestedSameModAbsorption",
                "相同模數巢狀運算",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::French => text(
                "NestedSameModAbsorption",
                "Modulo identique imbriqué",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Russian => text(
                "NestedSameModAbsorption",
                "Вложенный одинаковый модуль",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Spanish => text(
                "NestedSameModAbsorption",
                "Mismo módulo anidado",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Arabic => text(
                "NestedSameModAbsorption",
                "باقي قسمة متداخل بالمقياس نفسه",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Japanese => text(
                "NestedSameModAbsorption",
                "同じ法の入れ子",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Korean => text(
                "NestedSameModAbsorption",
                "동일한 법의 중첩",
                "(a mod n) mod n = a mod n",
            ),
            OutputLanguage::Vietnamese => text(
                "NestedSameModAbsorption",
                "Môđun giống nhau lồng nhau",
                "(a mod n) mod n = a mod n",
            ),
        }
    }
}

impl ModCompatibleSmallerModulusBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModCompatibleSmallerModulus",
            "compatible smaller modulus",
            "a mod d = (a mod m) mod d when m mod d = 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModCompatibleSmallerModulus",
            "相容更小模",
            "当 m mod d = 0 时 a mod d = (a mod m) mod d",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ModCompatibleSmallerModulus",
                "相容的較小模數",
                "a mod d = (a mod m) mod d（m mod d = 0 時）",
            ),
            OutputLanguage::French => text(
                "ModCompatibleSmallerModulus",
                "Module inférieur compatible",
                "a mod d = (a mod m) mod d si m mod d = 0",
            ),
            OutputLanguage::Russian => text(
                "ModCompatibleSmallerModulus",
                "Совместимый меньший модуль",
                "a mod d = (a mod m) mod d при m mod d = 0",
            ),
            OutputLanguage::Spanish => text(
                "ModCompatibleSmallerModulus",
                "Módulo menor compatible",
                "a mod d = (a mod m) mod d si m mod d = 0",
            ),
            OutputLanguage::Arabic => text(
                "ModCompatibleSmallerModulus",
                "مقياس أصغر متوافق",
                "a mod d = (a mod m) mod d إذا m mod d = 0",
            ),
            OutputLanguage::Japanese => text(
                "ModCompatibleSmallerModulus",
                "互換性のある小さい法",
                "a mod d = (a mod m) mod d（m mod d = 0 の場合）",
            ),
            OutputLanguage::Korean => text(
                "ModCompatibleSmallerModulus",
                "호환되는 작은 법",
                "a mod d = (a mod m) mod d(m mod d = 0일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "ModCompatibleSmallerModulus",
                "Môđun nhỏ hơn tương thích",
                "a mod d = (a mod m) mod d khi m mod d = 0",
            ),
        }
    }
}

impl MinIdempotentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MinIdempotent", "min(a,a)", "min(a,a) = a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MinIdempotent", "min(a,a)", "min(a,a) = a")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::French => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Russian => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Spanish => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Arabic => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Japanese => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Korean => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
            OutputLanguage::Vietnamese => text("MinIdempotent", "min(a,a)", "min(a,a) = a"),
        }
    }
}

impl MaxIdempotentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MaxIdempotent", "max(a,a)", "max(a,a) = a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MaxIdempotent", "max(a,a)", "max(a,a) = a")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::French => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Russian => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Spanish => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Arabic => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Japanese => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Korean => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
            OutputLanguage::Vietnamese => text("MaxIdempotent", "max(a,a)", "max(a,a) = a"),
        }
    }
}

impl MinCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MinCommutative", "min commutative", "min(a,b) = min(b,a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MinCommutative", "min 交换律", "min(a,b) = min(b,a)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("MinCommutative", "min 交換律", "min(a,b) = min(b,a)")
            }
            OutputLanguage::French => text(
                "MinCommutative",
                "Commutativité de min",
                "min(a,b) = min(b,a)",
            ),
            OutputLanguage::Russian => text(
                "MinCommutative",
                "Коммутативность min",
                "min(a,b) = min(b,a)",
            ),
            OutputLanguage::Spanish => text(
                "MinCommutative",
                "Conmutatividad de min",
                "min(a,b) = min(b,a)",
            ),
            OutputLanguage::Arabic => text("MinCommutative", "تبادلية min", "min(a,b) = min(b,a)"),
            OutputLanguage::Japanese => {
                text("MinCommutative", "min の可換性", "min(a,b) = min(b,a)")
            }
            OutputLanguage::Korean => text("MinCommutative", "min 교환법칙", "min(a,b) = min(b,a)"),
            OutputLanguage::Vietnamese => {
                text("MinCommutative", "Giao hoán của min", "min(a,b) = min(b,a)")
            }
        }
    }
}

impl MaxCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MaxCommutative", "max commutative", "max(a,b) = max(b,a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MaxCommutative", "max 交换律", "max(a,b) = max(b,a)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("MaxCommutative", "max 交換律", "max(a,b) = max(b,a)")
            }
            OutputLanguage::French => text(
                "MaxCommutative",
                "Commutativité de max",
                "max(a,b) = max(b,a)",
            ),
            OutputLanguage::Russian => text(
                "MaxCommutative",
                "Коммутативность max",
                "max(a,b) = max(b,a)",
            ),
            OutputLanguage::Spanish => text(
                "MaxCommutative",
                "Conmutatividad de max",
                "max(a,b) = max(b,a)",
            ),
            OutputLanguage::Arabic => text("MaxCommutative", "تبادلية max", "max(a,b) = max(b,a)"),
            OutputLanguage::Japanese => {
                text("MaxCommutative", "max の可換性", "max(a,b) = max(b,a)")
            }
            OutputLanguage::Korean => text("MaxCommutative", "max 교환법칙", "max(a,b) = max(b,a)"),
            OutputLanguage::Vietnamese => {
                text("MaxCommutative", "Giao hoán của max", "max(a,b) = max(b,a)")
            }
        }
    }
}

impl AbsAbsAbsorptionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsAbsAbsorption", "||a||", "||a|| = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsAbsAbsorption", "||a||", "||a|| = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::French => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Russian => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Spanish => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Arabic => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Japanese => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Korean => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
            OutputLanguage::Vietnamese => text("AbsAbsAbsorption", "||a||", "||a|| = |a|"),
        }
    }
}

impl ExpOfLnBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::French => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Russian => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Spanish => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Arabic => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Japanese => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Korean => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
            OutputLanguage::Vietnamese => text("ExpOfLn", "exp(ln(x))", "exp(ln(x)) = x"),
        }
    }
}

impl LnOfExpBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::French => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Russian => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Spanish => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Arabic => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Japanese => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Korean => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
            OutputLanguage::Vietnamese => text("LnOfExp", "ln(exp(x))", "ln(exp(x)) = x"),
        }
    }
}

impl FloorOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FloorOfInteger",
            "⌊n⌋ for integer n",
            "⌊n⌋ = n when n is an integer",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FloorOfInteger", "整数 n 的 ⌊n⌋", "当 n 为整数时 ⌊n⌋ = n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FloorOfInteger", "⌊n⌋（n 為整數）", "⌊n⌋ = n（n 為整數時）")
            }
            OutputLanguage::French => text(
                "FloorOfInteger",
                "⌊n⌋ pour n entier",
                "⌊n⌋ = n si n est entier",
            ),
            OutputLanguage::Russian => {
                text("FloorOfInteger", "⌊n⌋ для целого n", "⌊n⌋ = n если n целое")
            }
            OutputLanguage::Spanish => text(
                "FloorOfInteger",
                "⌊n⌋ para n entero",
                "⌊n⌋ = n si n es entero",
            ),
            OutputLanguage::Arabic => text(
                "FloorOfInteger",
                "⌊n⌋ للعدد الصحيح n",
                "⌊n⌋ = n إذا كان n صحيحًا",
            ),
            OutputLanguage::Japanese => text(
                "FloorOfInteger",
                "⌊n⌋（n は整数）",
                "⌊n⌋ = n（n が整数の場合）",
            ),
            OutputLanguage::Korean => {
                text("FloorOfInteger", "⌊n⌋(n은 정수)", "⌊n⌋ = n(n이 정수일 때)")
            }
            OutputLanguage::Vietnamese => text(
                "FloorOfInteger",
                "⌊n⌋ với n nguyên",
                "⌊n⌋ = n khi n là số nguyên",
            ),
        }
    }
}

impl CeilOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CeilOfInteger",
            "⌈n⌉ for integer n",
            "⌈n⌉ = n when n is an integer",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CeilOfInteger", "整数 n 的 ⌈n⌉", "当 n 为整数时 ⌈n⌉ = n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("CeilOfInteger", "⌈n⌉（n 為整數）", "⌈n⌉ = n（n 為整數時）")
            }
            OutputLanguage::French => text(
                "CeilOfInteger",
                "⌈n⌉ pour n entier",
                "⌈n⌉ = n si n est entier",
            ),
            OutputLanguage::Russian => {
                text("CeilOfInteger", "⌈n⌉ для целого n", "⌈n⌉ = n если n целое")
            }
            OutputLanguage::Spanish => text(
                "CeilOfInteger",
                "⌈n⌉ para n entero",
                "⌈n⌉ = n si n es entero",
            ),
            OutputLanguage::Arabic => text(
                "CeilOfInteger",
                "⌈n⌉ للعدد الصحيح n",
                "⌈n⌉ = n إذا كان n صحيحًا",
            ),
            OutputLanguage::Japanese => text(
                "CeilOfInteger",
                "⌈n⌉（n は整数）",
                "⌈n⌉ = n（n が整数の場合）",
            ),
            OutputLanguage::Korean => {
                text("CeilOfInteger", "⌈n⌉(n은 정수)", "⌈n⌉ = n(n이 정수일 때)")
            }
            OutputLanguage::Vietnamese => text(
                "CeilOfInteger",
                "⌈n⌉ với n nguyên",
                "⌈n⌉ = n khi n là số nguyên",
            ),
        }
    }
}

impl ModSelfZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ModSelfZero", "a mod a", "a mod a = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModSelfZero", "a mod a", "a mod a = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::French => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Russian => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Spanish => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Arabic => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Japanese => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Korean => text("ModSelfZero", "a mod a", "a mod a = 0"),
            OutputLanguage::Vietnamese => text("ModSelfZero", "a mod a", "a mod a = 0"),
        }
    }
}

impl FloorOfCeilOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n for integer n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "对整数 n，⌊⌈n⌉⌋ = n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n（n 為整數）")
            }
            OutputLanguage::French => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n pour n entier")
            }
            OutputLanguage::Russian => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n для целого n")
            }
            OutputLanguage::Spanish => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n para n entero")
            }
            OutputLanguage::Arabic => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n للعدد الصحيح n")
            }
            OutputLanguage::Japanese => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n（n は整数）")
            }
            OutputLanguage::Korean => text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n(n은 정수)"),
            OutputLanguage::Vietnamese => {
                text("FloorOfCeilOfInteger", "⌊⌈n⌉⌋", "⌊⌈n⌉⌋ = n với n nguyên")
            }
        }
    }
}

impl CeilOfFloorOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n for integer n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "对整数 n，⌈⌊n⌋⌉ = n")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n（n 為整數）")
            }
            OutputLanguage::French => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n pour n entier")
            }
            OutputLanguage::Russian => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n для целого n")
            }
            OutputLanguage::Spanish => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n para n entero")
            }
            OutputLanguage::Arabic => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n للعدد الصحيح n")
            }
            OutputLanguage::Japanese => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n（n は整数）")
            }
            OutputLanguage::Korean => text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n(n은 정수)"),
            OutputLanguage::Vietnamese => {
                text("CeilOfFloorOfInteger", "⌈⌊n⌋⌉", "⌈⌊n⌋⌉ = n với n nguyên")
            }
        }
    }
}

impl SqrtOfSquareEqualsAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|")
            }
            OutputLanguage::French => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Russian => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Spanish => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Arabic => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Japanese => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Korean => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
            OutputLanguage::Vietnamese => text("SqrtOfSquareEqualsAbs", "√(a²)=|a|", "√(a²) = |a|"),
        }
    }
}

impl QuotByOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("QuotByOne", "a ÷ 1", "a quot 1 = a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("QuotByOne", "a ÷ 1", "a quot 1 = a")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::French => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Russian => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Spanish => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Arabic => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Japanese => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Korean => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
            OutputLanguage::Vietnamese => text("QuotByOne", "a ÷ 1", "a quot 1 = a"),
        }
    }
}

impl QuotSelfOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)")
            }
            OutputLanguage::French => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Russian => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Spanish => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Arabic => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Japanese => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Korean => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
            OutputLanguage::Vietnamese => text("QuotSelfOne", "a ÷ a", "a quot a = 1 (a ≠ 0)"),
        }
    }
}

impl LcmCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LcmCommutative", "lcm commutative", "lcm(a,b) = lcm(b,a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LcmCommutative", "lcm 交换律", "lcm(a,b) = lcm(b,a)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LcmCommutative", "lcm 交換律", "lcm(a,b) = lcm(b,a)")
            }
            OutputLanguage::French => text(
                "LcmCommutative",
                "Commutativité de lcm",
                "lcm(a,b) = lcm(b,a)",
            ),
            OutputLanguage::Russian => text(
                "LcmCommutative",
                "Коммутативность lcm",
                "lcm(a,b) = lcm(b,a)",
            ),
            OutputLanguage::Spanish => text(
                "LcmCommutative",
                "Conmutatividad de lcm",
                "lcm(a,b) = lcm(b,a)",
            ),
            OutputLanguage::Arabic => text("LcmCommutative", "تبادلية lcm", "lcm(a,b) = lcm(b,a)"),
            OutputLanguage::Japanese => {
                text("LcmCommutative", "lcm の可換性", "lcm(a,b) = lcm(b,a)")
            }
            OutputLanguage::Korean => text("LcmCommutative", "lcm 교환법칙", "lcm(a,b) = lcm(b,a)"),
            OutputLanguage::Vietnamese => {
                text("LcmCommutative", "Giao hoán của lcm", "lcm(a,b) = lcm(b,a)")
            }
        }
    }
}

impl LcmIdempotentAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|")
            }
            OutputLanguage::French => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Russian => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Spanish => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Arabic => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Japanese => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Korean => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
            OutputLanguage::Vietnamese => text("LcmIdempotentAbs", "lcm(a,a)", "lcm(a,a) = |a|"),
        }
    }
}

impl GcdCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("GcdCommutative", "gcd commutative", "gcd(a,b) = gcd(b,a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("GcdCommutative", "gcd 交换律", "gcd(a,b) = gcd(b,a)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("GcdCommutative", "gcd 交換律", "gcd(a,b) = gcd(b,a)")
            }
            OutputLanguage::French => text(
                "GcdCommutative",
                "Commutativité de gcd",
                "gcd(a,b) = gcd(b,a)",
            ),
            OutputLanguage::Russian => text(
                "GcdCommutative",
                "Коммутативность gcd",
                "gcd(a,b) = gcd(b,a)",
            ),
            OutputLanguage::Spanish => text(
                "GcdCommutative",
                "Conmutatividad de gcd",
                "gcd(a,b) = gcd(b,a)",
            ),
            OutputLanguage::Arabic => text("GcdCommutative", "تبادلية gcd", "gcd(a,b) = gcd(b,a)"),
            OutputLanguage::Japanese => {
                text("GcdCommutative", "gcd の可換性", "gcd(a,b) = gcd(b,a)")
            }
            OutputLanguage::Korean => text("GcdCommutative", "gcd 교환법칙", "gcd(a,b) = gcd(b,a)"),
            OutputLanguage::Vietnamese => {
                text("GcdCommutative", "Giao hoán của gcd", "gcd(a,b) = gcd(b,a)")
            }
        }
    }
}

impl GcdIdempotentAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|")
            }
            OutputLanguage::French => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Russian => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Spanish => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Arabic => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Japanese => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Korean => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
            OutputLanguage::Vietnamese => text("GcdIdempotentAbs", "gcd(a,a)", "gcd(a,a) = |a|"),
        }
    }
}

impl GcdRightZeroAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|")
            }
            OutputLanguage::French => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Russian => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Spanish => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Arabic => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Japanese => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Korean => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
            OutputLanguage::Vietnamese => text("GcdRightZeroAbs", "gcd(a,0)", "gcd(a,0) = |a|"),
        }
    }
}

impl GcdLeftZeroAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|")
            }
            OutputLanguage::French => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Russian => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Spanish => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Arabic => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Japanese => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Korean => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
            OutputLanguage::Vietnamese => text("GcdLeftZeroAbs", "gcd(0,a)", "gcd(0,a) = |a|"),
        }
    }
}

impl FactorialSuccessorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!")
            }
            OutputLanguage::French => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Russian => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Spanish => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Arabic => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Japanese => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Korean => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
            OutputLanguage::Vietnamese => text("FactorialSuccessor", "(n+1)!", "(n+1)! = (n+1)·n!"),
        }
    }
}

impl AbsNonnegEqualsSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsNonnegEqualsSelf", "|a| for a≥0", "|a| = a when a ≥ 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsNonnegEqualsSelf", "非负时的 |a|", "当 a ≥ 0 时 |a| = a")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsNonnegEqualsSelf",
                "|a|（a≥0 時）",
                "|a| = a（a ≥ 0 時）",
            ),
            OutputLanguage::French => {
                text("AbsNonnegEqualsSelf", "|a| pour a≥0", "|a| = a si a ≥ 0")
            }
            OutputLanguage::Russian => {
                text("AbsNonnegEqualsSelf", "|a| для a≥0", "|a| = a при a ≥ 0")
            }
            OutputLanguage::Spanish => {
                text("AbsNonnegEqualsSelf", "|a| para a≥0", "|a| = a si a ≥ 0")
            }
            OutputLanguage::Arabic => {
                text("AbsNonnegEqualsSelf", "|a| لـ a≥0", "|a| = a إذا a ≥ 0")
            }
            OutputLanguage::Japanese => text(
                "AbsNonnegEqualsSelf",
                "|a|（a≥0 の場合）",
                "|a| = a（a ≥ 0 の場合）",
            ),
            OutputLanguage::Korean => text(
                "AbsNonnegEqualsSelf",
                "|a|(a≥0일 때)",
                "|a| = a(a ≥ 0일 때)",
            ),
            OutputLanguage::Vietnamese => {
                text("AbsNonnegEqualsSelf", "|a| với a≥0", "|a| = a khi a ≥ 0")
            }
        }
    }
}

impl AbsNonposEqualsNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsNonposEqualsNegation",
            "|a| for a≤0",
            "|a| = -a when a ≤ 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsNonposEqualsNegation",
            "非正时的 |a|",
            "当 a ≤ 0 时 |a| = -a",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsNonposEqualsNegation",
                "|a|（a≤0 時）",
                "|a| = -a（a ≤ 0 時）",
            ),
            OutputLanguage::French => text(
                "AbsNonposEqualsNegation",
                "|a| pour a≤0",
                "|a| = -a si a ≤ 0",
            ),
            OutputLanguage::Russian => text(
                "AbsNonposEqualsNegation",
                "|a| для a≤0",
                "|a| = -a при a ≤ 0",
            ),
            OutputLanguage::Spanish => text(
                "AbsNonposEqualsNegation",
                "|a| para a≤0",
                "|a| = -a si a ≤ 0",
            ),
            OutputLanguage::Arabic => text(
                "AbsNonposEqualsNegation",
                "|a| لـ a≤0",
                "|a| = -a إذا a ≤ 0",
            ),
            OutputLanguage::Japanese => text(
                "AbsNonposEqualsNegation",
                "|a|（a≤0 の場合）",
                "|a| = -a（a ≤ 0 の場合）",
            ),
            OutputLanguage::Korean => text(
                "AbsNonposEqualsNegation",
                "|a|(a≤0일 때)",
                "|a| = -a(a ≤ 0일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsNonposEqualsNegation",
                "|a| với a≤0",
                "|a| = -a khi a ≤ 0",
            ),
        }
    }
}

impl SignOfPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SignOfPositive",
            "sign of positive",
            "sign(a) = 1 when a > 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfPositive", "正数的符号", "当 a > 0 时 sign(a) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SignOfPositive", "正數的符號", "sign(a) = 1（a > 0 時）")
            }
            OutputLanguage::French => text(
                "SignOfPositive",
                "Signe d'un positif",
                "sign(a) = 1 si a > 0",
            ),
            OutputLanguage::Russian => text(
                "SignOfPositive",
                "Знак положительного числа",
                "sign(a) = 1 при a > 0",
            ),
            OutputLanguage::Spanish => text(
                "SignOfPositive",
                "Signo de un positivo",
                "sign(a) = 1 si a > 0",
            ),
            OutputLanguage::Arabic => {
                text("SignOfPositive", "إشارة عدد موجب", "sign(a) = 1 إذا a > 0")
            }
            OutputLanguage::Japanese => text(
                "SignOfPositive",
                "正数の符号",
                "sign(a) = 1（a > 0 の場合）",
            ),
            OutputLanguage::Korean => {
                text("SignOfPositive", "양수의 부호", "sign(a) = 1(a > 0일 때)")
            }
            OutputLanguage::Vietnamese => text(
                "SignOfPositive",
                "Dấu của số dương",
                "sign(a) = 1 khi a > 0",
            ),
        }
    }
}

impl SignOfNegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SignOfNegative",
            "sign of negative",
            "sign(a) = -1 when a < 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfNegative", "负数的符号", "当 a < 0 时 sign(a) = -1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SignOfNegative", "負數的符號", "sign(a) = -1（a < 0 時）")
            }
            OutputLanguage::French => text(
                "SignOfNegative",
                "Signe d'un négatif",
                "sign(a) = -1 si a < 0",
            ),
            OutputLanguage::Russian => text(
                "SignOfNegative",
                "Знак отрицательного числа",
                "sign(a) = -1 при a < 0",
            ),
            OutputLanguage::Spanish => text(
                "SignOfNegative",
                "Signo de un negativo",
                "sign(a) = -1 si a < 0",
            ),
            OutputLanguage::Arabic => {
                text("SignOfNegative", "إشارة عدد سالب", "sign(a) = -1 إذا a < 0")
            }
            OutputLanguage::Japanese => text(
                "SignOfNegative",
                "負数の符号",
                "sign(a) = -1（a < 0 の場合）",
            ),
            OutputLanguage::Korean => {
                text("SignOfNegative", "음수의 부호", "sign(a) = -1(a < 0일 때)")
            }
            OutputLanguage::Vietnamese => {
                text("SignOfNegative", "Dấu của số âm", "sign(a) = -1 khi a < 0")
            }
        }
    }
}

impl MaxRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MaxRightWhenLessEqual",
            "max when a≤b",
            "max(a,b) = b when a ≤ b",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MaxRightWhenLessEqual",
            "a≤b 时的 max",
            "当 a ≤ b 时 max(a,b) = b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MaxRightWhenLessEqual",
                "max（a≤b 時）",
                "max(a,b) = b（a ≤ b 時）",
            ),
            OutputLanguage::French => text(
                "MaxRightWhenLessEqual",
                "max si a≤b",
                "max(a,b) = b si a ≤ b",
            ),
            OutputLanguage::Russian => text(
                "MaxRightWhenLessEqual",
                "max при a≤b",
                "max(a,b) = b при a ≤ b",
            ),
            OutputLanguage::Spanish => text(
                "MaxRightWhenLessEqual",
                "max si a≤b",
                "max(a,b) = b si a ≤ b",
            ),
            OutputLanguage::Arabic => text(
                "MaxRightWhenLessEqual",
                "max إذا a≤b",
                "max(a,b) = b إذا a ≤ b",
            ),
            OutputLanguage::Japanese => text(
                "MaxRightWhenLessEqual",
                "max（a≤b の場合）",
                "max(a,b) = b（a ≤ b の場合）",
            ),
            OutputLanguage::Korean => text(
                "MaxRightWhenLessEqual",
                "max(a≤b일 때)",
                "max(a,b) = b(a ≤ b일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "MaxRightWhenLessEqual",
                "max khi a≤b",
                "max(a,b) = b khi a ≤ b",
            ),
        }
    }
}

impl MaxLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MaxLeftWhenLessEqual",
            "max when b≤a",
            "max(a,b) = a when b ≤ a",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MaxLeftWhenLessEqual",
            "b≤a 时的 max",
            "当 b ≤ a 时 max(a,b) = a",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MaxLeftWhenLessEqual",
                "max（b≤a 時）",
                "max(a,b) = a（b ≤ a 時）",
            ),
            OutputLanguage::French => text(
                "MaxLeftWhenLessEqual",
                "max si b≤a",
                "max(a,b) = a si b ≤ a",
            ),
            OutputLanguage::Russian => text(
                "MaxLeftWhenLessEqual",
                "max при b≤a",
                "max(a,b) = a при b ≤ a",
            ),
            OutputLanguage::Spanish => text(
                "MaxLeftWhenLessEqual",
                "max si b≤a",
                "max(a,b) = a si b ≤ a",
            ),
            OutputLanguage::Arabic => text(
                "MaxLeftWhenLessEqual",
                "max إذا b≤a",
                "max(a,b) = a إذا b ≤ a",
            ),
            OutputLanguage::Japanese => text(
                "MaxLeftWhenLessEqual",
                "max（b≤a の場合）",
                "max(a,b) = a（b ≤ a の場合）",
            ),
            OutputLanguage::Korean => text(
                "MaxLeftWhenLessEqual",
                "max(b≤a일 때)",
                "max(a,b) = a(b ≤ a일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "MaxLeftWhenLessEqual",
                "max khi b≤a",
                "max(a,b) = a khi b ≤ a",
            ),
        }
    }
}

impl MinLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MinLeftWhenLessEqual",
            "min when a≤b",
            "min(a,b) = a when a ≤ b",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MinLeftWhenLessEqual",
            "a≤b 时的 min",
            "当 a ≤ b 时 min(a,b) = a",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MinLeftWhenLessEqual",
                "min（a≤b 時）",
                "min(a,b) = a（a ≤ b 時）",
            ),
            OutputLanguage::French => text(
                "MinLeftWhenLessEqual",
                "min si a≤b",
                "min(a,b) = a si a ≤ b",
            ),
            OutputLanguage::Russian => text(
                "MinLeftWhenLessEqual",
                "min при a≤b",
                "min(a,b) = a при a ≤ b",
            ),
            OutputLanguage::Spanish => text(
                "MinLeftWhenLessEqual",
                "min si a≤b",
                "min(a,b) = a si a ≤ b",
            ),
            OutputLanguage::Arabic => text(
                "MinLeftWhenLessEqual",
                "min إذا a≤b",
                "min(a,b) = a إذا a ≤ b",
            ),
            OutputLanguage::Japanese => text(
                "MinLeftWhenLessEqual",
                "min（a≤b の場合）",
                "min(a,b) = a（a ≤ b の場合）",
            ),
            OutputLanguage::Korean => text(
                "MinLeftWhenLessEqual",
                "min(a≤b일 때)",
                "min(a,b) = a(a ≤ b일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "MinLeftWhenLessEqual",
                "min khi a≤b",
                "min(a,b) = a khi a ≤ b",
            ),
        }
    }
}

impl MinRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MinRightWhenLessEqual",
            "min when b≤a",
            "min(a,b) = b when b ≤ a",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MinRightWhenLessEqual",
            "b≤a 时的 min",
            "当 b ≤ a 时 min(a,b) = b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MinRightWhenLessEqual",
                "min（b≤a 時）",
                "min(a,b) = b（b ≤ a 時）",
            ),
            OutputLanguage::French => text(
                "MinRightWhenLessEqual",
                "min si b≤a",
                "min(a,b) = b si b ≤ a",
            ),
            OutputLanguage::Russian => text(
                "MinRightWhenLessEqual",
                "min при b≤a",
                "min(a,b) = b при b ≤ a",
            ),
            OutputLanguage::Spanish => text(
                "MinRightWhenLessEqual",
                "min si b≤a",
                "min(a,b) = b si b ≤ a",
            ),
            OutputLanguage::Arabic => text(
                "MinRightWhenLessEqual",
                "min إذا b≤a",
                "min(a,b) = b إذا b ≤ a",
            ),
            OutputLanguage::Japanese => text(
                "MinRightWhenLessEqual",
                "min（b≤a の場合）",
                "min(a,b) = b（b ≤ a の場合）",
            ),
            OutputLanguage::Korean => text(
                "MinRightWhenLessEqual",
                "min(b≤a일 때)",
                "min(a,b) = b(b ≤ a일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "MinRightWhenLessEqual",
                "min khi b≤a",
                "min(a,b) = b khi b ≤ a",
            ),
        }
    }
}

impl GcdDividesArgumentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "GcdDividesArgument",
            "gcd divides",
            "gcd(a,b) divides a (and b)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "GcdDividesArgument",
            "gcd 整除",
            "gcd(a,b) 整除 a（以及 b）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("GcdDividesArgument", "gcd 整除", "gcd(a,b) 整除 a 及 b")
            }
            OutputLanguage::French => text(
                "GcdDividesArgument",
                "Divisibilité par gcd",
                "gcd(a,b) divise a et b",
            ),
            OutputLanguage::Russian => text(
                "GcdDividesArgument",
                "Делимость на gcd",
                "gcd(a,b) делит a и b",
            ),
            OutputLanguage::Spanish => text(
                "GcdDividesArgument",
                "Divisibilidad por gcd",
                "gcd(a,b) divide a y b",
            ),
            OutputLanguage::Arabic => {
                text("GcdDividesArgument", "القسمة على gcd", "gcd(a,b) يقسم a وb")
            }
            OutputLanguage::Japanese => text(
                "GcdDividesArgument",
                "gcd による整除",
                "gcd(a,b) は a と b を割り切ります",
            ),
            OutputLanguage::Korean => text(
                "GcdDividesArgument",
                "gcd 나눔",
                "gcd(a,b)는 a와 b를 나눕니다",
            ),
            OutputLanguage::Vietnamese => text(
                "GcdDividesArgument",
                "Chia hết bởi gcd",
                "gcd(a,b) chia hết a và b",
            ),
        }
    }
}

impl ProductModFactorZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductModFactorZero",
            "product mod factor",
            "(k·n) mod n = 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductModFactorZero", "积对因子取模", "(k·n) mod n = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ProductModFactorZero", "乘積對因子取模", "(k·n) mod n = 0")
            }
            OutputLanguage::French => text(
                "ProductModFactorZero",
                "Produit modulo un facteur",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Russian => text(
                "ProductModFactorZero",
                "Произведение по модулю множителя",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Spanish => text(
                "ProductModFactorZero",
                "Producto módulo factor",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Arabic => text(
                "ProductModFactorZero",
                "حاصل ضرب بترديد عامل",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Japanese => text(
                "ProductModFactorZero",
                "因子を法とする積の剰余",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Korean => text(
                "ProductModFactorZero",
                "인자를 법으로 한 곱의 나머지",
                "(k·n) mod n = 0",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductModFactorZero",
                "Tích lấy môđun theo thừa số",
                "(k·n) mod n = 0",
            ),
        }
    }
}

impl EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EqualityFromTwoSidedWeakOrder",
            "a≤b and b≤a",
            "a = b follows from a ≤ b and b ≤ a",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EqualityFromTwoSidedWeakOrder",
            "a≤b 且 b≤a",
            "由 a ≤ b 且 b ≤ a 得到 a = b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::French => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Russian => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Spanish => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Arabic => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Japanese => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Korean => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
            OutputLanguage::Vietnamese => text(
                "EqualityFromTwoSidedWeakOrder",
                "a≤b ∧ b≤a",
                "a ≤ b ∧ b ≤ a ⇒ a = b",
            ),
        }
    }
}

impl DiffZeroFromEqualOperandsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DiffZeroFromEqualOperands",
            "a−b=0 from a=b",
            "a − b = 0 follows from a = b",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DiffZeroFromEqualOperands",
            "由 a=b 得 a−b=0",
            "由 a = b 得到 a − b = 0",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::French => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Russian => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Spanish => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Arabic => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Japanese => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Korean => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
            OutputLanguage::Vietnamese => text(
                "DiffZeroFromEqualOperands",
                "a=b ⇒ a−b=0",
                "a = b ⇒ a − b = 0",
            ),
        }
    }
}

impl EqualFromKnownDifferenceZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EqualFromKnownDifferenceZero",
            "a=b from a−b=0",
            "a = b follows from a known a − b = 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EqualFromKnownDifferenceZero",
            "由 a−b=0 得 a=b",
            "由已知 a − b = 0 得到 a = b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::French => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Russian => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Spanish => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Arabic => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Japanese => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Korean => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
            OutputLanguage::Vietnamese => text(
                "EqualFromKnownDifferenceZero",
                "a−b=0 ⇒ a=b",
                "a − b = 0 ⇒ a = b",
            ),
        }
    }
}

impl ZeroProductCancelBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ZeroProductCancel",
            "zero product",
            "a·b = 0 with a≠0 gives b = 0 (and symmetrically)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ZeroProductCancel",
            "零因子消元",
            "a·b = 0 且 a≠0 则 b = 0（对称亦然）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ZeroProductCancel",
                "零乘積",
                "a·b = 0 且 a≠0 推出 b = 0（對稱情況亦然）",
            ),
            OutputLanguage::French => text(
                "ZeroProductCancel",
                "Produit nul",
                "a·b = 0 avec a≠0 implique b = 0 (et symétriquement)",
            ),
            OutputLanguage::Russian => text(
                "ZeroProductCancel",
                "Нулевое произведение",
                "a·b = 0 при a≠0 влечёт b = 0 (и симметрично)",
            ),
            OutputLanguage::Spanish => text(
                "ZeroProductCancel",
                "Producto cero",
                "a·b = 0 con a≠0 implica b = 0 (y simétricamente)",
            ),
            OutputLanguage::Arabic => text(
                "ZeroProductCancel",
                "حاصل ضرب صفري",
                "a·b = 0 مع a≠0 تستلزم b = 0 (وبالتناظر أيضًا)",
            ),
            OutputLanguage::Japanese => text(
                "ZeroProductCancel",
                "積がゼロ",
                "a·b = 0 かつ a≠0 なら b = 0 です（対称の場合も同様）",
            ),
            OutputLanguage::Korean => text(
                "ZeroProductCancel",
                "곱이 0",
                "a·b = 0이고 a≠0이면 b = 0입니다(대칭적으로도 성립)",
            ),
            OutputLanguage::Vietnamese => text(
                "ZeroProductCancel",
                "Tích bằng không",
                "a·b = 0 với a≠0 suy ra b = 0 (và đối xứng)",
            ),
        }
    }
}

impl SignOfNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)")
            }
            OutputLanguage::French => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Russian => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Spanish => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Arabic => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Japanese => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Korean => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
            OutputLanguage::Vietnamese => text("SignOfNegation", "sign(-a)", "sign(-a) = -sign(a)"),
        }
    }
}

impl SignTimesAbsEqualsArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::French => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Russian => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Spanish => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Arabic => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Japanese => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Korean => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
            OutputLanguage::Vietnamese => {
                text("SignTimesAbsEqualsArg", "sign(a)·|a|", "sign(a)·|a| = a")
            }
        }
    }
}

impl AbsEqualsSignTimesArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsEqualsSignTimesArg",
            "|a| = sign(a)·a",
            "|a| = sign(a)·a when sign is defined",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsEqualsSignTimesArg",
            "|a| = sign(a)·a",
            "在符号有定义时 |a| = sign(a)·a",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a（sign 定義成立時）",
            ),
            OutputLanguage::French => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a si sign est défini",
            ),
            OutputLanguage::Russian => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a если sign определён",
            ),
            OutputLanguage::Spanish => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a si sign está definido",
            ),
            OutputLanguage::Arabic => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a إذا كانت sign معرّفة",
            ),
            OutputLanguage::Japanese => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a（sign が定義されている場合）",
            ),
            OutputLanguage::Korean => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a(sign이 정의될 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsEqualsSignTimesArg",
                "|a| = sign(a)·a",
                "|a| = sign(a)·a khi sign xác định",
            ),
        }
    }
}

impl SignOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::French => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Russian => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Spanish => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Arabic => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Japanese => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Korean => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
            OutputLanguage::Vietnamese => {
                text("SignOfProduct", "sign(a·b)", "sign(a·b) = sign(a)·sign(b)")
            }
        }
    }
}

impl SubtractionFromKnownAdditionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubtractionFromKnownAddition",
            "subtraction from addition",
            "c = a − b follows from a known a = b + c",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubtractionFromKnownAddition",
            "由加法得减法",
            "由已知 a = b + c 得到 c = a − b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubtractionFromKnownAddition",
                "由加法得減法",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::French => text(
                "SubtractionFromKnownAddition",
                "Soustraction depuis l'addition",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Russian => text(
                "SubtractionFromKnownAddition",
                "Вычитание из сложения",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Spanish => text(
                "SubtractionFromKnownAddition",
                "Resta desde suma",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Arabic => text(
                "SubtractionFromKnownAddition",
                "طرح من الجمع",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Japanese => text(
                "SubtractionFromKnownAddition",
                "加算から減算",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Korean => text(
                "SubtractionFromKnownAddition",
                "덧셈에서 뺄셈",
                "a = b + c ⇒ c = a − b",
            ),
            OutputLanguage::Vietnamese => text(
                "SubtractionFromKnownAddition",
                "Phép trừ từ phép cộng",
                "a = b + c ⇒ c = a − b",
            ),
        }
    }
}

impl QuotEuclideanDecompositionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "QuotEuclideanDecomposition",
            "Euclidean quot",
            "a = (a quot n)·n + (a mod n)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "QuotEuclideanDecomposition",
            "欧几里得商",
            "a = (a quot n)·n + (a mod n)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "QuotEuclideanDecomposition",
                "Euclid 整數商",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::French => text(
                "QuotEuclideanDecomposition",
                "Quotient euclidien",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Russian => text(
                "QuotEuclideanDecomposition",
                "Евклидово частное",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Spanish => text(
                "QuotEuclideanDecomposition",
                "Cociente euclídeo",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Arabic => text(
                "QuotEuclideanDecomposition",
                "خارج قسمة إقليدي",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Japanese => text(
                "QuotEuclideanDecomposition",
                "ユークリッドの商",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Korean => text(
                "QuotEuclideanDecomposition",
                "유클리드 몫",
                "a = (a quot n)·n + (a mod n)",
            ),
            OutputLanguage::Vietnamese => text(
                "QuotEuclideanDecomposition",
                "Thương Euclid",
                "a = (a quot n)·n + (a mod n)",
            ),
        }
    }
}

impl ModDividendMinusRemainderZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModDividendMinusRemainderZero",
            "mod remainder",
            "a − (a mod n) is divisible by n",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModDividendMinusRemainderZero",
            "模余数",
            "a − (a mod n) 可被 n 整除",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ModDividendMinusRemainderZero",
                "模運算餘數",
                "a − (a mod n) 可被 n 整除",
            ),
            OutputLanguage::French => text(
                "ModDividendMinusRemainderZero",
                "Reste modulaire",
                "a − (a mod n) est divisible par n",
            ),
            OutputLanguage::Russian => text(
                "ModDividendMinusRemainderZero",
                "Остаток по модулю",
                "a − (a mod n) делится на n",
            ),
            OutputLanguage::Spanish => text(
                "ModDividendMinusRemainderZero",
                "Resto modular",
                "a − (a mod n) es divisible por n",
            ),
            OutputLanguage::Arabic => text(
                "ModDividendMinusRemainderZero",
                "باقي القسمة",
                "a − (a mod n) يقبل القسمة على n",
            ),
            OutputLanguage::Japanese => text(
                "ModDividendMinusRemainderZero",
                "剰余",
                "a − (a mod n) は n で割り切れます",
            ),
            OutputLanguage::Korean => text(
                "ModDividendMinusRemainderZero",
                "나머지",
                "a − (a mod n)은 n으로 나누어집니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ModDividendMinusRemainderZero",
                "Số dư",
                "a − (a mod n) chia hết cho n",
            ),
        }
    }
}

impl SquareSumComponentZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SquareSumComponentZero",
            "square-sum zero",
            "a² + b² = 0 forces a = 0 and b = 0 (over reals)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SquareSumComponentZero",
            "平方和为零",
            "在实数上 a² + b² = 0 蕴含 a = 0 且 b = 0",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SquareSumComponentZero",
                "平方和為零",
                "對實數，a² + b² = 0 推出 a = 0 且 b = 0",
            ),
            OutputLanguage::French => text(
                "SquareSumComponentZero",
                "Somme de carrés nulle",
                "Sur les réels, a² + b² = 0 implique a = 0 et b = 0",
            ),
            OutputLanguage::Russian => text(
                "SquareSumComponentZero",
                "Нулевая сумма квадратов",
                "Для вещественных a² + b² = 0 влечёт a = 0 и b = 0",
            ),
            OutputLanguage::Spanish => text(
                "SquareSumComponentZero",
                "Suma de cuadrados cero",
                "En los reales, a² + b² = 0 implica a = 0 y b = 0",
            ),
            OutputLanguage::Arabic => text(
                "SquareSumComponentZero",
                "مجموع مربعات صفري",
                "للأعداد الحقيقية a² + b² = 0 تستلزم a = 0 وb = 0",
            ),
            OutputLanguage::Japanese => text(
                "SquareSumComponentZero",
                "平方和がゼロ",
                "実数では a² + b² = 0 から a = 0 かつ b = 0 を導きます",
            ),
            OutputLanguage::Korean => text(
                "SquareSumComponentZero",
                "제곱합이 0",
                "실수에서 a² + b² = 0이면 a = 0 및 b = 0입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SquareSumComponentZero",
                "Tổng bình phương bằng không",
                "Trên số thực, a² + b² = 0 suy ra a = 0 và b = 0",
            ),
        }
    }
}

impl MinusOneOddNaturalPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MinusOneOddNaturalPower",
            "(-1)^(odd)",
            "(-1)^n = -1 for odd natural n",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MinusOneOddNaturalPower",
            "(-1)^(odd)",
            "对奇自然数 n，(-1)^n = -1",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MinusOneOddNaturalPower",
                "(-1) 的奇數次方",
                "(-1)^n = -1（n 為奇自然數）",
            ),
            OutputLanguage::French => text(
                "MinusOneOddNaturalPower",
                "Puissance impaire de (-1)",
                "(-1)^n = -1 pour n naturel impair",
            ),
            OutputLanguage::Russian => text(
                "MinusOneOddNaturalPower",
                "Нечётная степень (-1)",
                "(-1)^n = -1 для нечётного натурального n",
            ),
            OutputLanguage::Spanish => text(
                "MinusOneOddNaturalPower",
                "Potencia impar de (-1)",
                "(-1)^n = -1 para n natural impar",
            ),
            OutputLanguage::Arabic => text(
                "MinusOneOddNaturalPower",
                "قوة فردية لـ (-1)",
                "(-1)^n = -1 للعدد الطبيعي الفردي n",
            ),
            OutputLanguage::Japanese => text(
                "MinusOneOddNaturalPower",
                "(-1) の奇数乗",
                "(-1)^n = -1（n は奇数の自然数）",
            ),
            OutputLanguage::Korean => text(
                "MinusOneOddNaturalPower",
                "(-1)의 홀수 거듭제곱",
                "(-1)^n = -1(n은 홀수 자연수)",
            ),
            OutputLanguage::Vietnamese => text(
                "MinusOneOddNaturalPower",
                "Lũy thừa lẻ của (-1)",
                "(-1)^n = -1 với n tự nhiên lẻ",
            ),
        }
    }
}

impl LcmGcdProductAbsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::French => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Russian => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Spanish => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Arabic => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Japanese => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Korean => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
            OutputLanguage::Vietnamese => {
                text("LcmGcdProductAbs", "lcm·gcd", "lcm(a,b)·gcd(a,b) = |a·b|")
            }
        }
    }
}

impl UnionEmptyRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::French => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Russian => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Spanish => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Arabic => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Japanese => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Korean => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
            OutputLanguage::Vietnamese => text("UnionEmptyRight", "A ∪ ∅", "A ∪ ∅ = A"),
        }
    }
}

impl UnionEmptyLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::French => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Russian => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Spanish => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Arabic => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Japanese => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Korean => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
            OutputLanguage::Vietnamese => text("UnionEmptyLeft", "∅ ∪ A", "∅ ∪ A = A"),
        }
    }
}

impl IntersectEmptyRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::French => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Russian => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Spanish => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Arabic => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Japanese => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Korean => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
            OutputLanguage::Vietnamese => text("IntersectEmptyRight", "A ∩ ∅", "A ∩ ∅ = ∅"),
        }
    }
}

impl IntersectEmptyLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::French => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Russian => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Spanish => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Arabic => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Japanese => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Korean => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
            OutputLanguage::Vietnamese => text("IntersectEmptyLeft", "∅ ∩ A", "∅ ∩ A = ∅"),
        }
    }
}

impl SetMinusSelfEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusSelfEmpty", "A \\\\ A", "A \\\\ A = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::French => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Russian => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Spanish => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Arabic => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Japanese => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Korean => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
            OutputLanguage::Vietnamese => text("SetMinusSelfEmpty", "A \\ A", "A \\ A = ∅"),
        }
    }
}

impl SetMinusEmptyRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusEmptyRight", "A \\\\ ∅", "A \\\\ ∅ = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A")
            }
            OutputLanguage::French => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Russian => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Spanish => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Arabic => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Japanese => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Korean => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
            OutputLanguage::Vietnamese => text("SetMinusEmptyRight", "A \\ ∅", "A \\ ∅ = A"),
        }
    }
}

impl SetMinusEmptyLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusEmptyLeft", "∅ \\\\ A", "∅ \\\\ A = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::French => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Russian => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Spanish => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Arabic => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Japanese => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Korean => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
            OutputLanguage::Vietnamese => text("SetMinusEmptyLeft", "∅ \\ A", "∅ \\ A = ∅"),
        }
    }
}

impl UnionCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionCommutative", "union commutative", "A ∪ B = B ∪ A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionCommutative", "并交换律", "A ∪ B = B ∪ A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("UnionCommutative", "聯集交換律", "A ∪ B = B ∪ A")
            }
            OutputLanguage::French => text(
                "UnionCommutative",
                "Commutativité de l'union",
                "A ∪ B = B ∪ A",
            ),
            OutputLanguage::Russian => text(
                "UnionCommutative",
                "Коммутативность объединения",
                "A ∪ B = B ∪ A",
            ),
            OutputLanguage::Spanish => text(
                "UnionCommutative",
                "Conmutatividad de unión",
                "A ∪ B = B ∪ A",
            ),
            OutputLanguage::Arabic => text("UnionCommutative", "تبادلية الاتحاد", "A ∪ B = B ∪ A"),
            OutputLanguage::Japanese => text("UnionCommutative", "和集合の可換性", "A ∪ B = B ∪ A"),
            OutputLanguage::Korean => text("UnionCommutative", "합집합 교환법칙", "A ∪ B = B ∪ A"),
            OutputLanguage::Vietnamese => {
                text("UnionCommutative", "Giao hoán của hợp", "A ∪ B = B ∪ A")
            }
        }
    }
}

impl IntersectCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectCommutative",
            "intersect commutative",
            "A ∩ B = B ∩ A",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectCommutative", "交交换律", "A ∩ B = B ∩ A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("IntersectCommutative", "交集交換律", "A ∩ B = B ∩ A")
            }
            OutputLanguage::French => text(
                "IntersectCommutative",
                "Commutativité de l'intersection",
                "A ∩ B = B ∩ A",
            ),
            OutputLanguage::Russian => text(
                "IntersectCommutative",
                "Коммутативность пересечения",
                "A ∩ B = B ∩ A",
            ),
            OutputLanguage::Spanish => text(
                "IntersectCommutative",
                "Conmutatividad de intersección",
                "A ∩ B = B ∩ A",
            ),
            OutputLanguage::Arabic => {
                text("IntersectCommutative", "تبادلية التقاطع", "A ∩ B = B ∩ A")
            }
            OutputLanguage::Japanese => {
                text("IntersectCommutative", "交差の可換性", "A ∩ B = B ∩ A")
            }
            OutputLanguage::Korean => {
                text("IntersectCommutative", "교집합 교환법칙", "A ∩ B = B ∩ A")
            }
            OutputLanguage::Vietnamese => text(
                "IntersectCommutative",
                "Giao hoán của giao",
                "A ∩ B = B ∩ A",
            ),
        }
    }
}

impl UnionIdempotentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionIdempotent", "A ∪ A", "A ∪ A = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionIdempotent", "A ∪ A", "A ∪ A = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::French => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Russian => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Spanish => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Arabic => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Japanese => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Korean => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
            OutputLanguage::Vietnamese => text("UnionIdempotent", "A ∪ A", "A ∪ A = A"),
        }
    }
}

impl IntersectIdempotentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectIdempotent", "A ∩ A", "A ∩ A = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectIdempotent", "A ∩ A", "A ∩ A = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::French => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Russian => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Spanish => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Arabic => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Japanese => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Korean => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
            OutputLanguage::Vietnamese => text("IntersectIdempotent", "A ∩ A", "A ∩ A = A"),
        }
    }
}

impl IntersectFromSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectFromSubset",
            "intersect from subset",
            "A ⊆ B gives A ∩ B = A",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectFromSubset", "由子集得交", "A ⊆ B 则 A ∩ B = A")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectFromSubset",
                "由子集關係得交集",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::French => text(
                "IntersectFromSubset",
                "Intersection depuis l'inclusion",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::Russian => text(
                "IntersectFromSubset",
                "Пересечение из включения",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::Spanish => text(
                "IntersectFromSubset",
                "Intersección desde inclusión",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::Arabic => text(
                "IntersectFromSubset",
                "تقاطع من احتواء جزئي",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::Japanese => {
                text("IntersectFromSubset", "包含から交差", "A ⊆ B ⇒ A ∩ B = A")
            }
            OutputLanguage::Korean => text(
                "IntersectFromSubset",
                "부분집합으로 교집합",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectFromSubset",
                "Giao từ tập con",
                "A ⊆ B ⇒ A ∩ B = A",
            ),
        }
    }
}

impl EmptySetFromNotNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromNotNonempty",
            "empty from not nonempty",
            "¬$is_nonempty_set(A) gives A = ∅",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromNotNonempty",
            "由非非空得空",
            "¬$is_nonempty_set(A) 则 A = ∅",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EmptySetFromNotNonempty",
                "由非非空得空集",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::French => text(
                "EmptySetFromNotNonempty",
                "Vide depuis la négation de non-vacuité",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Russian => text(
                "EmptySetFromNotNonempty",
                "Пустота из отрицания непустоты",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Spanish => text(
                "EmptySetFromNotNonempty",
                "Vacío desde negación de no vacuidad",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Arabic => text(
                "EmptySetFromNotNonempty",
                "الخلو من نفي عدم الخلو",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Japanese => text(
                "EmptySetFromNotNonempty",
                "非空性の否定から空集合",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Korean => text(
                "EmptySetFromNotNonempty",
                "비어 있지 않음의 부정으로 공집합",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
            OutputLanguage::Vietnamese => text(
                "EmptySetFromNotNonempty",
                "Rỗng từ phủ định không rỗng",
                "¬$is_nonempty_set(A) ⇒ A = ∅",
            ),
        }
    }
}

impl PowerSetFiniteSetSizeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowerSetFiniteSetSize",
            "|pow(A)|",
            "|pow(A)| = 2^|A| for finite A",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowerSetFiniteSetSize",
            "|pow(A)|",
            "对有限集 A，|pow(A)| = 2^|A|",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A|（A 有限時）",
            ),
            OutputLanguage::French => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A| pour A fini",
            ),
            OutputLanguage::Russian => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A| для конечного A",
            ),
            OutputLanguage::Spanish => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A| para A finito",
            ),
            OutputLanguage::Arabic => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A| لـ A المنتهية",
            ),
            OutputLanguage::Japanese => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A|（A が有限の場合）",
            ),
            OutputLanguage::Korean => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A|(A가 유한할 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "PowerSetFiniteSetSize",
                "|pow(A)|",
                "|pow(A)| = 2^|A| với A hữu hạn",
            ),
        }
    }
}

impl UnionAssociativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionAssociative",
            "union associative",
            "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionAssociative", "并结合律", "(A ∪ B) ∪ C = A ∪ (B ∪ C)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionAssociative",
                "聯集結合律",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::French => text(
                "UnionAssociative",
                "Associativité de l'union",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Russian => text(
                "UnionAssociative",
                "Ассоциативность объединения",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Spanish => text(
                "UnionAssociative",
                "Asociatividad de unión",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Arabic => text(
                "UnionAssociative",
                "تجميعية الاتحاد",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Japanese => text(
                "UnionAssociative",
                "和集合の結合律",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Korean => text(
                "UnionAssociative",
                "합집합 결합법칙",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionAssociative",
                "Kết hợp của hợp",
                "(A ∪ B) ∪ C = A ∪ (B ∪ C)",
            ),
        }
    }
}

impl IntersectAssociativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectAssociative",
            "intersect associative",
            "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectAssociative",
            "交结合律",
            "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectAssociative",
                "交集結合律",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::French => text(
                "IntersectAssociative",
                "Associativité de l'intersection",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Russian => text(
                "IntersectAssociative",
                "Ассоциативность пересечения",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Spanish => text(
                "IntersectAssociative",
                "Asociatividad de intersección",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Arabic => text(
                "IntersectAssociative",
                "تجميعية التقاطع",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Japanese => text(
                "IntersectAssociative",
                "交差の結合律",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Korean => text(
                "IntersectAssociative",
                "교집합 결합법칙",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectAssociative",
                "Kết hợp của giao",
                "(A ∩ B) ∩ C = A ∩ (B ∩ C)",
            ),
        }
    }
}

impl IntersectUnionDistributiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectUnionDistributive",
            "∩ distributes over ∪",
            "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectUnionDistributive",
            "∩ 对 ∪ 分配",
            "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectUnionDistributive",
                "交集對聯集的分配律",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::French => text(
                "IntersectUnionDistributive",
                "Distributivité de l'intersection sur l'union",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Russian => text(
                "IntersectUnionDistributive",
                "Дистрибутивность пересечения относительно объединения",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Spanish => text(
                "IntersectUnionDistributive",
                "Distributividad de intersección sobre unión",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Arabic => text(
                "IntersectUnionDistributive",
                "توزيعية التقاطع على الاتحاد",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Japanese => text(
                "IntersectUnionDistributive",
                "和集合に対する交差の分配律",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Korean => text(
                "IntersectUnionDistributive",
                "합집합에 대한 교집합 분배법칙",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectUnionDistributive",
                "Phân phối của giao trên hợp",
                "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)",
            ),
        }
    }
}

impl SetMinusUnionDeMorganBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusUnionDeMorgan",
            "\\ over ∪",
            "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusUnionDeMorgan",
            "差对并",
            "A \\\\ (B ∪ C) = (A \\\\ B) ∩ (A \\\\ C)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusUnionDeMorgan",
                "差集對聯集",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::French => text(
                "SetMinusUnionDeMorgan",
                "Différence sur union",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Russian => text(
                "SetMinusUnionDeMorgan",
                "Разность по объединению",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusUnionDeMorgan",
                "Diferencia sobre unión",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusUnionDeMorgan",
                "فرق على اتحاد",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusUnionDeMorgan",
                "和集合に対する差集合",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Korean => text(
                "SetMinusUnionDeMorgan",
                "합집합에 대한 차집합",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusUnionDeMorgan",
                "Hiệu trên hợp",
                "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)",
            ),
        }
    }
}

impl SetMinusIntersectDeMorganBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusIntersectDeMorgan",
            "\\ over ∩",
            "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusIntersectDeMorgan",
            "差对交",
            "A \\\\ (B ∩ C) = (A \\\\ B) ∪ (A \\\\ C)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusIntersectDeMorgan",
                "差集對交集",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::French => text(
                "SetMinusIntersectDeMorgan",
                "Différence sur intersection",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Russian => text(
                "SetMinusIntersectDeMorgan",
                "Разность по пересечению",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusIntersectDeMorgan",
                "Diferencia sobre intersección",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusIntersectDeMorgan",
                "فرق على تقاطع",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusIntersectDeMorgan",
                "交差に対する差集合",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Korean => text(
                "SetMinusIntersectDeMorgan",
                "교집합에 대한 차집합",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusIntersectDeMorgan",
                "Hiệu trên giao",
                "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)",
            ),
        }
    }
}

impl IntersectSetMinusSelfEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectSetMinusSelfEmpty",
            "A ∩ (A\\B)",
            "A ∩ (A \\ B) relates to emptiness / difference",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectSetMinusSelfEmpty",
            "A ∩ (A\\\\B)",
            "A ∩ (A \\\\ B) 与空集/差集相关",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "A ∩ (A \\ B) 的空集或差集關係",
            ),
            OutputLanguage::French => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "Relation de A ∩ (A \\ B) avec le vide ou la différence",
            ),
            OutputLanguage::Russian => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "Связь A ∩ (A \\ B) с пустотой или разностью",
            ),
            OutputLanguage::Spanish => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "Relación de A ∩ (A \\ B) con vacío o diferencia",
            ),
            OutputLanguage::Arabic => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "علاقة A ∩ (A \\ B) بالخلو أو الفرق",
            ),
            OutputLanguage::Japanese => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "A ∩ (A \\ B) の空集合または差集合との関係",
            ),
            OutputLanguage::Korean => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "A ∩ (A \\ B)의 공집합 또는 차집합 관계",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectSetMinusSelfEmpty",
                "A ∩ (A\\B)",
                "Quan hệ của A ∩ (A \\ B) với rỗng hoặc hiệu",
            ),
        }
    }
}

impl FiniteSetSumEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSumEmpty", "sum over ∅", "∑_{x∈∅} f(x) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSumEmpty", "空集上求和", "∑_{x∈∅} f(x) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FiniteSetSumEmpty", "空集合和", "∑_{x∈∅} f(x) = 0")
            }
            OutputLanguage::French => text("FiniteSetSumEmpty", "Somme sur ∅", "∑_{x∈∅} f(x) = 0"),
            OutputLanguage::Russian => text("FiniteSetSumEmpty", "Сумма по ∅", "∑_{x∈∅} f(x) = 0"),
            OutputLanguage::Spanish => {
                text("FiniteSetSumEmpty", "Suma sobre ∅", "∑_{x∈∅} f(x) = 0")
            }
            OutputLanguage::Arabic => text("FiniteSetSumEmpty", "مجموع على ∅", "∑_{x∈∅} f(x) = 0"),
            OutputLanguage::Japanese => text("FiniteSetSumEmpty", "∅ 上の和", "∑_{x∈∅} f(x) = 0"),
            OutputLanguage::Korean => text("FiniteSetSumEmpty", "∅ 위의 합", "∑_{x∈∅} f(x) = 0"),
            OutputLanguage::Vietnamese => {
                text("FiniteSetSumEmpty", "Tổng trên ∅", "∑_{x∈∅} f(x) = 0")
            }
        }
    }
}

impl FiniteSetProductEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetProductEmpty",
            "product over ∅",
            "∏_{x∈∅} f(x) = 1",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetProductEmpty", "空集上求积", "∏_{x∈∅} f(x) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FiniteSetProductEmpty", "空集合乘積", "∏_{x∈∅} f(x) = 1")
            }
            OutputLanguage::French => {
                text("FiniteSetProductEmpty", "Produit sur ∅", "∏_{x∈∅} f(x) = 1")
            }
            OutputLanguage::Russian => text(
                "FiniteSetProductEmpty",
                "Произведение по ∅",
                "∏_{x∈∅} f(x) = 1",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetProductEmpty",
                "Producto sobre ∅",
                "∏_{x∈∅} f(x) = 1",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetProductEmpty",
                "حاصل ضرب على ∅",
                "∏_{x∈∅} f(x) = 1",
            ),
            OutputLanguage::Japanese => {
                text("FiniteSetProductEmpty", "∅ 上の積", "∏_{x∈∅} f(x) = 1")
            }
            OutputLanguage::Korean => {
                text("FiniteSetProductEmpty", "∅ 위의 곱", "∏_{x∈∅} f(x) = 1")
            }
            OutputLanguage::Vietnamese => {
                text("FiniteSetProductEmpty", "Tích trên ∅", "∏_{x∈∅} f(x) = 1")
            }
        }
    }
}

impl FiniteSetReduceEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetReduceEmpty",
            "reduce over ∅",
            "reduce over the empty set is the unit",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetReduceEmpty", "空集上归约", "空集上的归约是单位元")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetReduceEmpty",
                "空集合折疊",
                "空集合上的折疊為單位元",
            ),
            OutputLanguage::French => text(
                "FiniteSetReduceEmpty",
                "Pli sur ∅",
                "Le pli sur l'ensemble vide est l'unité",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetReduceEmpty",
                "Свёртка по ∅",
                "Свёртка по пустому множеству равна единице",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetReduceEmpty",
                "Pliegue sobre ∅",
                "El pliegue sobre conjunto vacío es la unidad",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetReduceEmpty",
                "طي على ∅",
                "الطي على المجموعة الخالية هو الوحدة",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetReduceEmpty",
                "∅ 上の畳み込み",
                "空集合上の畳み込みは単位元です",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetReduceEmpty",
                "∅ 위의 접기",
                "공집합 위의 접기는 단위원입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetReduceEmpty",
                "Gấp trên ∅",
                "Gấp trên tập rỗng là đơn vị",
            ),
        }
    }
}

impl ReduceEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ReduceEmpty",
            "reduce empty",
            "reduce on an empty range is the unit",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReduceEmpty", "空归约", "空范围上的归约是单位元")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReduceEmpty", "空折疊", "空區間上的折疊為單位元")
            }
            OutputLanguage::French => text(
                "ReduceEmpty",
                "Pli vide",
                "Le pli sur un intervalle vide est l'unité",
            ),
            OutputLanguage::Russian => text(
                "ReduceEmpty",
                "Пустая свёртка",
                "Свёртка по пустому интервалу равна единице",
            ),
            OutputLanguage::Spanish => text(
                "ReduceEmpty",
                "Pliegue vacío",
                "El pliegue sobre intervalo vacío es la unidad",
            ),
            OutputLanguage::Arabic => {
                text("ReduceEmpty", "طي خالٍ", "الطي على فترة خالية هو الوحدة")
            }
            OutputLanguage::Japanese => text(
                "ReduceEmpty",
                "空の畳み込み",
                "空区間上の畳み込みは単位元です",
            ),
            OutputLanguage::Korean => {
                text("ReduceEmpty", "빈 접기", "빈 구간 위의 접기는 단위원입니다")
            }
            OutputLanguage::Vietnamese => {
                text("ReduceEmpty", "Gấp rỗng", "Gấp trên khoảng rỗng là đơn vị")
            }
        }
    }
}

impl SumEmptyRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumEmptyRange",
            "sum empty range",
            "∑ over an empty range is 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumEmptyRange", "空范围求和", "空范围求和为 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SumEmptyRange", "空區間和", "空區間上的 ∑ 為 0")
            }
            OutputLanguage::French => text(
                "SumEmptyRange",
                "Somme sur intervalle vide",
                "∑ sur un intervalle vide vaut 0",
            ),
            OutputLanguage::Russian => text(
                "SumEmptyRange",
                "Сумма по пустому интервалу",
                "∑ по пустому интервалу равно 0",
            ),
            OutputLanguage::Spanish => text(
                "SumEmptyRange",
                "Suma de intervalo vacío",
                "∑ sobre intervalo vacío es 0",
            ),
            OutputLanguage::Arabic => text(
                "SumEmptyRange",
                "مجموع فترة خالية",
                "∑ على فترة خالية يساوي 0",
            ),
            OutputLanguage::Japanese => {
                text("SumEmptyRange", "空区間の和", "空区間上の ∑ は 0 です")
            }
            OutputLanguage::Korean => {
                text("SumEmptyRange", "빈 구간의 합", "빈 구간 위의 ∑는 0입니다")
            }
            OutputLanguage::Vietnamese => text(
                "SumEmptyRange",
                "Tổng khoảng rỗng",
                "∑ trên khoảng rỗng bằng 0",
            ),
        }
    }
}

impl ProductEmptyRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductEmptyRange",
            "product empty range",
            "∏ over an empty range is 1",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductEmptyRange", "空范围求积", "空范围求积为 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ProductEmptyRange", "空區間乘積", "空區間上的 ∏ 為 1")
            }
            OutputLanguage::French => text(
                "ProductEmptyRange",
                "Produit sur intervalle vide",
                "∏ sur un intervalle vide vaut 1",
            ),
            OutputLanguage::Russian => text(
                "ProductEmptyRange",
                "Произведение по пустому интервалу",
                "∏ по пустому интервалу равно 1",
            ),
            OutputLanguage::Spanish => text(
                "ProductEmptyRange",
                "Producto de intervalo vacío",
                "∏ sobre intervalo vacío es 1",
            ),
            OutputLanguage::Arabic => text(
                "ProductEmptyRange",
                "حاصل ضرب فترة خالية",
                "∏ على فترة خالية يساوي 1",
            ),
            OutputLanguage::Japanese => {
                text("ProductEmptyRange", "空区間の積", "空区間上の ∏ は 1 です")
            }
            OutputLanguage::Korean => text(
                "ProductEmptyRange",
                "빈 구간의 곱",
                "빈 구간 위의 ∏는 1입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductEmptyRange",
                "Tích khoảng rỗng",
                "∏ trên khoảng rỗng bằng 1",
            ),
        }
    }
}

impl UnionAbsorptionFromSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionAbsorptionFromSubset",
            "union absorption",
            "A ⊆ B gives A ∪ B = B",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionAbsorptionFromSubset", "并吸收", "A ⊆ B 则 A ∪ B = B")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionAbsorptionFromSubset",
                "聯集吸收律",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::French => text(
                "UnionAbsorptionFromSubset",
                "Absorption de l'union",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Russian => text(
                "UnionAbsorptionFromSubset",
                "Поглощение объединения",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Spanish => text(
                "UnionAbsorptionFromSubset",
                "Absorción de unión",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Arabic => text(
                "UnionAbsorptionFromSubset",
                "امتصاص الاتحاد",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Japanese => text(
                "UnionAbsorptionFromSubset",
                "和集合の吸収律",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Korean => text(
                "UnionAbsorptionFromSubset",
                "합집합 흡수법칙",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionAbsorptionFromSubset",
                "Hấp thụ của hợp",
                "A ⊆ B ⇒ A ∪ B = B",
            ),
        }
    }
}

impl SetMinusRecoversSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusRecoversSubset",
            "difference recovers subset",
            "A ⊆ B gives B \\ (B \\ A) = A",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusRecoversSubset",
            "差集恢复子集",
            "A ⊆ B 则 B \\\\ (B \\\\ A) = A",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusRecoversSubset",
                "差集取回子集",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::French => text(
                "SetMinusRecoversSubset",
                "Différence retrouvant le sous-ensemble",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Russian => text(
                "SetMinusRecoversSubset",
                "Восстановление подмножества разностью",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusRecoversSubset",
                "Diferencia recupera subconjunto",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusRecoversSubset",
                "الفرق يستعيد المجموعة الجزئية",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusRecoversSubset",
                "差集合による部分集合の復元",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Korean => text(
                "SetMinusRecoversSubset",
                "차집합으로 부분집합 복원",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusRecoversSubset",
                "Hiệu khôi phục tập con",
                "A ⊆ B ⇒ B \\ (B \\ A) = A",
            ),
        }
    }
}

impl EmptySetFromSizeZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromSizeZero",
            "empty from size 0",
            "|A| = 0 gives A = ∅",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromSizeZero",
            "由大小 0 得空集",
            "|A| = 0 则 A = ∅",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("EmptySetFromSizeZero", "由大小零得空集", "|A| = 0 ⇒ A = ∅")
            }
            OutputLanguage::French => text(
                "EmptySetFromSizeZero",
                "Vide depuis la taille zéro",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Russian => text(
                "EmptySetFromSizeZero",
                "Пустота из нулевого размера",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Spanish => text(
                "EmptySetFromSizeZero",
                "Vacío desde tamaño cero",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Arabic => text(
                "EmptySetFromSizeZero",
                "الخلو من الحجم صفر",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Japanese => text(
                "EmptySetFromSizeZero",
                "大きさゼロから空集合",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Korean => text(
                "EmptySetFromSizeZero",
                "크기 0으로 공집합",
                "|A| = 0 ⇒ A = ∅",
            ),
            OutputLanguage::Vietnamese => text(
                "EmptySetFromSizeZero",
                "Rỗng từ kích thước không",
                "|A| = 0 ⇒ A = ∅",
            ),
        }
    }
}

impl CartProjFactorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CartProjFactor",
            "cart projection factor",
            "Projection recovers a Cartesian factor",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CartProjFactor",
            "cart projection factor",
            "Projection recovers a Cartesian factor",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("CartProjFactor", "笛卡兒積因子投影", "投影取回笛卡兒積因子")
            }
            OutputLanguage::French => text(
                "CartProjFactor",
                "Projection d'un facteur cartésien",
                "La projection retrouve un facteur cartésien",
            ),
            OutputLanguage::Russian => text(
                "CartProjFactor",
                "Проекция декартова множителя",
                "Проекция восстанавливает декартов множитель",
            ),
            OutputLanguage::Spanish => text(
                "CartProjFactor",
                "Proyección de factor cartesiano",
                "La proyección recupera un factor cartesiano",
            ),
            OutputLanguage::Arabic => text(
                "CartProjFactor",
                "إسقاط عامل ديكارتي",
                "الإسقاط يستعيد عاملًا ديكارتيًا",
            ),
            OutputLanguage::Japanese => text(
                "CartProjFactor",
                "直積因子の射影",
                "射影は直積の因子を復元します",
            ),
            OutputLanguage::Korean => text(
                "CartProjFactor",
                "데카르트 인자의 사영",
                "사영은 데카르트 곱의 인자를 복원합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "CartProjFactor",
                "Chiếu thừa số Descartes",
                "Phép chiếu khôi phục thừa số Descartes",
            ),
        }
    }
}

impl TupleComponentAtIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "TupleComponentAtIndex",
            "tuple component",
            "The i-th component of a tuple equals the stated entry",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "TupleComponentAtIndex",
            "元组分量",
            "元组的第 i 个分量等于所述分量",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "TupleComponentAtIndex",
                "元組分量",
                "元組第 i 個分量等於對應項目",
            ),
            OutputLanguage::French => text(
                "TupleComponentAtIndex",
                "Composante de tuple",
                "La i-ème composante d'un tuple est égale à l'entrée indiquée",
            ),
            OutputLanguage::Russian => text(
                "TupleComponentAtIndex",
                "Компонента кортежа",
                "i-я компонента кортежа равна указанному элементу",
            ),
            OutputLanguage::Spanish => text(
                "TupleComponentAtIndex",
                "Componente de tupla",
                "La componente i de una tupla equivale a la entrada indicada",
            ),
            OutputLanguage::Arabic => text(
                "TupleComponentAtIndex",
                "مكوّن صف",
                "المكوّن رقم i للصف يساوي العنصر المحدد",
            ),
            OutputLanguage::Japanese => text(
                "TupleComponentAtIndex",
                "タプルの成分",
                "タプルの第 i 成分は指定された要素に等しいです",
            ),
            OutputLanguage::Korean => text(
                "TupleComponentAtIndex",
                "튜플 성분",
                "튜플의 i번째 성분은 명시된 항목과 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "TupleComponentAtIndex",
                "Thành phần của bộ",
                "Thành phần thứ i của bộ bằng phần tử đã nêu",
            ),
        }
    }
}

impl FiniteSetSizeSetMinusBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSetMinus",
            "|A\\B|",
            "|A \\ B| = |A| − |A ∩ B| for finite sets",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSetMinus",
            "|A\\\\B|",
            "对有限集，|A \\\\ B| = |A| − |A ∩ B|",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B|（對有限集合）",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B| pour des ensembles finis",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B| для конечных множеств",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B| para conjuntos finitos",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B| للمجموعات المنتهية",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B|（有限集合について）",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B|(유한 집합에 대해)",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeSetMinus",
                "|A\\B|",
                "|A \\ B| = |A| − |A ∩ B| với các tập hữu hạn",
            ),
        }
    }
}

impl FiniteSetSizeUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeUnion",
            "|A∪B|",
            "|A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeUnion",
            "|A∪B|",
            "|A ∪ B| = |A| + |B| − |A ∩ B|",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeUnion",
                "|A∪B|",
                "|A ∪ B| = |A| + |B| − |A ∩ B|",
            ),
        }
    }
}

impl ClosedRangeSingletonListSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedRangeSingletonListSet",
            "closed range singleton",
            "{n..n} = {n}",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ClosedRangeSingletonListSet", "闭区间单点", "{n..n} = {n}")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedRangeSingletonListSet",
                "封閉區間單元素集合",
                "{n..n} = {n}",
            ),
            OutputLanguage::French => text(
                "ClosedRangeSingletonListSet",
                "Intervalle fermé singleton",
                "{n..n} = {n}",
            ),
            OutputLanguage::Russian => text(
                "ClosedRangeSingletonListSet",
                "Одноэлементный замкнутый интервал",
                "{n..n} = {n}",
            ),
            OutputLanguage::Spanish => text(
                "ClosedRangeSingletonListSet",
                "Intervalo cerrado unitario",
                "{n..n} = {n}",
            ),
            OutputLanguage::Arabic => text(
                "ClosedRangeSingletonListSet",
                "فترة مغلقة أحادية",
                "{n..n} = {n}",
            ),
            OutputLanguage::Japanese => text(
                "ClosedRangeSingletonListSet",
                "一要素の閉区間",
                "{n..n} = {n}",
            ),
            OutputLanguage::Korean => text(
                "ClosedRangeSingletonListSet",
                "한 원소 닫힌 구간",
                "{n..n} = {n}",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedRangeSingletonListSet",
                "Khoảng đóng đơn phần tử",
                "{n..n} = {n}",
            ),
        }
    }
}

impl SumSingleTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumSingleTerm",
            "sum one term",
            "∑ with a single term equals that term",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumSingleTerm", "单项目求和", "单项求和等于该项")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SumSingleTerm", "單項和", "單項 ∑ 等於該項")
            }
            OutputLanguage::French => text(
                "SumSingleTerm",
                "Somme à terme unique",
                "∑ à terme unique vaut ce terme",
            ),
            OutputLanguage::Russian => text(
                "SumSingleTerm",
                "Сумма одного члена",
                "∑ одного члена равно этому члену",
            ),
            OutputLanguage::Spanish => text(
                "SumSingleTerm",
                "Suma de un término",
                "∑ de un término equivale a ese término",
            ),
            OutputLanguage::Arabic => text(
                "SumSingleTerm",
                "مجموع حد واحد",
                "∑ بحد واحد يساوي ذلك الحد",
            ),
            OutputLanguage::Japanese => {
                text("SumSingleTerm", "一項の和", "一項の ∑ はその項に等しいです")
            }
            OutputLanguage::Korean => text(
                "SumSingleTerm",
                "한 항의 합",
                "한 항의 ∑는 그 항과 같습니다",
            ),
            OutputLanguage::Vietnamese => {
                text("SumSingleTerm", "Tổng một hạng", "∑ một hạng bằng hạng đó")
            }
        }
    }
}

impl ProductSingleTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductSingleTerm",
            "product one term",
            "∏ with a single term equals that term",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductSingleTerm", "单项目求积", "单项求积等于该项")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ProductSingleTerm", "單項乘積", "單項 ∏ 等於該項")
            }
            OutputLanguage::French => text(
                "ProductSingleTerm",
                "Produit à terme unique",
                "∏ à terme unique vaut ce terme",
            ),
            OutputLanguage::Russian => text(
                "ProductSingleTerm",
                "Произведение одного члена",
                "∏ одного члена равно этому члену",
            ),
            OutputLanguage::Spanish => text(
                "ProductSingleTerm",
                "Producto de un término",
                "∏ de un término equivale a ese término",
            ),
            OutputLanguage::Arabic => text(
                "ProductSingleTerm",
                "حاصل ضرب حد واحد",
                "∏ بحد واحد يساوي ذلك الحد",
            ),
            OutputLanguage::Japanese => text(
                "ProductSingleTerm",
                "一項の積",
                "一項の ∏ はその項に等しいです",
            ),
            OutputLanguage::Korean => text(
                "ProductSingleTerm",
                "한 항의 곱",
                "한 항의 ∏는 그 항과 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductSingleTerm",
                "Tích một hạng",
                "∏ một hạng bằng hạng đó",
            ),
        }
    }
}

impl ReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ReduceAddZeroEqualsSum",
            "reduce +0 as sum",
            "reduce with add and 0 equals a sum",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ReduceAddZeroEqualsSum",
            "归约 +0 即求和",
            "以加法与 0 归约等于求和",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ReduceAddZeroEqualsSum",
                "+0 折疊視為和",
                "加法以 0 為初值的折疊等於和",
            ),
            OutputLanguage::French => text(
                "ReduceAddZeroEqualsSum",
                "Pli +0 comme somme",
                "Le pli avec addition et 0 est égal à une somme",
            ),
            OutputLanguage::Russian => text(
                "ReduceAddZeroEqualsSum",
                "Свёртка +0 как сумма",
                "Свёртка со сложением и 0 равна сумме",
            ),
            OutputLanguage::Spanish => text(
                "ReduceAddZeroEqualsSum",
                "Pliegue +0 como suma",
                "El pliegue con suma y 0 equivale a una suma",
            ),
            OutputLanguage::Arabic => text(
                "ReduceAddZeroEqualsSum",
                "طي +0 كمجموع",
                "الطي بالجمع و0 يساوي مجموعًا",
            ),
            OutputLanguage::Japanese => text(
                "ReduceAddZeroEqualsSum",
                "和としての +0 畳み込み",
                "加算と 0 による畳み込みは和に等しいです",
            ),
            OutputLanguage::Korean => text(
                "ReduceAddZeroEqualsSum",
                "합으로서의 +0 접기",
                "덧셈과 0으로 접으면 합과 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ReduceAddZeroEqualsSum",
                "Gấp +0 là tổng",
                "Gấp với phép cộng và 0 bằng tổng",
            ),
        }
    }
}

impl FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetReduceAddZeroEqualsSum",
            "finite-set reduce as sum",
            "finite-set reduce with + and 0 equals a sum",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetReduceAddZeroEqualsSum",
            "有限集归约即求和",
            "有限集上以 + 与 0 归约等于求和",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "有限集合折疊視為和",
                "以 + 和 0 折疊有限集合等於和",
            ),
            OutputLanguage::French => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "Pli sur ensemble fini comme somme",
                "Un pli sur ensemble fini avec + et 0 est égal à une somme",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "Свёртка конечного множества как сумма",
                "Свёртка конечного множества с + и 0 равна сумме",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "Pliegue de conjunto finito como suma",
                "Un pliegue de conjunto finito con + y 0 equivale a una suma",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "طي مجموعة منتهية كمجموع",
                "طي مجموعة منتهية مع + و0 يساوي مجموعًا",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "和としての有限集合の畳み込み",
                "有限集合を + と 0 で畳み込むと和に等しいです",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "합으로서의 유한 집합 접기",
                "유한 집합을 +와 0으로 접으면 합과 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetReduceAddZeroEqualsSum",
                "Gấp tập hữu hạn là tổng",
                "Gấp tập hữu hạn với + và 0 bằng tổng",
            ),
        }
    }
}

impl PowOfLogInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b")
            }
            OutputLanguage::French => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Russian => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Spanish => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Arabic => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Japanese => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Korean => text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b"),
            OutputLanguage::Vietnamese => {
                text("PowOfLogInverse", "a^(log_a b)", "a^(log_a(b)) = b")
            }
        }
    }
}

impl UnionSetMinusDecompositionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionSetMinusDecomposition",
            "union\\difference",
            "A ∪ B = A ∪ (B \\ A)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionSetMinusDecomposition",
            "union\\\\difference",
            "A ∪ B = A ∪ (B \\\\ A)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionSetMinusDecomposition",
                "聯集與差集",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::French => text(
                "UnionSetMinusDecomposition",
                "Union et différence",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Russian => text(
                "UnionSetMinusDecomposition",
                "Объединение и разность",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Spanish => text(
                "UnionSetMinusDecomposition",
                "Unión y diferencia",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Arabic => text(
                "UnionSetMinusDecomposition",
                "اتحاد وفرق",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Japanese => text(
                "UnionSetMinusDecomposition",
                "和集合と差集合",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Korean => text(
                "UnionSetMinusDecomposition",
                "합집합과 차집합",
                "A ∪ B = A ∪ (B \\ A)",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionSetMinusDecomposition",
                "Hợp và hiệu",
                "A ∪ B = A ∪ (B \\ A)",
            ),
        }
    }
}

impl SetMinusIntersectSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusIntersectSelf",
            "A \\ (A∩B)",
            "A \\ (A ∩ B) = A \\ B",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusIntersectSelf",
            "A \\\\ (A∩B)",
            "A \\\\ (A ∩ B) = A \\\\ B",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::French => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Russian => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Korean => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusIntersectSelf",
                "A \\ (A∩B)",
                "A \\ (A ∩ B) = A \\ B",
            ),
        }
    }
}

impl ReOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::French => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Russian => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Spanish => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Arabic => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Japanese => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Korean => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
            OutputLanguage::Vietnamese => text("ReOfImaginaryUnit", "Re(i)", "Re(i) = 0"),
        }
    }
}

impl ImgOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::French => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Russian => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Spanish => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Arabic => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Japanese => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Korean => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
            OutputLanguage::Vietnamese => text("ImgOfImaginaryUnit", "Im(i)", "Im(i) = 1"),
        }
    }
}

impl ReOfRealEmbeddingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfRealEmbedding", "Re of real", "Re(embed(x)) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfRealEmbedding", "实嵌入的 Re", "Re(embed(x)) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReOfRealEmbedding", "實數的實部", "Re(embed(x)) = x")
            }
            OutputLanguage::French => text(
                "ReOfRealEmbedding",
                "Partie réelle d'un réel",
                "Re(embed(x)) = x",
            ),
            OutputLanguage::Russian => text(
                "ReOfRealEmbedding",
                "Действительная часть вещественного",
                "Re(embed(x)) = x",
            ),
            OutputLanguage::Spanish => text(
                "ReOfRealEmbedding",
                "Parte real de un real",
                "Re(embed(x)) = x",
            ),
            OutputLanguage::Arabic => text(
                "ReOfRealEmbedding",
                "الجزء الحقيقي لعدد حقيقي",
                "Re(embed(x)) = x",
            ),
            OutputLanguage::Japanese => text("ReOfRealEmbedding", "実数の実部", "Re(embed(x)) = x"),
            OutputLanguage::Korean => {
                text("ReOfRealEmbedding", "실수의 실수부", "Re(embed(x)) = x")
            }
            OutputLanguage::Vietnamese => text(
                "ReOfRealEmbedding",
                "Phần thực của số thực",
                "Re(embed(x)) = x",
            ),
        }
    }
}

impl ImgOfRealEmbeddingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfRealEmbedding", "Im of real", "Im(embed(x)) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfRealEmbedding", "实嵌入的 Im", "Im(embed(x)) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ImgOfRealEmbedding", "實數的虛部", "Im(embed(x)) = 0")
            }
            OutputLanguage::French => text(
                "ImgOfRealEmbedding",
                "Partie imaginaire d'un réel",
                "Im(embed(x)) = 0",
            ),
            OutputLanguage::Russian => text(
                "ImgOfRealEmbedding",
                "Мнимая часть вещественного",
                "Im(embed(x)) = 0",
            ),
            OutputLanguage::Spanish => text(
                "ImgOfRealEmbedding",
                "Parte imaginaria de un real",
                "Im(embed(x)) = 0",
            ),
            OutputLanguage::Arabic => text(
                "ImgOfRealEmbedding",
                "الجزء التخيلي لعدد حقيقي",
                "Im(embed(x)) = 0",
            ),
            OutputLanguage::Japanese => {
                text("ImgOfRealEmbedding", "実数の虚部", "Im(embed(x)) = 0")
            }
            OutputLanguage::Korean => {
                text("ImgOfRealEmbedding", "실수의 허수부", "Im(embed(x)) = 0")
            }
            OutputLanguage::Vietnamese => text(
                "ImgOfRealEmbedding",
                "Phần ảo của số thực",
                "Im(embed(x)) = 0",
            ),
        }
    }
}

impl ReOfRealPlusIBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::French => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Russian => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Spanish => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Arabic => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Japanese => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Korean => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
            OutputLanguage::Vietnamese => text("ReOfRealPlusI", "Re(x+i)", "Re(x + i) = x"),
        }
    }
}

impl ImgOfRealPlusIBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1")
            }
            OutputLanguage::French => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Russian => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Spanish => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Arabic => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Japanese => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Korean => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
            OutputLanguage::Vietnamese => text("ImgOfRealPlusI", "Im(x+i)", "Im(x + i) = 1"),
        }
    }
}

impl ComplexAbsOfImaginaryUnitBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1")
            }
            OutputLanguage::French => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Russian => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Spanish => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Arabic => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Japanese => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Korean => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
            OutputLanguage::Vietnamese => text("ComplexAbsOfImaginaryUnit", "|i|", "|i| = 1"),
        }
    }
}

impl ModNestedDivisibleAbsorptionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModNestedDivisibleAbsorption",
            "nested mod absorption",
            "If n | m then (a mod m) mod n = a mod n",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModNestedDivisibleAbsorption",
            "nested mod absorption",
            "If n | m then (a mod m) mod n = a mod n",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ModNestedDivisibleAbsorption",
                "巢狀模運算吸收律",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::French => text(
                "ModNestedDivisibleAbsorption",
                "Absorption de modulo imbriqué",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Russian => text(
                "ModNestedDivisibleAbsorption",
                "Поглощение вложенного модуля",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Spanish => text(
                "ModNestedDivisibleAbsorption",
                "Absorción de módulo anidado",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Arabic => text(
                "ModNestedDivisibleAbsorption",
                "امتصاص باقي القسمة المتداخل",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Japanese => text(
                "ModNestedDivisibleAbsorption",
                "入れ子の剰余の吸収",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Korean => text(
                "ModNestedDivisibleAbsorption",
                "중첩 나머지 흡수",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
            OutputLanguage::Vietnamese => text(
                "ModNestedDivisibleAbsorption",
                "Hấp thụ môđun lồng nhau",
                "n | m ⇒ (a mod m) mod n = a mod n",
            ),
        }
    }
}

impl SumSplitLastTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumSplitLastTerm",
            "sum split last",
            "Sum splits off its last term",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumSplitLastTerm", "求和拆末项", "求和可拆出最后一项")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SumSplitLastTerm", "和拆出末項", "和拆出最後一項")
            }
            OutputLanguage::French => text(
                "SumSplitLastTerm",
                "Séparation du dernier terme de la somme",
                "La somme sépare son dernier terme",
            ),
            OutputLanguage::Russian => text(
                "SumSplitLastTerm",
                "Отделение последнего члена суммы",
                "Сумма отделяет последний член",
            ),
            OutputLanguage::Spanish => text(
                "SumSplitLastTerm",
                "Separación del último término de suma",
                "La suma separa su último término",
            ),
            OutputLanguage::Arabic => text(
                "SumSplitLastTerm",
                "فصل الحد الأخير للمجموع",
                "المجموع يفصل حده الأخير",
            ),
            OutputLanguage::Japanese => text(
                "SumSplitLastTerm",
                "和の最後の項の分離",
                "和から最後の項を分離します",
            ),
            OutputLanguage::Korean => text(
                "SumSplitLastTerm",
                "합의 마지막 항 분리",
                "합에서 마지막 항을 분리합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SumSplitLastTerm",
                "Tổng tách hạng cuối",
                "Tổng tách hạng cuối",
            ),
        }
    }
}

impl ProductSplitLastTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductSplitLastTerm",
            "product split last",
            "Product splits off its last term",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductSplitLastTerm", "求积拆末项", "求积可拆出最后一项")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ProductSplitLastTerm", "乘積拆出末項", "乘積拆出最後一項")
            }
            OutputLanguage::French => text(
                "ProductSplitLastTerm",
                "Séparation du dernier terme du produit",
                "Le produit sépare son dernier terme",
            ),
            OutputLanguage::Russian => text(
                "ProductSplitLastTerm",
                "Отделение последнего множителя",
                "Произведение отделяет последний множитель",
            ),
            OutputLanguage::Spanish => text(
                "ProductSplitLastTerm",
                "Separación del último término del producto",
                "El producto separa su último término",
            ),
            OutputLanguage::Arabic => text(
                "ProductSplitLastTerm",
                "فصل الحد الأخير لحاصل الضرب",
                "حاصل الضرب يفصل حده الأخير",
            ),
            OutputLanguage::Japanese => text(
                "ProductSplitLastTerm",
                "積の最後の項の分離",
                "積から最後の項を分離します",
            ),
            OutputLanguage::Korean => text(
                "ProductSplitLastTerm",
                "곱의 마지막 항 분리",
                "곱에서 마지막 항을 분리합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductSplitLastTerm",
                "Tích tách hạng cuối",
                "Tích tách hạng cuối",
            ),
        }
    }
}

impl FiniteSetSumListExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumListExpansion",
            "finite-set sum expand",
            "Sum over a list-set expands to an explicit sum",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumListExpansion",
            "有限集求和展开",
            "列表集上的求和展开为显式和",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSumListExpansion",
                "有限集合和展開",
                "列表集合上的和展開為明確加總",
            ),
            OutputLanguage::French => text(
                "FiniteSetSumListExpansion",
                "Développement de somme sur ensemble fini",
                "La somme sur un ensemble liste se développe en somme explicite",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSumListExpansion",
                "Раскрытие суммы по конечному множеству",
                "Сумма по списочному множеству раскрывается в явную сумму",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSumListExpansion",
                "Expansión de suma de conjunto finito",
                "La suma sobre conjunto de lista se expande a suma explícita",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSumListExpansion",
                "توسيع مجموع مجموعة منتهية",
                "المجموع على مجموعة قائمة يتوسع إلى مجموع صريح",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSumListExpansion",
                "有限集合の和の展開",
                "リスト集合上の和を明示的な和に展開します",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSumListExpansion",
                "유한 집합 합 전개",
                "목록 집합 위의 합을 명시적 합으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSumListExpansion",
                "Khai triển tổng tập hữu hạn",
                "Tổng trên tập danh sách khai triển thành tổng tường minh",
            ),
        }
    }
}

impl FiniteSetProductListExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetProductListExpansion",
            "finite-set product expand",
            "Product over a list-set expands to an explicit product",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetProductListExpansion",
            "有限集求积展开",
            "列表集上的求积展开为显式积",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetProductListExpansion",
                "有限集合乘積展開",
                "列表集合上的乘積展開為明確乘積",
            ),
            OutputLanguage::French => text(
                "FiniteSetProductListExpansion",
                "Développement du produit sur ensemble fini",
                "Le produit sur un ensemble liste se développe en produit explicite",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetProductListExpansion",
                "Раскрытие произведения по конечному множеству",
                "Произведение по списочному множеству раскрывается в явное произведение",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetProductListExpansion",
                "Expansión de producto de conjunto finito",
                "El producto sobre conjunto de lista se expande a producto explícito",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetProductListExpansion",
                "توسيع حاصل ضرب مجموعة منتهية",
                "حاصل الضرب على مجموعة قائمة يتوسع إلى حاصل ضرب صريح",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetProductListExpansion",
                "有限集合の積の展開",
                "リスト集合上の積を明示的な積に展開します",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetProductListExpansion",
                "유한 집합 곱 전개",
                "목록 집합 위의 곱을 명시적 곱으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetProductListExpansion",
                "Khai triển tích tập hữu hạn",
                "Tích trên tập danh sách khai triển thành tích tường minh",
            ),
        }
    }
}

impl EulerEqualsExpOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)")
            }
            OutputLanguage::French => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Russian => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Spanish => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Arabic => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Japanese => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Korean => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
            OutputLanguage::Vietnamese => text("EulerEqualsExpOne", "e = exp(1)", "e = exp(1)"),
        }
    }
}

impl LnOfEulerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LnOfEuler", "ln(e)", "ln(e) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LnOfEuler", "ln(e)", "ln(e) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::French => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Russian => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Spanish => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Arabic => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Japanese => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Korean => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
            OutputLanguage::Vietnamese => text("LnOfEuler", "ln(e)", "ln(e) = 1"),
        }
    }
}

impl ReOfRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfReal", "Re(x) for real x", "Re(x) = x for real x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfReal", "实数的 Re", "对实数 x，Re(x) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReOfReal", "Re(x)（x 為實數）", "Re(x) = x（x 為實數）")
            }
            OutputLanguage::French => {
                text("ReOfReal", "Re(x) pour x réel", "Re(x) = x pour x réel")
            }
            OutputLanguage::Russian => text(
                "ReOfReal",
                "Re(x) для вещественного x",
                "Re(x) = x для вещественного x",
            ),
            OutputLanguage::Spanish => {
                text("ReOfReal", "Re(x) para x real", "Re(x) = x para x real")
            }
            OutputLanguage::Arabic => text(
                "ReOfReal",
                "Re(x) للعدد الحقيقي x",
                "Re(x) = x للعدد الحقيقي x",
            ),
            OutputLanguage::Japanese => {
                text("ReOfReal", "Re(x)（x は実数）", "Re(x) = x（x は実数）")
            }
            OutputLanguage::Korean => text("ReOfReal", "Re(x)(x는 실수)", "Re(x) = x(x는 실수)"),
            OutputLanguage::Vietnamese => {
                text("ReOfReal", "Re(x) với x thực", "Re(x) = x với x thực")
            }
        }
    }
}

impl ImgOfRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfReal", "Im(x) for real x", "Im(x) = 0 for real x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfReal", "实数的 Im", "对实数 x，Im(x) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ImgOfReal", "Im(x)（x 為實數）", "Im(x) = 0（x 為實數）")
            }
            OutputLanguage::French => {
                text("ImgOfReal", "Im(x) pour x réel", "Im(x) = 0 pour x réel")
            }
            OutputLanguage::Russian => text(
                "ImgOfReal",
                "Im(x) для вещественного x",
                "Im(x) = 0 для вещественного x",
            ),
            OutputLanguage::Spanish => {
                text("ImgOfReal", "Im(x) para x real", "Im(x) = 0 para x real")
            }
            OutputLanguage::Arabic => text(
                "ImgOfReal",
                "Im(x) للعدد الحقيقي x",
                "Im(x) = 0 للعدد الحقيقي x",
            ),
            OutputLanguage::Japanese => {
                text("ImgOfReal", "Im(x)（x は実数）", "Im(x) = 0（x は実数）")
            }
            OutputLanguage::Korean => text("ImgOfReal", "Im(x)(x는 실수)", "Im(x) = 0(x는 실수)"),
            OutputLanguage::Vietnamese => {
                text("ImgOfReal", "Im(x) với x thực", "Im(x) = 0 với x thực")
            }
        }
    }
}

impl ReOfRealPlusImagScaledBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::French => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Russian => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Spanish => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Arabic => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Japanese => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Korean => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
            OutputLanguage::Vietnamese => {
                text("ReOfRealPlusImagScaled", "Re(x+y·i)", "Re(x + y·i) = x")
            }
        }
    }
}

impl ImgOfRealPlusImagScaledBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::French => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Russian => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Spanish => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Arabic => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Japanese => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Korean => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
            OutputLanguage::Vietnamese => {
                text("ImgOfRealPlusImagScaled", "Im(x+y·i)", "Im(x + y·i) = y")
            }
        }
    }
}

impl ComplexAbsOfNonnegRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexAbsOfNonnegReal",
            "|x| for x≥0 real",
            "|embed(x)| = x for x ≥ 0",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexAbsOfNonnegReal",
            "非负实数模",
            "对 x ≥ 0，|embed(x)| = x",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ComplexAbsOfNonnegReal",
                "非負實數 x 的 |x|",
                "|embed(x)| = x（x ≥ 0 時）",
            ),
            OutputLanguage::French => text(
                "ComplexAbsOfNonnegReal",
                "|x| pour x réel non négatif",
                "|embed(x)| = x pour x ≥ 0",
            ),
            OutputLanguage::Russian => text(
                "ComplexAbsOfNonnegReal",
                "|x| для неотрицательного вещественного x",
                "|embed(x)| = x для x ≥ 0",
            ),
            OutputLanguage::Spanish => text(
                "ComplexAbsOfNonnegReal",
                "|x| para x real no negativo",
                "|embed(x)| = x para x ≥ 0",
            ),
            OutputLanguage::Arabic => text(
                "ComplexAbsOfNonnegReal",
                "|x| للعدد الحقيقي غير السالب x",
                "|embed(x)| = x لـ x ≥ 0",
            ),
            OutputLanguage::Japanese => text(
                "ComplexAbsOfNonnegReal",
                "非負実数 x の |x|",
                "|embed(x)| = x（x ≥ 0 の場合）",
            ),
            OutputLanguage::Korean => text(
                "ComplexAbsOfNonnegReal",
                "음이 아닌 실수 x의 |x|",
                "|embed(x)| = x(x ≥ 0일 때)",
            ),
            OutputLanguage::Vietnamese => text(
                "ComplexAbsOfNonnegReal",
                "|x| với x thực không âm",
                "|embed(x)| = x với x ≥ 0",
            ),
        }
    }
}

impl ComplexAbsOfImagScaledBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|")
            }
            OutputLanguage::French => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Russian => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Spanish => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Arabic => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Japanese => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Korean => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
            OutputLanguage::Vietnamese => text("ComplexAbsOfImagScaled", "|y·i|", "|y·i| = |y|"),
        }
    }
}

impl ClosedRangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedRangeLiteralExpansion",
            "closed range expand",
            "A numeric closed range expands to an explicit list set",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedRangeLiteralExpansion",
            "闭区间展开",
            "数值闭区间展开为显式列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedRangeLiteralExpansion",
                "封閉區間展開",
                "數值封閉區間展開為明確列表集合",
            ),
            OutputLanguage::French => text(
                "ClosedRangeLiteralExpansion",
                "Développement d'intervalle fermé",
                "Un intervalle numérique fermé se développe en ensemble liste explicite",
            ),
            OutputLanguage::Russian => text(
                "ClosedRangeLiteralExpansion",
                "Раскрытие замкнутого интервала",
                "Числовой замкнутый интервал раскрывается в явное списочное множество",
            ),
            OutputLanguage::Spanish => text(
                "ClosedRangeLiteralExpansion",
                "Expansión de intervalo cerrado",
                "Un intervalo numérico cerrado se expande a conjunto de lista explícito",
            ),
            OutputLanguage::Arabic => text(
                "ClosedRangeLiteralExpansion",
                "توسيع فترة مغلقة",
                "تتوسع الفترة العددية المغلقة إلى مجموعة قائمة صريحة",
            ),
            OutputLanguage::Japanese => text(
                "ClosedRangeLiteralExpansion",
                "閉区間の展開",
                "数値の閉区間を明示的なリスト集合に展開します",
            ),
            OutputLanguage::Korean => text(
                "ClosedRangeLiteralExpansion",
                "닫힌 구간 전개",
                "수치 닫힌 구간을 명시적 목록 집합으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedRangeLiteralExpansion",
                "Khai triển khoảng đóng",
                "Khoảng đóng dạng số khai triển thành tập danh sách tường minh",
            ),
        }
    }
}

impl RangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RangeLiteralExpansion",
            "range expand",
            "A numeric range expands to an explicit list set",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RangeLiteralExpansion",
            "区间展开",
            "数值区间展开为显式列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "RangeLiteralExpansion",
                "區間展開",
                "數值區間展開為明確列表集合",
            ),
            OutputLanguage::French => text(
                "RangeLiteralExpansion",
                "Développement d'intervalle",
                "Un intervalle numérique se développe en ensemble liste explicite",
            ),
            OutputLanguage::Russian => text(
                "RangeLiteralExpansion",
                "Раскрытие интервала",
                "Числовой интервал раскрывается в явное списочное множество",
            ),
            OutputLanguage::Spanish => text(
                "RangeLiteralExpansion",
                "Expansión de intervalo",
                "Un intervalo numérico se expande a conjunto de lista explícito",
            ),
            OutputLanguage::Arabic => text(
                "RangeLiteralExpansion",
                "توسيع فترة",
                "تتوسع الفترة العددية إلى مجموعة قائمة صريحة",
            ),
            OutputLanguage::Japanese => text(
                "RangeLiteralExpansion",
                "区間の展開",
                "数値区間を明示的なリスト集合に展開します",
            ),
            OutputLanguage::Korean => text(
                "RangeLiteralExpansion",
                "구간 전개",
                "수치 구간을 명시적 목록 집합으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "RangeLiteralExpansion",
                "Khai triển khoảng",
                "Khoảng dạng số khai triển thành tập danh sách tường minh",
            ),
        }
    }
}

impl PowerSetOfEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::French => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Russian => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Spanish => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Arabic => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Japanese => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Korean => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
            OutputLanguage::Vietnamese => text("PowerSetOfEmpty", "pow(∅)", "pow(∅) = {∅}"),
        }
    }
}

impl PowerSetOfSingletonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::French => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Russian => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Spanish => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Arabic => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Japanese => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Korean => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
            OutputLanguage::Vietnamese => {
                text("PowerSetOfSingleton", "pow({a})", "pow({a}) = {∅, {a}}")
            }
        }
    }
}

impl FamilyUnionOfEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::French => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Russian => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Spanish => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Arabic => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Japanese => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Korean => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
            OutputLanguage::Vietnamese => text("FamilyUnionOfEmpty", "⋃∅", "⋃∅ = ∅"),
        }
    }
}

impl CartWithEmptyFactorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::French => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Russian => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Spanish => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Arabic => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Japanese => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Korean => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
            OutputLanguage::Vietnamese => text("CartWithEmptyFactor", "A × ∅", "A × ∅ = ∅"),
        }
    }
}

impl UnionOverIntersectDistributiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionOverIntersectDistributive",
            "∪ over ∩",
            "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionOverIntersectDistributive",
            "∪ 对 ∩",
            "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionOverIntersectDistributive",
                "聯集對交集",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::French => text(
                "UnionOverIntersectDistributive",
                "Union sur intersection",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Russian => text(
                "UnionOverIntersectDistributive",
                "Объединение по пересечению",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Spanish => text(
                "UnionOverIntersectDistributive",
                "Unión sobre intersección",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Arabic => text(
                "UnionOverIntersectDistributive",
                "اتحاد على تقاطع",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Japanese => text(
                "UnionOverIntersectDistributive",
                "交差に対する和集合",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Korean => text(
                "UnionOverIntersectDistributive",
                "교집합에 대한 합집합",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionOverIntersectDistributive",
                "Hợp trên giao",
                "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)",
            ),
        }
    }
}

impl SetMinusChainToUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusChainToUnion",
            "chained difference",
            "A \\ B \\ C expands via union of removed sets",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusChainToUnion",
            "链式差集",
            "A \\\\ B \\\\ C 通过被去掉集合的并展开",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusChainToUnion",
                "連續差集",
                "A \\ B \\ C 以被移除集合之聯集展開",
            ),
            OutputLanguage::French => text(
                "SetMinusChainToUnion",
                "Différence en chaîne",
                "A \\ B \\ C se développe par l'union des ensembles retirés",
            ),
            OutputLanguage::Russian => text(
                "SetMinusChainToUnion",
                "Последовательная разность",
                "A \\ B \\ C раскрывается через объединение удаляемых множеств",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusChainToUnion",
                "Diferencia encadenada",
                "A \\ B \\ C se expande por la unión de conjuntos retirados",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusChainToUnion",
                "فرق متسلسل",
                "يتوسع A \\ B \\ C باتحاد المجموعات المحذوفة",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusChainToUnion",
                "連続する差集合",
                "A \\ B \\ C を除かれる集合の和で展開します",
            ),
            OutputLanguage::Korean => text(
                "SetMinusChainToUnion",
                "연속 차집합",
                "A \\ B \\ C를 제거되는 집합의 합집합으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusChainToUnion",
                "Hiệu liên tiếp",
                "A \\ B \\ C khai triển qua hợp các tập bị loại",
            ),
        }
    }
}

impl FnRangeOfConstantAnonymousFnBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FnRangeOfConstantAnonymousFn",
            "range of constant fn",
            "Range of a constant anonymous function is a singleton",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FnRangeOfConstantAnonymousFn",
            "常值函数值域",
            "常值匿名函数的值域是单点集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FnRangeOfConstantAnonymousFn",
                "常數函數值域",
                "常數匿名函數的值域為單元素集合",
            ),
            OutputLanguage::French => text(
                "FnRangeOfConstantAnonymousFn",
                "Image d'une fonction constante",
                "L'image d'une fonction anonyme constante est un singleton",
            ),
            OutputLanguage::Russian => text(
                "FnRangeOfConstantAnonymousFn",
                "Область значений постоянной функции",
                "Область значений постоянной анонимной функции является одноэлементным множеством",
            ),
            OutputLanguage::Spanish => text(
                "FnRangeOfConstantAnonymousFn",
                "Rango de función constante",
                "El rango de una función anónima constante es un conjunto unitario",
            ),
            OutputLanguage::Arabic => text(
                "FnRangeOfConstantAnonymousFn",
                "مدى دالة ثابتة",
                "مدى الدالة المجهولة الثابتة مجموعة أحادية",
            ),
            OutputLanguage::Japanese => text(
                "FnRangeOfConstantAnonymousFn",
                "定数関数の値域",
                "定数の無名関数の値域は一要素集合です",
            ),
            OutputLanguage::Korean => text(
                "FnRangeOfConstantAnonymousFn",
                "상수 함수의 치역",
                "상수 익명 함수의 치역은 한 원소 집합입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FnRangeOfConstantAnonymousFn",
                "Miền giá trị hàm hằng",
                "Miền giá trị hàm ẩn danh hằng là tập đơn phần tử",
            ),
        }
    }
}

impl SeqEqualsFnOnNPosBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SeqEqualsFnOnNPos",
            "seq as fn on N+",
            "A sequence equals its function on positive integers",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SeqEqualsFnOnNPos",
            "序列即 N+ 上函数",
            "序列等于其在正整数上的函数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SeqEqualsFnOnNPos",
                "N+ 上的序列函數",
                "序列等於其在正整數上的函數",
            ),
            OutputLanguage::French => text(
                "SeqEqualsFnOnNPos",
                "Suite comme fonction sur N+",
                "Une suite est égale à sa fonction sur les entiers positifs",
            ),
            OutputLanguage::Russian => text(
                "SeqEqualsFnOnNPos",
                "Последовательность как функция на N+",
                "Последовательность равна своей функции на положительных целых",
            ),
            OutputLanguage::Spanish => text(
                "SeqEqualsFnOnNPos",
                "Secuencia como función en N+",
                "Una secuencia equivale a su función en enteros positivos",
            ),
            OutputLanguage::Arabic => text(
                "SeqEqualsFnOnNPos",
                "متتالية كدالة على N+",
                "المتتالية تساوي دالتها على الأعداد الصحيحة الموجبة",
            ),
            OutputLanguage::Japanese => text(
                "SeqEqualsFnOnNPos",
                "N+ 上の関数としての列",
                "列は正の整数上の関数に等しいです",
            ),
            OutputLanguage::Korean => text(
                "SeqEqualsFnOnNPos",
                "N+ 위의 함수로서의 수열",
                "수열은 양의 정수 위의 함수와 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SeqEqualsFnOnNPos",
                "Dãy là hàm trên N+",
                "Dãy bằng hàm trên các số nguyên dương",
            ),
        }
    }
}

impl FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqEqualsFnOnOneBasedDomain",
            "finite seq as fn",
            "A finite sequence equals its function on indices 1 through its length",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqEqualsFnOnOneBasedDomain",
            "有限序列即函数",
            "有限序列等于其在 1 至长度上的函数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "有限序列視為函數",
                "有限序列等於在索引 1 至其長度上的函數",
            ),
            OutputLanguage::French => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "Suite finie comme fonction",
                "Une suite finie est égale à sa fonction sur les indices de 1 à sa longueur",
            ),
            OutputLanguage::Russian => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "Конечная последовательность как функция",
                "Конечная последовательность равна своей функции на индексах от 1 до её длины",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "Secuencia finita como función",
                "Una secuencia finita equivale a su función en índices de 1 hasta su longitud",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "متتالية منتهية كدالة",
                "المتتالية المنتهية تساوي دالتها على الفهارس من 1 إلى طولها",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "関数としての有限列",
                "有限列は添字 1 からその長さまでの関数に等しいです",
            ),
            OutputLanguage::Korean => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "함수로서의 유한 수열",
                "유한 수열은 인덱스 1부터 길이까지의 함수와 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSeqEqualsFnOnOneBasedDomain",
                "Dãy hữu hạn là hàm",
                "Dãy hữu hạn bằng hàm trên chỉ số từ 1 đến độ dài của nó",
            ),
        }
    }
}

impl IndexUnionEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IndexUnionEmptyIndex",
            "⋃_{i∈∅}",
            "Indexed union over an empty index is ∅",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IndexUnionEmptyIndex", "⋃_{i∈∅}", "空指标上的指标并是 ∅")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("IndexUnionEmptyIndex", "⋃_{i∈∅}", "空索引上的聯集為 ∅")
            }
            OutputLanguage::French => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "L'union sur un indice vide est ∅",
            ),
            OutputLanguage::Russian => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "Объединение по пустому индексу равно ∅",
            ),
            OutputLanguage::Spanish => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "La unión sobre índice vacío es ∅",
            ),
            OutputLanguage::Arabic => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "الاتحاد على فهرس خالٍ يساوي ∅",
            ),
            OutputLanguage::Japanese => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "空の添字集合上の和は ∅ です",
            ),
            OutputLanguage::Korean => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "빈 인덱스 위의 합집합은 ∅입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IndexUnionEmptyIndex",
                "⋃_{i∈∅}",
                "Hợp theo chỉ số rỗng bằng ∅",
            ),
        }
    }
}

impl IndexIntersectEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "Indexed intersect over an empty index is the ambient universe convention used by Litex")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IndexIntersectEmptyIndex",
            "⋂_{i∈∅}",
            "空指标上的指标交按 Litex 约定为全空间",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        ,
            OutputLanguage::ChineseTraditional => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "空索引上的交集採用 Litex 的背景全集約定")
    },
            OutputLanguage::French => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "L'intersection sur un indice vide suit la convention d'univers ambiant de Litex")
    },
            OutputLanguage::Russian => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "Пересечение по пустому индексу соответствует соглашению Litex об окружающем универсуме")
    },
            OutputLanguage::Spanish => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "La intersección sobre índice vacío sigue la convención de universo ambiente de Litex")
    },
            OutputLanguage::Arabic => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "التقاطع على فهرس خالٍ يتبع اصطلاح الكون المحيط في Litex")
    },
            OutputLanguage::Japanese => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "空の添字集合上の交差は Litex の周囲の全体集合の規約に従います")
    },
            OutputLanguage::Korean => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "빈 인덱스 위의 교집합은 Litex의 주변 전체집합 규약을 따릅니다")
    },
            OutputLanguage::Vietnamese => {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "Giao theo chỉ số rỗng dùng quy ước tập vũ trụ bao quanh của Litex")
    },
}
    }
}

impl IndexCartEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IndexCartEmptyIndex",
            "indexed cart empty",
            "Indexed Cartesian product over an empty index is a unit",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IndexCartEmptyIndex",
            "空指标笛卡尔积",
            "空指标上的指标笛卡尔积是单位",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IndexCartEmptyIndex",
                "空索引笛卡兒積",
                "空索引上的帶索引笛卡兒積為單位元",
            ),
            OutputLanguage::French => text(
                "IndexCartEmptyIndex",
                "Produit cartésien à indice vide",
                "Le produit cartésien indexé sur un indice vide est une unité",
            ),
            OutputLanguage::Russian => text(
                "IndexCartEmptyIndex",
                "Декартово произведение по пустому индексу",
                "Индексированное декартово произведение по пустому индексу является единицей",
            ),
            OutputLanguage::Spanish => text(
                "IndexCartEmptyIndex",
                "Producto cartesiano de índice vacío",
                "El producto cartesiano indexado sobre índice vacío es una unidad",
            ),
            OutputLanguage::Arabic => text(
                "IndexCartEmptyIndex",
                "حاصل ضرب ديكارتي بفهرس خالٍ",
                "حاصل الضرب الديكارتي المفهرس على فهرس خالٍ هو وحدة",
            ),
            OutputLanguage::Japanese => text(
                "IndexCartEmptyIndex",
                "空の添字集合の直積",
                "空の添字集合上の直積は単位です",
            ),
            OutputLanguage::Korean => text(
                "IndexCartEmptyIndex",
                "빈 인덱스 데카르트 곱",
                "빈 인덱스 위의 데카르트 곱은 단위원입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IndexCartEmptyIndex",
                "Tích Descartes chỉ số rỗng",
                "Tích Descartes theo chỉ số rỗng là đơn vị",
            ),
        }
    }
}

impl IndexUnionSingletonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IndexUnionSingleton",
            "⋃_{i∈{a}}",
            "Indexed union over a singleton index is the single set",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IndexUnionSingleton",
            "⋃_{i∈{a}}",
            "单点指标上的指标并是那个集合",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "單元素索引上的聯集等於該集合",
            ),
            OutputLanguage::French => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "L'union sur un indice singleton est cet ensemble unique",
            ),
            OutputLanguage::Russian => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "Объединение по одноэлементному индексу равно единственному множеству",
            ),
            OutputLanguage::Spanish => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "La unión sobre índice unitario es el único conjunto",
            ),
            OutputLanguage::Arabic => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "الاتحاد على فهرس أحادي يساوي المجموعة الوحيدة",
            ),
            OutputLanguage::Japanese => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "一要素の添字集合上の和はその集合です",
            ),
            OutputLanguage::Korean => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "한 원소 인덱스 위의 합집합은 그 집합입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IndexUnionSingleton",
                "⋃_{i∈{a}}",
                "Hợp theo chỉ số đơn phần tử là tập duy nhất đó",
            ),
        }
    }
}

impl FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroEqualsFnOnEmpty",
            "empty finite seq",
            "The length-0 finite sequence equals the function on the empty range",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroEqualsFnOnEmpty",
            "空有限序列",
            "长度为 0 的有限序列等于空区间上的函数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "空有限序列",
                "長度為零的有限序列等於空區間上的函數",
            ),
            OutputLanguage::French => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "Suite finie vide",
                "La suite finie de longueur zéro est égale à la fonction sur l'intervalle vide",
            ),
            OutputLanguage::Russian => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "Пустая конечная последовательность",
                "Конечная последовательность длины ноль равна функции на пустом интервале",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "Secuencia finita vacía",
                "La secuencia finita de longitud cero equivale a la función en rango vacío",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "متتالية منتهية خالية",
                "المتتالية المنتهية بطول صفر تساوي الدالة على الفترة الخالية",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "空の有限列",
                "長さゼロの有限列は空区間上の関数に等しいです",
            ),
            OutputLanguage::Korean => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "빈 유한 수열",
                "길이 0인 유한 수열은 빈 구간 위의 함수와 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSeqZeroEqualsFnOnEmpty",
                "Dãy hữu hạn rỗng",
                "Dãy hữu hạn độ dài không bằng hàm trên khoảng rỗng",
            ),
        }
    }
}

impl SetBuilderObviouslyEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetBuilderObviouslyEmpty",
            "empty set-builder",
            "A contradictory set-builder equals ∅",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetBuilderObviouslyEmpty",
            "空集合构造器",
            "矛盾的集合构造器等于 ∅",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetBuilderObviouslyEmpty",
                "空集合構造",
                "條件矛盾的集合構造等於 ∅",
            ),
            OutputLanguage::French => text(
                "SetBuilderObviouslyEmpty",
                "Compréhension vide",
                "Un ensemble en compréhension contradictoire est égal à ∅",
            ),
            OutputLanguage::Russian => text(
                "SetBuilderObviouslyEmpty",
                "Пустое множество по условию",
                "Множество с противоречивым условием равно ∅",
            ),
            OutputLanguage::Spanish => text(
                "SetBuilderObviouslyEmpty",
                "Comprensión vacía",
                "Un conjunto por comprensión contradictorio es igual a ∅",
            ),
            OutputLanguage::Arabic => text(
                "SetBuilderObviouslyEmpty",
                "بناء مجموعة خالية",
                "المجموعة المبنية بشرط متناقض تساوي ∅",
            ),
            OutputLanguage::Japanese => text(
                "SetBuilderObviouslyEmpty",
                "空の内包表記集合",
                "矛盾する条件の内包表記集合は ∅ です",
            ),
            OutputLanguage::Korean => text(
                "SetBuilderObviouslyEmpty",
                "빈 조건제시 집합",
                "조건이 모순인 조건제시 집합은 ∅입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SetBuilderObviouslyEmpty",
                "Tập dựng rỗng",
                "Tập dựng có điều kiện mâu thuẫn bằng ∅",
            ),
        }
    }
}

impl ComplexAbsSquaredOfRectFormBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ComplexAbsSquaredOfRectForm",
            "|x+y i|²",
            "|x + y·i|² = x² + y²",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ComplexAbsSquaredOfRectForm",
            "|x+y i|²",
            "|x + y·i|² = x² + y²",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::French => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Russian => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Spanish => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Arabic => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Japanese => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Korean => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
            OutputLanguage::Vietnamese => text(
                "ComplexAbsSquaredOfRectForm",
                "|x+y i|²",
                "|x + y·i|² = x² + y²",
            ),
        }
    }
}

impl ExpOfSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)")
            }
            OutputLanguage::French => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Russian => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Spanish => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Arabic => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Japanese => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Korean => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
            OutputLanguage::Vietnamese => text("ExpOfSum", "exp(x+y)", "exp(x+y) = exp(x)·exp(y)"),
        }
    }
}

impl LogBasePowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogBasePower",
            "log_(a^n)(b)",
            "log_(a^n)(b) = (1/n)·log_a(b)",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogBasePower",
            "log_(a^n)(b)",
            "log_(a^n)(b) = (1/n)·log_a(b)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::French => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Russian => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Spanish => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Arabic => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Japanese => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Korean => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
            OutputLanguage::Vietnamese => text(
                "LogBasePower",
                "log_(a^n)(b)",
                "log_(a^n)(b) = (1/n)·log_a(b)",
            ),
        }
    }
}

impl ReOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ReOfProduct",
            "Re(z·w)",
            "Re(z·w) expands from rectangular forms",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfProduct", "Re(z·w)", "Re(z·w) 由直角坐标形式展开")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ReOfProduct", "Re(z·w)", "由直角形式展開 Re(z·w)")
            }
            OutputLanguage::French => text(
                "ReOfProduct",
                "Re(z·w)",
                "Re(z·w) se développe depuis les formes cartésiennes",
            ),
            OutputLanguage::Russian => text(
                "ReOfProduct",
                "Re(z·w)",
                "Re(z·w) раскрывается из прямоугольных форм",
            ),
            OutputLanguage::Spanish => text(
                "ReOfProduct",
                "Re(z·w)",
                "Re(z·w) se expande desde formas cartesianas",
            ),
            OutputLanguage::Arabic => text(
                "ReOfProduct",
                "Re(z·w)",
                "يتوسع Re(z·w) من الأشكال الديكارتية",
            ),
            OutputLanguage::Japanese => text(
                "ReOfProduct",
                "Re(z·w)",
                "直交形式から Re(z·w) を展開します",
            ),
            OutputLanguage::Korean => text(
                "ReOfProduct",
                "Re(z·w)",
                "직교 형식에서 Re(z·w)를 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ReOfProduct",
                "Re(z·w)",
                "Re(z·w) khai triển từ dạng tọa độ chữ nhật",
            ),
        }
    }
}

impl ImgOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ImgOfProduct",
            "Im(z·w)",
            "Im(z·w) expands from rectangular forms",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfProduct", "Img(z·w)", "Img(z·w) 由直角坐标形式展开")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ImgOfProduct", "Im(z·w)", "由直角形式展開 Im(z·w)")
            }
            OutputLanguage::French => text(
                "ImgOfProduct",
                "Im(z·w)",
                "Im(z·w) se développe depuis les formes cartésiennes",
            ),
            OutputLanguage::Russian => text(
                "ImgOfProduct",
                "Im(z·w)",
                "Im(z·w) раскрывается из прямоугольных форм",
            ),
            OutputLanguage::Spanish => text(
                "ImgOfProduct",
                "Im(z·w)",
                "Im(z·w) se expande desde formas cartesianas",
            ),
            OutputLanguage::Arabic => text(
                "ImgOfProduct",
                "Im(z·w)",
                "يتوسع Im(z·w) من الأشكال الديكارتية",
            ),
            OutputLanguage::Japanese => text(
                "ImgOfProduct",
                "Im(z·w)",
                "直交形式から Im(z·w) を展開します",
            ),
            OutputLanguage::Korean => text(
                "ImgOfProduct",
                "Im(z·w)",
                "직교 형식에서 Im(z·w)를 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ImgOfProduct",
                "Im(z·w)",
                "Im(z·w) khai triển từ dạng tọa độ chữ nhật",
            ),
        }
    }
}

impl SinOfSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SinOfSum",
            "sin(x+y)",
            "sin(x+y) = sin x cos y + cos x sin y",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SinOfSum",
            "sin(x+y)",
            "sin(x+y) = sin x cos y + cos x sin y",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::French => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Russian => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Spanish => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Arabic => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Japanese => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Korean => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
            OutputLanguage::Vietnamese => text(
                "SinOfSum",
                "sin(x+y)",
                "sin(x+y) = sin x cos y + cos x sin y",
            ),
        }
    }
}

impl CosOfSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CosOfSum",
            "cos(x+y)",
            "cos(x+y) = cos x cos y − sin x sin y",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CosOfSum",
            "cos(x+y)",
            "cos(x+y) = cos x cos y − sin x sin y",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::French => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Russian => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Spanish => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Arabic => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Japanese => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Korean => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
            OutputLanguage::Vietnamese => text(
                "CosOfSum",
                "cos(x+y)",
                "cos(x+y) = cos x cos y − sin x sin y",
            ),
        }
    }
}

impl ReduceSingleTermWithAddZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ReduceSingleTermWithAddZero",
            "reduce one term",
            "Reduce with a single term and +0 equals that term",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ReduceSingleTermWithAddZero",
            "单项归约",
            "单项并以 +0 归约等于该项",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ReduceSingleTermWithAddZero",
                "單項折疊",
                "單項且以 +0 折疊時等於該項",
            ),
            OutputLanguage::French => text(
                "ReduceSingleTermWithAddZero",
                "Pli à terme unique",
                "Un pli à terme unique avec +0 est égal à ce terme",
            ),
            OutputLanguage::Russian => text(
                "ReduceSingleTermWithAddZero",
                "Свёртка одного члена",
                "Свёртка одного члена с +0 равна этому члену",
            ),
            OutputLanguage::Spanish => text(
                "ReduceSingleTermWithAddZero",
                "Pliegue de un término",
                "Un pliegue de un término con +0 equivale a ese término",
            ),
            OutputLanguage::Arabic => text(
                "ReduceSingleTermWithAddZero",
                "طي حد واحد",
                "طي حد واحد مع +0 يساوي ذلك الحد",
            ),
            OutputLanguage::Japanese => text(
                "ReduceSingleTermWithAddZero",
                "一項の畳み込み",
                "一項を +0 で畳み込むとその項に等しいです",
            ),
            OutputLanguage::Korean => text(
                "ReduceSingleTermWithAddZero",
                "한 항 접기",
                "한 항을 +0으로 접으면 그 항과 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ReduceSingleTermWithAddZero",
                "Gấp một hạng",
                "Gấp một hạng với +0 bằng hạng đó",
            ),
        }
    }
}

impl FiniteSetSumFubiniSwapBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumFubiniSwap",
            "Fubini swap for sums",
            "Finite double sums may swap summation order",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumFubiniSwap",
            "有限双重和 Fubini",
            "有限双重和可交换求和次序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSumFubiniSwap",
                "求和的 Fubini 交換",
                "有限二重和可交換求和順序",
            ),
            OutputLanguage::French => text(
                "FiniteSetSumFubiniSwap",
                "Échange de Fubini pour les sommes",
                "Les sommes doubles finies permettent d'échanger l'ordre de sommation",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSumFubiniSwap",
                "Перестановка сумм по Фубини",
                "В конечных двойных суммах можно менять порядок суммирования",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSumFubiniSwap",
                "Intercambio de Fubini para sumas",
                "Las sumas dobles finitas permiten intercambiar el orden de suma",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSumFubiniSwap",
                "تبديل فوبيني للمجاميع",
                "يمكن تبديل ترتيب الجمع في المجاميع المزدوجة المنتهية",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSumFubiniSwap",
                "総和のフビニの交換",
                "有限二重和では総和の順序を交換できます",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSumFubiniSwap",
                "합의 푸비니 교환",
                "유한 이중 합은 합산 순서를 바꿀 수 있습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSumFubiniSwap",
                "Đổi tổng theo Fubini",
                "Tổng kép hữu hạn có thể đổi thứ tự lấy tổng",
            ),
        }
    }
}

impl FiniteSetSumOverCartesianProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumOverCartesianProduct",
            "sum over A×B",
            "Sum over a Cartesian product expands as an iterated sum",
        )
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSumOverCartesianProduct",
            "A×B 上求和",
            "笛卡尔积上的求和展开为迭代和",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSumOverCartesianProduct",
                "A×B 上的和",
                "笛卡兒積上的和展開為疊代和",
            ),
            OutputLanguage::French => text(
                "FiniteSetSumOverCartesianProduct",
                "Somme sur A×B",
                "La somme sur un produit cartésien se développe en somme itérée",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSumOverCartesianProduct",
                "Сумма по A×B",
                "Сумма по декартову произведению раскрывается в повторную сумму",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSumOverCartesianProduct",
                "Suma sobre A×B",
                "La suma sobre producto cartesiano se expande a suma iterada",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSumOverCartesianProduct",
                "مجموع على A×B",
                "المجموع على حاصل ضرب ديكارتي يتوسع إلى مجموع متكرر",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSumOverCartesianProduct",
                "A×B 上の和",
                "直積上の和を反復和に展開します",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSumOverCartesianProduct",
                "A×B 위의 합",
                "데카르트 곱 위의 합을 반복 합으로 전개합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSumOverCartesianProduct",
                "Tổng trên A×B",
                "Tổng trên tích Descartes khai triển thành tổng lặp",
            ),
        }
    }
}

impl SinOfZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SinOfZero", "sin 0", "sin(0) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinOfZero", "sin 0", "sin(0) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::French => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Russian => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Spanish => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Arabic => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Japanese => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Korean => text("SinOfZero", "sin 0", "sin(0) = 0"),
            OutputLanguage::Vietnamese => text("SinOfZero", "sin 0", "sin(0) = 0"),
        }
    }
}

impl CosOfZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CosOfZero", "cos 0", "cos(0) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CosOfZero", "cos 0", "cos(0) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::French => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Russian => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Spanish => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Arabic => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Japanese => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Korean => text("CosOfZero", "cos 0", "cos(0) = 1"),
            OutputLanguage::Vietnamese => text("CosOfZero", "cos 0", "cos(0) = 1"),
        }
    }
}

impl TanOfZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("TanOfZero", "tan 0", "tan(0) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("TanOfZero", "tan 0", "tan(0) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::French => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Russian => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Spanish => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Arabic => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Japanese => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Korean => text("TanOfZero", "tan 0", "tan(0) = 0"),
            OutputLanguage::Vietnamese => text("TanOfZero", "tan 0", "tan(0) = 0"),
        }
    }
}

impl SinOfHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::French => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Russian => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Spanish => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Arabic => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Japanese => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Korean => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
            OutputLanguage::Vietnamese => text("SinOfHalfPi", "sin(π/2)", "sin(π/2) = 1"),
        }
    }
}

impl CosOfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CosOfPi", "cos(π)", "cos(π) = -1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CosOfPi", "cos(π)", "cos(π) = -1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::French => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Russian => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Spanish => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Arabic => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Japanese => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Korean => text("CosOfPi", "cos(π)", "cos(π) = -1"),
            OutputLanguage::Vietnamese => text("CosOfPi", "cos(π)", "cos(π) = -1"),
        }
    }
}

impl SinOfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SinOfPi", "sin(π)", "sin(π) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinOfPi", "sin(π)", "sin(π) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::French => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Russian => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Spanish => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Arabic => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Japanese => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Korean => text("SinOfPi", "sin(π)", "sin(π) = 0"),
            OutputLanguage::Vietnamese => text("SinOfPi", "sin(π)", "sin(π) = 0"),
        }
    }
}

impl CotOfHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::French => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Russian => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Spanish => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Arabic => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Japanese => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Korean => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
            OutputLanguage::Vietnamese => text("CotOfHalfPi", "cot(π/2)", "cot(π/2) = 0"),
        }
    }
}

impl PythagoreanIdentityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::French => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Russian => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Spanish => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Arabic => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Japanese => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Korean => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
            OutputLanguage::Vietnamese => {
                text("PythagoreanIdentity", "sin²+cos²", "sin²(x) + cos²(x) = 1")
            }
        }
    }
}

impl FamilyUnionOfSingletonBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FamilyUnionOfSingleton",
                "Union of a singleton family",
                "The union of a singleton family of sets is its member.",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FamilyUnionOfSingleton",
                "單元素集合族的聯集",
                "單元素集合族的聯集等於其成員。",
            ),
            OutputLanguage::French => text(
                "FamilyUnionOfSingleton",
                "Union d'une famille singleton",
                "L'union d'une famille singleton d'ensembles est son membre.",
            ),
            OutputLanguage::Russian => text(
                "FamilyUnionOfSingleton",
                "Объединение одноэлементного семейства",
                "Объединение одноэлементного семейства множеств равно его элементу.",
            ),
            OutputLanguage::Spanish => text(
                "FamilyUnionOfSingleton",
                "Unión de familia unitaria",
                "La unión de una familia unitaria de conjuntos es su miembro.",
            ),
            OutputLanguage::Arabic => text(
                "FamilyUnionOfSingleton",
                "اتحاد عائلة أحادية",
                "اتحاد عائلة أحادية من المجموعات يساوي عنصرها.",
            ),
            OutputLanguage::Japanese => text(
                "FamilyUnionOfSingleton",
                "一要素の集合族の和",
                "一要素の集合族の和はその要素です。",
            ),
            OutputLanguage::Korean => text(
                "FamilyUnionOfSingleton",
                "한 원소 집합족의 합집합",
                "한 원소 집합족의 합집합은 그 원소입니다.",
            ),
            OutputLanguage::Vietnamese => text(
                "FamilyUnionOfSingleton",
                "Hợp của họ đơn phần tử",
                "Hợp của họ tập hợp đơn phần tử là phần tử của nó.",
            ),

            OutputLanguage::Chinese => text(
                "FamilyUnionOfSingleton",
                "单元素集合族的并",
                "只包含集合 A 的集合族，其并集等于 A。",
            ),
        }
    }
}

impl FamilyUnionOfPowerSetBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FamilyUnionOfPowerSet",
                "Union of a power set",
                "The union of the power set of a set is that set.",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FamilyUnionOfPowerSet",
                "冪集的聯集",
                "集合冪集中所有集合的聯集等於該集合。",
            ),
            OutputLanguage::French => text(
                "FamilyUnionOfPowerSet",
                "Union de l'ensemble des parties",
                "L'union de l'ensemble des parties d'un ensemble est cet ensemble.",
            ),
            OutputLanguage::Russian => text(
                "FamilyUnionOfPowerSet",
                "Объединение множества подмножеств",
                "Объединение множества подмножеств множества равно этому множеству.",
            ),
            OutputLanguage::Spanish => text(
                "FamilyUnionOfPowerSet",
                "Unión de conjunto potencia",
                "La unión del conjunto potencia de un conjunto es ese conjunto.",
            ),
            OutputLanguage::Arabic => text(
                "FamilyUnionOfPowerSet",
                "اتحاد مجموعة القوى",
                "اتحاد مجموعة القوى لمجموعة يساوي تلك المجموعة.",
            ),
            OutputLanguage::Japanese => text(
                "FamilyUnionOfPowerSet",
                "べき集合の和",
                "集合のべき集合の和はその集合です。",
            ),
            OutputLanguage::Korean => text(
                "FamilyUnionOfPowerSet",
                "멱집합의 합집합",
                "집합의 멱집합의 합집합은 그 집합입니다.",
            ),
            OutputLanguage::Vietnamese => text(
                "FamilyUnionOfPowerSet",
                "Hợp của tập lũy thừa",
                "Hợp của tập lũy thừa của một tập là chính tập đó.",
            ),

            OutputLanguage::Chinese => text(
                "FamilyUnionOfPowerSet",
                "幂集的并",
                "集合 A 的幂集中所有集合的并等于 A。",
            ),
        }
    }
}
