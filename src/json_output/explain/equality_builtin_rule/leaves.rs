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
        text("SinArcsinLeftInverse", "sin ∘ arcsin", "sin(arcsin(x)) = x on the arcsin range")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinArcsinLeftInverse", "sin ∘ arcsin", "在 arcsin 值域上，sin(arcsin(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl CosArccosLeftInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CosArccosLeftInverse", "cos ∘ arccos", "cos(arccos(x)) = x on the arccos range")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CosArccosLeftInverse", "cos ∘ arccos", "在 arccos 值域上，cos(arccos(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ArcsinSinRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArcsinSinRightInverse", "arcsin ∘ sin", "arcsin(sin(x)) = x on the principal interval")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArcsinSinRightInverse", "arcsin ∘ sin", "在主值区间上，arcsin(sin(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ArccosCosRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccosCosRightInverse", "arccos ∘ cos", "arccos(cos(x)) = x on the principal interval")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccosCosRightInverse", "arccos ∘ cos", "在主值区间上，arccos(cos(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ArctanTanRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArctanTanRightInverse", "arctan ∘ tan", "arctan(tan(x)) = x on the principal interval")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArctanTanRightInverse", "arctan ∘ tan", "在主值区间上，arctan(tan(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ArccotCotRightInverseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ArccotCotRightInverse", "arccot ∘ cot", "arccot(cot(x)) = x on the principal interval")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ArccotCotRightInverse", "arccot ∘ cot", "在主值区间上，arccot(cot(x)) = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl QuotientAsMulNegOnePowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("QuotientAsMulNegOnePower", "a/b as a·b^(-1)", "a/b = a · b^(-1)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("QuotientAsMulNegOnePower", "a/b 即 a·b^(-1)", "a/b = a · b^(-1)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ZeroToPosNatPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ZeroToPosNatPower", "0^n (n>0)", "0^n = 0 for positive natural n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ZeroToPosNatPower", "0^n (n>0)", "对正自然数 n，0^n = 0")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SqrtSquareBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtSquare", "√(a²)", "√(a²) relates to |a| / square-root of a square")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtSquare", "√(a²)", "√(a²) 与 |a| / 平方的平方根相关")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl LogProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogProduct", "log_a(b·c)", "log_a(b·c) = log_a(b) + log_a(c)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogProduct", "log_a(b·c)", "log_a(b·c) = log_a(b) + log_a(c)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl LogQuotientBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogQuotient", "log_a(b/c)", "log_a(b/c) = log_a(b) - log_a(c)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogQuotient", "log_a(b/c)", "log_a(b/c) = log_a(b) - log_a(c)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl LogChangeOfBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogChangeOfBase", "change of base", "log_a(b) = log_c(b) / log_c(a)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogChangeOfBase", "换底公式", "log_a(b) = log_c(b) / log_c(a)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl OneModAtLeastTwoBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("OneModAtLeastTwo", "1 mod n (n≥2)", "1 mod n = 1 when n ≥ 2")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("OneModAtLeastTwo", "1 mod n (n≥2)", "当 n ≥ 2 时 1 mod n = 1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl NestedSameModAbsorptionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("NestedSameModAbsorption", "nested same mod", "(a mod n) mod n = a mod n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("NestedSameModAbsorption", "同模嵌套吸收", "(a mod n) mod n = a mod n")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ModCompatibleSmallerModulusBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ModCompatibleSmallerModulus", "compatible smaller modulus", "a mod d = (a mod m) mod d when m mod d = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModCompatibleSmallerModulus", "相容更小模", "当 m mod d = 0 时 a mod d = (a mod m) mod d")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FloorOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FloorOfInteger", "⌊n⌋ for integer n", "⌊n⌋ = n when n is an integer")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FloorOfInteger", "整数 n 的 ⌊n⌋", "当 n 为整数时 ⌊n⌋ = n")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl CeilOfIntegerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CeilOfInteger", "⌈n⌉ for integer n", "⌈n⌉ = n when n is an integer")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CeilOfInteger", "整数 n 的 ⌈n⌉", "当 n 为整数时 ⌈n⌉ = n")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl AbsNonposEqualsNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsNonposEqualsNegation", "|a| for a≤0", "|a| = -a when a ≤ 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsNonposEqualsNegation", "非正时的 |a|", "当 a ≤ 0 时 |a| = -a")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SignOfPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SignOfPositive", "sign of positive", "sign(a) = 1 when a > 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfPositive", "正数的符号", "当 a > 0 时 sign(a) = 1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SignOfNegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SignOfNegative", "sign of negative", "sign(a) = -1 when a < 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SignOfNegative", "负数的符号", "当 a < 0 时 sign(a) = -1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl MaxRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MaxRightWhenLessEqual", "max when a≤b", "max(a,b) = b when a ≤ b")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MaxRightWhenLessEqual", "a≤b 时的 max", "当 a ≤ b 时 max(a,b) = b")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl MaxLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MaxLeftWhenLessEqual", "max when b≤a", "max(a,b) = a when b ≤ a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MaxLeftWhenLessEqual", "b≤a 时的 max", "当 b ≤ a 时 max(a,b) = a")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl MinLeftWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MinLeftWhenLessEqual", "min when a≤b", "min(a,b) = a when a ≤ b")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MinLeftWhenLessEqual", "a≤b 时的 min", "当 a ≤ b 时 min(a,b) = a")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl MinRightWhenLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MinRightWhenLessEqual", "min when b≤a", "min(a,b) = b when b ≤ a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MinRightWhenLessEqual", "b≤a 时的 min", "当 b ≤ a 时 min(a,b) = b")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl GcdDividesArgumentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("GcdDividesArgument", "gcd divides", "gcd(a,b) divides a (and b)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("GcdDividesArgument", "gcd 整除", "gcd(a,b) 整除 a（以及 b）")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ProductModFactorZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ProductModFactorZero", "product mod factor", "(k·n) mod n = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductModFactorZero", "积对因子取模", "(k·n) mod n = 0")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("EqualityFromTwoSidedWeakOrder", "a≤b and b≤a", "a = b follows from a ≤ b and b ≤ a")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EqualityFromTwoSidedWeakOrder", "a≤b 且 b≤a", "由 a ≤ b 且 b ≤ a 得到 a = b")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl DiffZeroFromEqualOperandsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("DiffZeroFromEqualOperands", "a−b=0 from a=b", "a − b = 0 follows from a = b")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("DiffZeroFromEqualOperands", "由 a=b 得 a−b=0", "由 a = b 得到 a − b = 0")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl EqualFromKnownDifferenceZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("EqualFromKnownDifferenceZero", "a=b from a−b=0", "a = b follows from a known a − b = 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EqualFromKnownDifferenceZero", "由 a−b=0 得 a=b", "由已知 a − b = 0 得到 a = b")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ZeroProductCancelBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ZeroProductCancel", "zero product", "a·b = 0 with a≠0 gives b = 0 (and symmetrically)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ZeroProductCancel", "零因子消元", "a·b = 0 且 a≠0 则 b = 0（对称亦然）")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl AbsEqualsSignTimesArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsEqualsSignTimesArg", "|a| = sign(a)·a", "|a| = sign(a)·a when sign is defined")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsEqualsSignTimesArg", "|a| = sign(a)·a", "在符号有定义时 |a| = sign(a)·a")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SubtractionFromKnownAdditionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SubtractionFromKnownAddition", "subtraction from addition", "c = a − b follows from a known a = b + c")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubtractionFromKnownAddition", "由加法得减法", "由已知 a = b + c 得到 c = a − b")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl QuotEuclideanDecompositionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("QuotEuclideanDecomposition", "Euclidean quot", "a = (a quot n)·n + (a mod n)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("QuotEuclideanDecomposition", "欧几里得商", "a = (a quot n)·n + (a mod n)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ModDividendMinusRemainderZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ModDividendMinusRemainderZero", "mod remainder", "a − (a mod n) is divisible by n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModDividendMinusRemainderZero", "模余数", "a − (a mod n) 可被 n 整除")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SquareSumComponentZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SquareSumComponentZero", "square-sum zero", "a² + b² = 0 forces a = 0 and b = 0 (over reals)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SquareSumComponentZero", "平方和为零", "在实数上 a² + b² = 0 蕴含 a = 0 且 b = 0")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl MinusOneOddNaturalPowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("MinusOneOddNaturalPower", "(-1)^(odd)", "(-1)^n = -1 for odd natural n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("MinusOneOddNaturalPower", "(-1)^(odd)", "对奇自然数 n，(-1)^n = -1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IntersectCommutativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectCommutative", "intersect commutative", "A ∩ B = B ∩ A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectCommutative", "交交换律", "A ∩ B = B ∩ A")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IntersectFromSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectFromSubset", "intersect from subset", "A ⊆ B gives A ∩ B = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectFromSubset", "由子集得交", "A ⊆ B 则 A ∩ B = A")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl EmptySetFromNotNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("EmptySetFromNotNonempty", "empty from not nonempty", "¬$is_nonempty_set(A) gives A = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EmptySetFromNotNonempty", "由非非空得空", "¬$is_nonempty_set(A) 则 A = ∅")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl PowerSetFiniteSetSizeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("PowerSetFiniteSetSize", "|pow(A)|", "|pow(A)| = 2^|A| for finite A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerSetFiniteSetSize", "|pow(A)|", "对有限集 A，|pow(A)| = 2^|A|")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl UnionAssociativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionAssociative", "union associative", "(A ∪ B) ∪ C = A ∪ (B ∪ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionAssociative", "并结合律", "(A ∪ B) ∪ C = A ∪ (B ∪ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IntersectAssociativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectAssociative", "intersect associative", "(A ∩ B) ∩ C = A ∩ (B ∩ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectAssociative", "交结合律", "(A ∩ B) ∩ C = A ∩ (B ∩ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IntersectUnionDistributiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectUnionDistributive", "∩ distributes over ∪", "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectUnionDistributive", "∩ 对 ∪ 分配", "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetMinusUnionDeMorganBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusUnionDeMorgan", "\\ over ∪", "A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusUnionDeMorgan", "差对并", "A \\\\ (B ∪ C) = (A \\\\ B) ∩ (A \\\\ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetMinusIntersectDeMorganBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusIntersectDeMorgan", "\\ over ∩", "A \\ (B ∩ C) = (A \\ B) ∪ (A \\ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusIntersectDeMorgan", "差对交", "A \\\\ (B ∩ C) = (A \\\\ B) ∪ (A \\\\ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IntersectSetMinusSelfEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IntersectSetMinusSelfEmpty", "A ∩ (A\\B)", "A ∩ (A \\ B) relates to emptiness / difference")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntersectSetMinusSelfEmpty", "A ∩ (A\\\\B)", "A ∩ (A \\\\ B) 与空集/差集相关")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetProductEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetProductEmpty", "product over ∅", "∏_{x∈∅} f(x) = 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetProductEmpty", "空集上求积", "∏_{x∈∅} f(x) = 1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetReduceEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetReduceEmpty", "reduce over ∅", "reduce over the empty set is the unit")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetReduceEmpty", "空集上归约", "空集上的归约是单位元")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ReduceEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReduceEmpty", "reduce empty", "reduce on an empty range is the unit")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReduceEmpty", "空归约", "空范围上的归约是单位元")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SumEmptyRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SumEmptyRange", "sum empty range", "∑ over an empty range is 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumEmptyRange", "空范围求和", "空范围求和为 0")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ProductEmptyRangeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ProductEmptyRange", "product empty range", "∏ over an empty range is 1")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductEmptyRange", "空范围求积", "空范围求积为 1")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl UnionAbsorptionFromSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionAbsorptionFromSubset", "union absorption", "A ⊆ B gives A ∪ B = B")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionAbsorptionFromSubset", "并吸收", "A ⊆ B 则 A ∪ B = B")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetMinusRecoversSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusRecoversSubset", "difference recovers subset", "A ⊆ B gives B \\ (B \\ A) = A")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusRecoversSubset", "差集恢复子集", "A ⊆ B 则 B \\\\ (B \\\\ A) = A")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl EmptySetFromSizeZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("EmptySetFromSizeZero", "empty from size 0", "|A| = 0 gives A = ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EmptySetFromSizeZero", "由大小 0 得空集", "|A| = 0 则 A = ∅")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl CartProjFactorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CartProjFactor", "cart projection factor", "Projection recovers a Cartesian factor")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CartProjFactor", "cart projection factor", "Projection recovers a Cartesian factor")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl TupleComponentAtIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("TupleComponentAtIndex", "tuple component", "The i-th component of a tuple equals the stated entry")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("TupleComponentAtIndex", "元组分量", "元组的第 i 个分量等于所述分量")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetSizeSetMinusBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSizeSetMinus", "|A\\B|", "|A \\ B| = |A| − |A ∩ B| for finite sets")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSizeSetMinus", "|A\\\\B|", "对有限集，|A \\\\ B| = |A| − |A ∩ B|")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetSizeUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSizeUnion", "|A∪B|", "|A ∪ B| = |A| + |B| − |A ∩ B|")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSizeUnion", "|A∪B|", "|A ∪ B| = |A| + |B| − |A ∩ B|")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ClosedRangeSingletonListSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ClosedRangeSingletonListSet", "closed range singleton", "{n..n} = {n}")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ClosedRangeSingletonListSet", "闭区间单点", "{n..n} = {n}")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SumSingleTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SumSingleTerm", "sum one term", "∑ with a single term equals that term")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumSingleTerm", "单项目求和", "单项求和等于该项")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ProductSingleTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ProductSingleTerm", "product one term", "∏ with a single term equals that term")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductSingleTerm", "单项目求积", "单项求积等于该项")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReduceAddZeroEqualsSum", "reduce +0 as sum", "reduce with add and 0 equals a sum")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReduceAddZeroEqualsSum", "归约 +0 即求和", "以加法与 0 归约等于求和")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetReduceAddZeroEqualsSum", "finite-set reduce as sum", "finite-set reduce with + and 0 equals a sum")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetReduceAddZeroEqualsSum", "有限集归约即求和", "有限集上以 + 与 0 归约等于求和")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl UnionSetMinusDecompositionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionSetMinusDecomposition", "union\\difference", "A ∪ B = A ∪ (B \\ A)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionSetMinusDecomposition", "union\\\\difference", "A ∪ B = A ∪ (B \\\\ A)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetMinusIntersectSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusIntersectSelf", "A \\ (A∩B)", "A \\ (A ∩ B) = A \\ B")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusIntersectSelf", "A \\\\ (A∩B)", "A \\\\ (A ∩ B) = A \\\\ B")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ModNestedDivisibleAbsorptionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ModNestedDivisibleAbsorption", "nested mod absorption", "If n | m then (a mod m) mod n = a mod n")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModNestedDivisibleAbsorption", "nested mod absorption", "If n | m then (a mod m) mod n = a mod n")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SumSplitLastTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SumSplitLastTerm", "sum split last", "Sum splits off its last term")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumSplitLastTerm", "求和拆末项", "求和可拆出最后一项")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ProductSplitLastTermBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ProductSplitLastTerm", "product split last", "Product splits off its last term")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductSplitLastTerm", "求积拆末项", "求积可拆出最后一项")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetSumListExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSumListExpansion", "finite-set sum expand", "Sum over a list-set expands to an explicit sum")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSumListExpansion", "有限集求和展开", "列表集上的求和展开为显式和")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetProductListExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetProductListExpansion", "finite-set product expand", "Product over a list-set expands to an explicit product")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetProductListExpansion", "有限集求积展开", "列表集上的求积展开为显式积")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ComplexAbsOfNonnegRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ComplexAbsOfNonnegReal", "|x| for x≥0 real", "|embed(x)| = x for x ≥ 0")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ComplexAbsOfNonnegReal", "非负实数模", "对 x ≥ 0，|embed(x)| = x")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ClosedRangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ClosedRangeLiteralExpansion", "closed range expand", "A numeric closed range expands to an explicit list set")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ClosedRangeLiteralExpansion", "闭区间展开", "数值闭区间展开为显式列表集")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl RangeLiteralExpansionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("RangeLiteralExpansion", "range expand", "A numeric range expands to an explicit list set")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("RangeLiteralExpansion", "区间展开", "数值区间展开为显式列表集")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl UnionOverIntersectDistributiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("UnionOverIntersectDistributive", "∪ over ∩", "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("UnionOverIntersectDistributive", "∪ 对 ∩", "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetMinusChainToUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetMinusChainToUnion", "chained difference", "A \\ B \\ C expands via union of removed sets")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetMinusChainToUnion", "链式差集", "A \\\\ B \\\\ C 通过被去掉集合的并展开")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FnRangeOfConstantAnonymousFnBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FnRangeOfConstantAnonymousFn", "range of constant fn", "Range of a constant anonymous function is a singleton")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FnRangeOfConstantAnonymousFn", "常值函数值域", "常值匿名函数的值域是单点集")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SeqEqualsFnOnNPosBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SeqEqualsFnOnNPos", "seq as fn on N+", "A sequence equals its function on positive integers")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SeqEqualsFnOnNPos", "序列即 N+ 上函数", "序列等于其在正整数上的函数")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSeqEqualsFnOnOneBasedDomain", "finite seq as fn", "A finite sequence equals its function on indices 1 through its length")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSeqEqualsFnOnOneBasedDomain", "有限序列即函数", "有限序列等于其在 1 至长度上的函数")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IndexUnionEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IndexUnionEmptyIndex", "⋃_{i∈∅}", "Indexed union over an empty index is ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IndexUnionEmptyIndex", "⋃_{i∈∅}", "空指标上的指标并是 ∅")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IndexIntersectEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "Indexed intersect over an empty index is the ambient universe convention used by Litex")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IndexIntersectEmptyIndex", "⋂_{i∈∅}", "空指标上的指标交按 Litex 约定为全空间")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IndexCartEmptyIndexBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IndexCartEmptyIndex", "indexed cart empty", "Indexed Cartesian product over an empty index is a unit")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IndexCartEmptyIndex", "空指标笛卡尔积", "空指标上的指标笛卡尔积是单位")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl IndexUnionSingletonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("IndexUnionSingleton", "⋃_{i∈{a}}", "Indexed union over a singleton index is the single set")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IndexUnionSingleton", "⋃_{i∈{a}}", "单点指标上的指标并是那个集合")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSeqZeroEqualsFnOnEmpty", "empty finite seq", "The length-0 finite sequence equals the function on the empty range")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSeqZeroEqualsFnOnEmpty", "空有限序列", "长度为 0 的有限序列等于空区间上的函数")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SetBuilderObviouslyEmptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SetBuilderObviouslyEmpty", "empty set-builder", "A contradictory set-builder equals ∅")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SetBuilderObviouslyEmpty", "空集合构造器", "矛盾的集合构造器等于 ∅")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ComplexAbsSquaredOfRectFormBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ComplexAbsSquaredOfRectForm", "|x+y i|²", "|x + y·i|² = x² + y²")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ComplexAbsSquaredOfRectForm", "|x+y i|²", "|x + y·i|² = x² + y²")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl LogBasePowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("LogBasePower", "log_(a^n)(b)", "log_(a^n)(b) = (1/n)·log_a(b)")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LogBasePower", "log_(a^n)(b)", "log_(a^n)(b) = (1/n)·log_a(b)")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ReOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReOfProduct", "Re(z·w)", "Re(z·w) expands from rectangular forms")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReOfProduct", "Re(z·w)", "Re(z·w) 由直角坐标形式展开")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ImgOfProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ImgOfProduct", "Im(z·w)", "Im(z·w) expands from rectangular forms")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ImgOfProduct", "Img(z·w)", "Img(z·w) 由直角坐标形式展开")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl SinOfSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SinOfSum", "sin(x+y)", "sin(x+y) = sin x cos y + cos x sin y")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinOfSum", "sin(x+y)", "sin(x+y) = sin x cos y + cos x sin y")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl CosOfSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("CosOfSum", "cos(x+y)", "cos(x+y) = cos x cos y − sin x sin y")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CosOfSum", "cos(x+y)", "cos(x+y) = cos x cos y − sin x sin y")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl ReduceSingleTermWithAddZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("ReduceSingleTermWithAddZero", "reduce one term", "Reduce with a single term and +0 equals that term")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ReduceSingleTermWithAddZero", "单项归约", "单项并以 +0 归约等于该项")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetSumFubiniSwapBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSumFubiniSwap", "Fubini swap for sums", "Finite double sums may swap summation order")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSumFubiniSwap", "有限双重和 Fubini", "有限双重和可交换求和次序")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FiniteSetSumOverCartesianProductBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("FiniteSetSumOverCartesianProduct", "sum over A×B", "Sum over a Cartesian product expands as an iterated sum")
    }
    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("FiniteSetSumOverCartesianProduct", "A×B 上求和", "笛卡尔积上的求和展开为迭代和")
    }


    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
        }
    }
}

impl FamilyUnionOfSingletonBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FamilyUnionOfSingleton", "Union of a singleton family", "The union of a singleton family of sets is its member."),
            OutputLanguage::Chinese => text("FamilyUnionOfSingleton", "单元素集合族的并", "只包含集合 A 的集合族，其并集等于 A。"),
        }
    }
}

impl FamilyUnionOfPowerSetBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FamilyUnionOfPowerSet", "Union of a power set", "The union of the power set of a set is that set."),
            OutputLanguage::Chinese => text("FamilyUnionOfPowerSet", "幂集的并", "集合 A 的幂集中所有集合的并等于 A。"),
        }
    }
}
