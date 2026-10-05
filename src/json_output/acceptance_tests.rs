//! Acceptance properties for Normal JSON explain / projection.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
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
use crate::json_output::explain::{
    explain_compound_fact_why, explain_searched_proof_why, explain_stmt_kind,
};
use crate::json_output::json_keys::localize_key;
use crate::json_output::{project_run_normal, project_stmt_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{FactId, Runtime};
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::tokenize::Tokenizer;

fn has_cjk(s: &str) -> bool {
    s.chars().any(|c| ('\u{4e00}'..='\u{9fff}').contains(&c))
}

fn has_english_prose(s: &str) -> bool {
    let lower = s.to_ascii_lowercase();
    for word in [
        " the ",
        " and ",
        " for ",
        " when ",
        " from ",
        " with ",
        " over ",
        " equals ",
        " follows ",
        " gives ",
        " both ",
        " verified ",
        " reduce ",
        " finite ",
        " empty ",
        " range ",
        " known ",
        " sequence ",
        " component ",
        " stated ",
        " entry ",
        " forces ",
        " share ",
        " internal ",
        " representation ",
        " expands ",
        " via ",
    ] {
        if lower.contains(word) {
            return true;
        }
    }
    // also catch start-of-string prose
    for word in [
        "the ",
        "both ",
        "verified ",
        "reduce ",
        "sum ",
        "product ",
        "finite ",
    ] {
        if lower.starts_with(word) {
            return true;
        }
    }
    false
}

fn assert_builtin_text_ok(context: &str, lang: OutputLanguage, name: &str, message: &str) {
    assert!(!name.is_empty(), "{context} {lang:?} empty rule_name");
    assert!(!message.is_empty(), "{context} {lang:?} empty message");
    if matches!(lang, OutputLanguage::Chinese) {
        let combined = format!("{name} {message}");
        assert!(
            has_cjk(&combined) || !has_english_prose(&format!(" {combined} ")),
            "{context} Chinese text still has English prose: name={name:?} message={message:?}"
        );
    }
}

fn all_equality_rules() -> Vec<EqualitySearchProofByBuiltinRule> {
    vec![
        EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {},
        ),
        EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(
            SinArcsinLeftInverseBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(
            CosArccosLeftInverseBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(
            TanArctanLeftInverseBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(
            CotArccotLeftInverseBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(
            ArcsinSinRightInverseBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(
            ArccosCosRightInverseBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(
            ArctanTanRightInverseBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(
            ArccotCotRightInverseBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::ArcsinExactZero(ArcsinExactZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(ArcsinExactOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(ArcsinExactNegOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArccosExactOne(ArccosExactOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArccosExactZero(ArccosExactZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArccosExactNegOne(ArccosExactNegOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArctanExactZero(ArctanExactZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ArccotExactZero(ArccotExactZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::PowerProductSameBase(
            PowerProductSameBaseBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::PowerOfPower(PowerOfPowerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::PowerOfProduct(PowerOfProductBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(
            ReciprocalAsNegOnePowerBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(
            QuotientAsMulNegOnePowerBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::OneToAnyPower(OneToAnyPowerBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(ZeroToPosNatPowerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SqrtSquare(SqrtSquareBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SqrtZero(SqrtZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SqrtOne(SqrtOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SqrtOfSquare(SqrtOfSquareBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SqrtProduct(SqrtProductBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SqrtQuotient(SqrtQuotientBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::AbsOfNegation(AbsOfNegationBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::AbsProduct(AbsProductBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::AbsSquare(AbsSquareBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::LogBaseSelf(LogBaseSelfBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogOfOne(LogOfOneBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(LogOfPowerSameBaseBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogArgPower(LogArgPowerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogProduct(LogProductBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogQuotient(LogQuotientBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogReciprocal(LogReciprocalBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LogChangeOfBase(LogChangeOfBaseBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ZeroMod(ZeroModBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ModOne(ModOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(OneModAtLeastTwoBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(
            NestedSameModAbsorptionBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::ModCompatibleSmallerModulus(
            ModCompatibleSmallerModulusBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::MinIdempotent(MinIdempotentBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::MaxIdempotent(MaxIdempotentBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::MinCommutative(MinCommutativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::MaxCommutative(MaxCommutativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(AbsAbsAbsorptionBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ExpOfLn(ExpOfLnBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LnOfExp(LnOfExpBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::FloorOfInteger(FloorOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::CeilOfInteger(CeilOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ModSelfZero(ModSelfZeroBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(
            FloorOfCeilOfIntegerBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(
            CeilOfFloorOfIntegerBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(
            SqrtOfSquareEqualsAbsBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::QuotByOne(QuotByOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::QuotSelfOne(QuotSelfOneBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::LcmCommutative(LcmCommutativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(LcmIdempotentAbsBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::GcdCommutative(GcdCommutativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(GcdIdempotentAbsBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(GcdRightZeroAbsBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(GcdLeftZeroAbsBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::FactorialSuccessor(FactorialSuccessorBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(
            AbsNonnegEqualsSelfBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(
            AbsNonposEqualsNegationBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::SignOfPositive(SignOfPositiveBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SignOfNegative(SignOfNegativeBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(
            MaxRightWhenLessEqualBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(
            MaxLeftWhenLessEqualBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(
            MinLeftWhenLessEqualBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(
            MinRightWhenLessEqualBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::GcdDividesArgument(GcdDividesArgumentBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ProductModFactorZero(
            ProductModFactorZeroBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(
            EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
                left_le_right_proof: sample_known_atomic_premise("0 <= 0"),
                right_le_left_proof: sample_known_atomic_premise("0 <= 0"),
            },
        ),
        EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(
            DiffZeroFromEqualOperandsBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(
            EqualFromKnownDifferenceZeroBuiltinRuleProof {
                cite_fact_id: FactId::new(1),
            },
        ),
        EqualitySearchProofByBuiltinRule::ZeroProductCancel(ZeroProductCancelBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SignOfNegation(SignOfNegationBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(
            SignTimesAbsEqualsArgBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(
            AbsEqualsSignTimesArgBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SignOfProduct(SignOfProductBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(
            SubtractionFromKnownAdditionBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(
            QuotEuclideanDecompositionBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(
            ModDividendMinusRemainderZeroBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SquareSumComponentZero(
            SquareSumComponentZeroBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(
            MinusOneOddNaturalPowerBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(LcmGcdProductAbsBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::UnionEmptyRight(UnionEmptyRightBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::UnionEmptyLeft(UnionEmptyLeftBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::IntersectEmptyRight(
            IntersectEmptyRightBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(IntersectEmptyLeftBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(SetMinusSelfEmptyBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(SetMinusEmptyRightBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(SetMinusEmptyLeftBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::UnionCommutative(UnionCommutativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::IntersectCommutative(
            IntersectCommutativeBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::UnionIdempotent(UnionIdempotentBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::IntersectIdempotent(
            IntersectIdempotentBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(
            IntersectFromSubsetBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(
            EmptySetFromNotNonemptyBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(
            PowerSetFiniteSetSizeBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::UnionAssociative(UnionAssociativeBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::IntersectAssociative(
            IntersectAssociativeBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(
            IntersectUnionDistributiveBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(
            SetMinusUnionDeMorganBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(
            SetMinusIntersectDeMorganBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(
            IntersectSetMinusSelfEmptyBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(FiniteSetSumEmptyBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(
            FiniteSetProductEmptyBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(
            FiniteSetReduceEmptyBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ReduceEmpty(ReduceEmptyBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::SumEmptyRange(SumEmptyRangeBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ProductEmptyRange(ProductEmptyRangeBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(
            UnionAbsorptionFromSubsetBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(
            SetMinusRecoversSubsetBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(
            EmptySetFromSizeZeroBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::CartProjFactor(CartProjFactorBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::TupleComponentAtIndex(
            TupleComponentAtIndexBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(
            FiniteSetSizeSetMinusBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(FiniteSetSizeUnionBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(
            ClosedRangeSingletonListSetBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SumSingleTerm(SumSingleTermBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ProductSingleTerm(ProductSingleTermBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(
            ReduceAddZeroEqualsSumBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(
            FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::PowOfLogInverse(PowOfLogInverseBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(
            UnionSetMinusDecompositionBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(
            SetMinusIntersectSelfBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(ReOfImaginaryUnitBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(ImgOfImaginaryUnitBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(ReOfRealEmbeddingBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(ImgOfRealEmbeddingBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ReOfRealPlusI(ReOfRealPlusIBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(ImgOfRealPlusIBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(
            ComplexAbsOfImaginaryUnitBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(
            ModNestedDivisibleAbsorptionBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::SumSplitLastTerm(SumSplitLastTermBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(
            ProductSplitLastTermBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(
            FiniteSetSumListExpansionBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(
            FiniteSetProductListExpansionBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(EulerEqualsExpOneBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::LnOfEuler(LnOfEulerBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ReOfReal(ReOfRealBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ImgOfReal(ImgOfRealBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(
            ReOfRealPlusImagScaledBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(
            ImgOfRealPlusImagScaledBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(
            ComplexAbsOfNonnegRealBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(
            ComplexAbsOfImagScaledBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(
            ClosedRangeLiteralExpansionBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(
            RangeLiteralExpansionBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(PowerSetOfEmptyBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(
            PowerSetOfSingletonBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(FamilyUnionOfEmptyBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::FamilyUnionOfSingleton(
            FamilyUnionOfSingletonBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FamilyUnionOfPowerSet(
            FamilyUnionOfPowerSetBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(
            CartWithEmptyFactorBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(
            UnionOverIntersectDistributiveBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(
            SetMinusChainToUnionBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(
            FnRangeOfConstantAnonymousFnBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SeqEqualsFnOnNPos(SeqEqualsFnOnNPosBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnOneBasedDomain(
            FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(
            IndexUnionEmptyIndexBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(
            IndexIntersectEmptyIndexBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(
            IndexCartEmptyIndexBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::IndexUnionSingleton(
            IndexUnionSingletonBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(
            FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(
            SetBuilderObviouslyEmptyBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(
            ComplexAbsSquaredOfRectFormBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::ExpOfSum(ExpOfSumBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::LogBasePower(LogBasePowerBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }),
        EqualitySearchProofByBuiltinRule::ReOfProduct(ReOfProductBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ImgOfProduct(ImgOfProductBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SinOfSum(SinOfSumBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::CosOfSum(CosOfSumBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(
            ReduceSingleTermWithAddZeroBuiltinRuleProof {
                proof_of_requirement_facts: Vec::new(),
            },
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(
            FiniteSetSumFubiniSwapBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(
            FiniteSetSumOverCartesianProductBuiltinRuleProof {},
        ),
        EqualitySearchProofByBuiltinRule::SinOfZero(SinOfZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::CosOfZero(CosOfZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::TanOfZero(TanOfZeroBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SinOfHalfPi(SinOfHalfPiBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::CosOfPi(CosOfPiBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::SinOfPi(SinOfPiBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::CotOfHalfPi(CotOfHalfPiBuiltinRuleProof {}),
        EqualitySearchProofByBuiltinRule::PythagoreanIdentity(
            PythagoreanIdentityBuiltinRuleProof {},
        ),
    ]
}

#[test]
fn acceptance_equality_builtin_all_variants_bilingual() {
    let rules = all_equality_rules();
    // Four identity leaves moved to TheyAreTheSame; indexed lookup is now a class proof.
    assert_eq!(rules.len(), 190);
    for (index, rule) in rules.iter().enumerate() {
        let context = format!("equality variant {index}");
        let en = rule.rule_name_and_message(OutputLanguage::English);
        let zh = rule.rule_name_and_message(OutputLanguage::Chinese);
        assert_builtin_text_ok(
            &context,
            OutputLanguage::English,
            &en.rule_name,
            &en.message,
        );
        assert_builtin_text_ok(
            &context,
            OutputLanguage::Chinese,
            &zh.rule_name,
            &zh.message,
        );
        for language in OutputLanguage::ALL.into_iter().skip(2) {
            let localized = rule.rule_name_and_message(language);
            assert_builtin_text_ok(
                &context,
                language,
                &localized.rule_name,
                &localized.message,
            );
            if has_english_prose(&en.message) {
                assert_ne!(
                    localized.message, en.message,
                    "{context} {language:?} fell back to English"
                );
            }
        }
    }
}

#[test]
fn acceptance_equality_named_language_methods_match_dispatch_for_every_variant() {
    use crate::json_output::explain::BuiltinRuleText;
    let methods: [fn(&EqualitySearchProofByBuiltinRule) -> BuiltinRuleText; 10] = [
        EqualitySearchProofByBuiltinRule::rule_name_and_message_en,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_zh,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_zh_hant,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_fr,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_ru,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_es,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_ar,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_ja,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_ko,
        EqualitySearchProofByBuiltinRule::rule_name_and_message_vi,
    ];
    for rule in all_equality_rules() {
        for (language, method) in OutputLanguage::ALL.into_iter().zip(methods) {
            let direct = method(&rule);
            let selected = rule.rule_name_and_message(language);
            assert_eq!(
                (direct.rule_name, direct.message),
                (selected.rule_name, selected.message),
                "{language:?}",
            );
        }
    }
}

#[test]
fn localized_copy_states_the_actual_rule_instead_of_an_unrelated_formula() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::ZeroFromNatAndOneLeBuiltinRuleProof;
    let sqrt = SqrtSquareBuiltinRuleProof { proof_of_requirement_facts: vec![] };
    let difference = IntersectSetMinusSelfEmptyBuiltinRuleProof {};
    let arcsin = ArcsinExactZeroBuiltinRuleProof {};
    let inverse = ArcsinSinRightInverseBuiltinRuleProof { proof_of_requirement_facts: vec![] };
    let nonzero = ZeroFromNatAndOneLeBuiltinRuleProof { proof_of_requirement_facts: vec![] };
    for lang in OutputLanguage::ALL {
        let text = sqrt.rule_name_and_message(lang);
        assert!(text.message.contains("(sqrt(x))^2 = x (x ≥ 0)"), "{lang:?}");
        assert!(!text.message.contains("sqrt(a²)"));
        let text = difference.rule_name_and_message(lang);
        assert!(text.message.contains("A ∩ (B \\ A) = ∅"), "{lang:?}");
        assert!(!text.message.contains("A ∩ (A \\ B)"));
        let text = inverse.rule_name_and_message(lang);
        assert!(text.message.contains("[-π/2, π/2]"), "{lang:?}");
        assert!(text.message.contains("arcsin(sin(x)) = x"));
        let text = arcsin.rule_name_and_message(lang);
        assert!(text.message.contains("arcsin(0) = 0"));
        assert_ne!(text.rule_name, "arcsin 0");
        assert_ne!(text.message, "arcsin(0) = 0");
        let text = nonzero.rule_name_and_message(lang);
        assert!(text.message.contains("n ∈ N ∧ 1 ≤ n ⇒ n ≠ 0"), "{lang:?}");
    }
    let zh = arcsin.rule_name_and_message_zh();
    assert_eq!(zh.rule_name, "反正弦函数在零处的值");
    assert_eq!(zh.message, "反正弦函数在零处的值为零，即 arcsin(0) = 0");
}

const STMT_KINDS: &[&str] = &[
    "let",
    "have_in_nonempty",
    "have_equal",
    "have_by_exist",
    "obtain_exist",
    "obtain_atomic",
    "have_by_preimage",
    "have_by_replacement",
    "have_fn_equal",
    "have_fn_cases",
    "have_fn_forall_exist_unique",
    "have_fn_induc",
    "def_prop",
    "def_abstract_prop",
    "def_struct",
    "def_template",
    "def_algo_cases",
    "def_algo_induc",
    "def_thm",
    "axiom",
    "def_strategy",
    "witness_exist",
    "witness_atomic",
    "witness_nonempty",
    "trust",
    "trust_have",
    "by_cases",
    "by_contra",
    "by_def",
    "by_extension",
    "by_fn_extension",
    "by_enumerate",
    "by_for",
    "by_thm",
    "by_induc",
    "by_strong_induc",
    "register_reflexive",
    "register_symmetric",
    "register_transitive",
    "release_thm",
    "release_struct",
    "release_obj",
    "expand_range",
    "release_zorn",
    "release_choice",
    "release_regularity",
    "claim",
    "sketch",
    "eval",
];

#[test]
fn acceptance_stmt_kinds_all_bilingual() {
    for kind in STMT_KINDS {
        let en = explain_stmt_kind(kind, OutputLanguage::English);
        let zh = explain_stmt_kind(kind, OutputLanguage::Chinese);
        assert!(!en.type_tag.is_empty(), "{kind}");
        assert!(
            !en.rule_name.is_empty() && !en.message.is_empty(),
            "{kind} en"
        );
        assert!(
            !zh.rule_name.is_empty() && !zh.message.is_empty(),
            "{kind} zh"
        );
        assert!(
            has_cjk(&zh.rule_name) || has_cjk(&zh.message),
            "{kind} zh lacks CJK: {} / {}",
            zh.rule_name,
            zh.message
        );
        assert!(
            has_cjk(zh.type_tag),
            "{kind} Chinese type_tag must be Chinese, got {:?}",
            zh.type_tag
        );
        // must not fall through to raw kind as rule_name for known kinds
        assert_ne!(en.rule_name, *kind, "{kind} fell through English default");
    }
}

const SEARCHED_KINDS: &[&str] = &[
    "builtin_strategy",
    "by_definition",
    "known_strategy",
    "builtin_rewrite",
    "known_rewrite",
    "equivalence_class",
    "object_definition",
    "matching_one_arg_by_one",
    "known_forall_via_symmetry",
    "failed",
];

#[test]
fn acceptance_searched_proof_why_all_bilingual() {
    for kind in SEARCHED_KINDS {
        let en = explain_searched_proof_why(kind, OutputLanguage::English);
        let zh = explain_searched_proof_why(kind, OutputLanguage::Chinese);
        assert_eq!(en.type_tag, *kind);
        assert!(!en.rule_name.is_empty() && !en.message.is_empty());
        assert!(!zh.rule_name.is_empty() && !zh.message.is_empty());
        assert!(has_cjk(&zh.rule_name) || has_cjk(&zh.message), "{kind}");
        assert!(
            has_cjk(zh.type_tag),
            "{kind} Chinese type_tag must be Chinese, got {:?}",
            zh.type_tag
        );
        assert_ne!(
            zh.type_tag, *kind,
            "{kind} Chinese type_tag must not stay English"
        );
    }
}

#[test]
fn acceptance_compound_fact_why_bilingual() {
    for kind in ["and", "or", "forall", "exist", "chain"] {
        let en = explain_compound_fact_why(kind, OutputLanguage::English);
        let zh = explain_compound_fact_why(kind, OutputLanguage::Chinese);
        assert_eq!(en.type_tag, "compound_fact");
        assert_eq!(zh.type_tag, "复合事实");
        assert!(has_cjk(&zh.rule_name) || has_cjk(&zh.message));
    }
}

#[test]
fn acceptance_json_keys_chinese_map() {
    for (en, zh) in [
        ("success", "成功"),
        ("statement", "语句"),
        ("proof_method", "证明方法"),
        ("why_failed", "失败原因"),
        ("fail_reason", "失败原因"),
        ("stores", "存储"),
        ("infers", "推断"),
        ("type", "类型"),
        ("rule_name", "规则名"),
        ("message", "说明"),
        ("cite", "引用"),
        ("line", "行号"),
        ("phase", "阶段"),
        ("goal", "目标命题"),
        ("kind", "种类"),
        ("detail", "详细度"),
        ("language", "语言"),
        ("statement_results", "语句结果"),
        ("session_error", "会话错误"),
        ("verify", "验证"),
        ("store_and_infer", "存储与推理"),
        ("fact", "命题"),
        ("fact_id", "命题编号"),
    ] {
        assert_eq!(localize_key(en, OutputLanguage::Chinese), zh);
        assert_eq!(localize_key(en, OutputLanguage::English), en);
    }
}

fn runtime_en() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

fn runtime_zh() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::Chinese,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> crate::execute::ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1);
    runtime.exec_stmt(&stmts[0]).expect("exec")
}

fn obj_field<'a>(v: &'a JsonValue, key: &str) -> &'a JsonValue {
    v.as_object()
        .expect("object")
        .get(key)
        .unwrap_or_else(|| panic!("missing {key}"))
}

#[test]
fn acceptance_normal_success_field_order() {
    let mut rt = runtime_en();
    let json = project_stmt_normal(&exec_one(&mut rt, "1 + 1 = 2"), &rt);
    let keys = json.as_object().expect("object").keys_in_order();
    assert_eq!(
        keys,
        vec!["success", "statement", "proof_method", "stores", "infers"]
    );
    let why = obj_field(&json, "proof_method").as_object().unwrap();
    assert_eq!(why.keys_in_order(), vec!["type", "rule_name", "message"]);
}

#[test]
fn acceptance_normal_success_shape_and_no_rule_id() {
    let mut rt = runtime_en();
    let json = project_stmt_normal(&exec_one(&mut rt, "1 + 1 = 2"), &rt);
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(true));
    assert!(obj_field(&json, "statement")
        .as_str()
        .ok()
        .unwrap()
        .contains("="));
    let why = obj_field(&json, "proof_method").as_object().unwrap();
    assert_eq!(
        why.get("type").and_then(|x| x.as_str().ok()),
        Some("by_closed_calculation")
    );
    assert!(why.get("rule_name").is_some());
    assert!(why.get("message").is_some());
    assert!(why.get("rule").is_none());
    assert!(why.get("rule_id").is_none());
    assert!(why.get("variant").is_none());
    assert!(obj_field(&json, "stores").as_array().is_ok());
    assert!(obj_field(&json, "infers").as_array().is_ok());
}

#[test]
fn acceptance_normal_failure_empty_stores() {
    let mut rt = runtime_en();
    let _ = exec_one(&mut rt, "have a R");
    let json = project_stmt_normal(&exec_one(&mut rt, "a > 10"), &rt);
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(false));
    let why = obj_field(&json, "why_failed").as_object().unwrap();
    assert_eq!(
        why.get("phase").and_then(|x| x.as_str().ok()),
        Some("search_proof")
    );
    assert!(why.get("goal").is_some());
    assert!(obj_field(&json, "stores").as_array().unwrap().is_empty());
    assert!(obj_field(&json, "infers").as_array().unwrap().is_empty());
}

#[test]
fn acceptance_chinese_keys_and_messages_end_to_end() {
    let mut rt = runtime_zh();
    let json = project_stmt_normal(&exec_one(&mut rt, "1 + 2 = 3"), &rt);
    assert_eq!(obj_field(&json, "成功"), &JsonValue::Bool(true));
    let why = obj_field(&json, "证明方法").as_object().unwrap();
    assert_eq!(
        why.get("规则名").and_then(|x| x.as_str().ok()),
        Some("封闭计算")
    );
    assert_eq!(
        why.get("说明").and_then(|x| x.as_str().ok()),
        Some("精确计算封闭表达式，不递归搜索证明")
    );
    assert_eq!(
        why.get("类型").and_then(|x| x.as_str().ok()),
        Some("封闭计算")
    );
}

#[test]
fn acceptance_cite_readable_no_hash_wrappers() {
    let mut rt = runtime_en();
    let _ = exec_one(&mut rt, "have k N");
    let json = project_stmt_normal(&exec_one(&mut rt, "k >= 0"), &rt);
    let why = obj_field(&json, "proof_method").as_object().unwrap();
    let cite = why.get("cite").and_then(|x| x.as_str().ok()).unwrap_or("");
    assert_eq!(cite, "0 <= k");
    assert!(!cite.contains('#'));
    assert_eq!(
        why.get("rule_name").and_then(|x| x.as_str().ok()),
        Some("Known converse order")
    );
}

#[test]
fn acceptance_stmt_let_chinese() {
    let mut rt = runtime_zh();
    let json = project_stmt_normal(&exec_one(&mut rt, "let a = 1"), &rt);
    let why = obj_field(&json, "证明方法").as_object().unwrap();
    assert_eq!(
        why.get("类型").and_then(|x| x.as_str().ok()),
        Some("定义对象")
    );
    assert_eq!(
        why.get("规则名").and_then(|x| x.as_str().ok()),
        Some("赋值定义")
    );
}

#[test]
fn acceptance_run_envelope_language() {
    let mut rt = runtime_zh();
    let stmt = exec_one(&mut rt, "1 = 1");
    let run = RunLitexCodeResult {
        success: true,
        statement_results: vec![stmt],
        failed_statement_results: None,
        session_error: None,
        normal_json: None,
    };
    let json = project_run_normal(&run, &rt, "eval", None);
    assert_eq!(obj_field(&json, "种类").as_str().ok(), Some("run"));
    assert_eq!(obj_field(&json, "详细度").as_str().ok(), Some("normal"));
    assert_eq!(obj_field(&json, "语言").as_str().ok(), Some("zh"));
    assert_eq!(obj_field(&json, "成功"), &JsonValue::Bool(true));
    assert_eq!(obj_field(&json, "语句结果").as_array().unwrap().len(), 1);
}

#[test]
fn acceptance_hot_atomic_chinese_from_known_in_n() {
    let mut rt = runtime_zh();
    let _ = exec_one(&mut rt, "have k N");
    let json = project_stmt_normal(&exec_one(&mut rt, "k >= 0"), &rt);
    let why = obj_field(&json, "证明方法").as_object().unwrap();
    assert_eq!(
        why.get("规则名").and_then(|x| x.as_str().ok()),
        Some("已知反向序关系")
    );
    assert!(has_cjk(
        why.get("说明").and_then(|x| x.as_str().ok()).unwrap_or("")
    ));
}

#[test]
fn acceptance_previously_stubbed_atomic_families_bilingual() {
    use crate::ast::obj::StandardSet;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater::{
        ClosedNumericComparisonBuiltinRuleProof as GreaterClosed,
        GreaterFactSearchProofByBuiltinRule, NativeEulerGreaterZeroBuiltinRuleProof,
        NativePiGreaterZeroBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
        ClosedNumericMembershipBuiltinRuleProof, InFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_set::{
        IsSetAlwaysTrueBuiltinRuleProof, IsSetFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::{
        IsNonemptySetFactSearchProofByBuiltinRule, LiteralListSetNonemptyBuiltinRuleProof,
        PowerSetNonemptyBuiltinRuleProof, StandardSetNonemptyBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::{
        IsFiniteSetFactSearchProofByBuiltinRule, ListSetFiniteBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_cart::{
        CartConstructorBuiltinRuleProof, IsCartFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_tuple::{
        IsTupleFactSearchProofByBuiltinRule, TupleLiteralBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::{
        SubsetFactSearchProofByBuiltinRule, SubsetReflexivityBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::superset::{
        SupersetFactSearchProofByBuiltinRule, SupersetReflexivityBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
        CoprimeByComputation, CoprimeFactSearchProofByBuiltinRule, NotCoprimeByComputation,
        NotCoprimeFactSearchProofByBuiltinRule, NotPrimeByComputation,
        NotPrimeFactSearchProofByBuiltinRule, PrimeByComputation, PrimeFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_less::{
        ClosedNumericComparisonBuiltinRuleProof as NotLessClosed,
        NotLessFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_greater::{
        ClosedNumericComparisonBuiltinRuleProof as NotGreaterClosed,
        NotGreaterFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::{
        ClosedNumericNonMembershipBuiltinRuleProof, NotInFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_nonempty_set::{
        EmptyListSetNotNonemptyBuiltinRuleProof, NotIsNonemptySetFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_finite_set::{
        NotIsFiniteSetFactSearchProofByBuiltinRule, StandardInfiniteSetBuiltinRuleProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_subset::{
        FromKnownNotSupersetBuiltinRuleProof, NotSubsetFactSearchProofByBuiltinRule,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_superset::{
        FromKnownNotSubsetBuiltinRuleProof, NotSupersetFactSearchProofByBuiltinRule,
    };

    let samples = vec![
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::NativeEulerGreaterZero(
                NativeEulerGreaterZeroBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::NativePiGreaterZero(
                NativePiGreaterZeroBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(GreaterClosed {
                left_normal: "2".into(),
                right_normal: "1".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(
            IsSetFactSearchProofByBuiltinRule::AlwaysTrue(IsSetAlwaysTrueBuiltinRuleProof {}),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(
            IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(
                StandardSetNonemptyBuiltinRuleProof {
                    target_set: StandardSet::R,
                },
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(
            IsNonemptySetFactSearchProofByBuiltinRule::LiteralListSetNonempty(
                LiteralListSetNonemptyBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(
            IsNonemptySetFactSearchProofByBuiltinRule::PowerSetNonempty(
                PowerSetNonemptyBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(
            IsFiniteSetFactSearchProofByBuiltinRule::ListSet(ListSetFiniteBuiltinRuleProof {}),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::ClosedNumericMembership(
                ClosedNumericMembershipBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsCartFact(
            IsCartFactSearchProofByBuiltinRule::CartConstructor(CartConstructorBuiltinRuleProof {}),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsTupleFact(
            IsTupleFactSearchProofByBuiltinRule::TupleLiteral(TupleLiteralBuiltinRuleProof {}),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(
            SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(
                SubsetReflexivityBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(
            SupersetFactSearchProofByBuiltinRule::SupersetReflexivity(
                SupersetReflexivityBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(
            PrimeFactSearchProofByBuiltinRule::PrimeByComputation(PrimeByComputation {
                resolved_value: "17".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(
            CoprimeFactSearchProofByBuiltinRule::CoprimeByComputation(CoprimeByComputation {
                left_resolved: "14".into(),
                right_resolved: "25".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(
            NotPrimeFactSearchProofByBuiltinRule::NotPrimeByComputation(NotPrimeByComputation {
                resolved_value: "1".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(
            NotCoprimeFactSearchProofByBuiltinRule::NotCoprimeByComputation(
                NotCoprimeByComputation {
                    left_resolved: "14".into(),
                    right_resolved: "21".into(),
                },
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(
            NotLessFactSearchProofByBuiltinRule::ClosedNumericComparison(NotLessClosed {
                left_normal: "2".into(),
                right_normal: "1".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(
            NotGreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(NotGreaterClosed {
                left_normal: "1".into(),
                right_normal: "2".into(),
            }),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
            NotInFactSearchProofByBuiltinRule::ClosedNumericNonMembership(
                ClosedNumericNonMembershipBuiltinRuleProof { normal: "0".into() },
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(
            NotIsNonemptySetFactSearchProofByBuiltinRule::EmptyListSet(
                EmptyListSetNotNonemptyBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(
            NotIsFiniteSetFactSearchProofByBuiltinRule::StandardInfiniteSet(
                StandardInfiniteSetBuiltinRuleProof {},
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(
            NotSubsetFactSearchProofByBuiltinRule::FromKnownNotSuperset(
                FromKnownNotSupersetBuiltinRuleProof {
                    premise_proof: sample_known_atomic_premise("not {2} $superset {1}"),
                },
            ),
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(
            NotSupersetFactSearchProofByBuiltinRule::FromKnownNotSubset(
                FromKnownNotSubsetBuiltinRuleProof {
                    premise_proof: sample_known_atomic_premise("not {1} $subset {2}"),
                },
            ),
        ),
    ];

    assert!(samples.len() >= 20);
    for (index, rule) in samples.iter().enumerate() {
        let context = format!("atomic family sample {index}");
        let en = rule.rule_name_and_message(OutputLanguage::English);
        let zh = rule.rule_name_and_message(OutputLanguage::Chinese);
        assert_builtin_text_ok(
            &context,
            OutputLanguage::English,
            &en.rule_name,
            &en.message,
        );
        assert_builtin_text_ok(
            &context,
            OutputLanguage::Chinese,
            &zh.rule_name,
            &zh.message,
        );
        assert!(
            has_cjk(&zh.rule_name) || has_cjk(&zh.message),
            "{context} zh"
        );
    }
}

fn sample_known_atomic_premise(code: &str) -> crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof{
    // These fixtures test explanation text, using actual stored premise proofs.
    let mut runtime = runtime_en();
    assert!(!exec_one(&mut runtime, &format!("trust {code}")).is_failed());
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .unwrap();
    let mut stmts = runtime.parse(&tokens).unwrap();
    let crate::ast::stmt::Stmt::Fact(crate::ast::fact::Fact::AtomicFact(fact)) = stmts.remove(0)
    else {
        panic!("atomic fixture");
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
    };
    use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
    let result = runtime
        .verify_fact(
            &crate::ast::fact::Fact::AtomicFact(fact),
            VerifyState::top_level(),
        )
        .unwrap();
    let VerifyFactResult::AtomicExceptEquality(result) = result else {
        panic!("atomic result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("known fixture")
    };
    assert!(matches!(
        result.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
    ));
    crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof {
        fact: result.fact, searched_proof: Box::new(result.searched_proof),
    }
}

#[test]
fn acceptance_all_locales_cover_statement_and_proof_routes() {
    for language in OutputLanguage::ALL {
        for kind in STMT_KINDS {
            let text = explain_stmt_kind(kind, language);
            assert!(
                !text.type_tag.is_empty() && !text.rule_name.is_empty() && !text.message.is_empty()
            );
            if language != OutputLanguage::English {
                assert_ne!(
                    text.message,
                    explain_stmt_kind(kind, OutputLanguage::English).message
                );
            }
        }
        for kind in SEARCHED_KINDS.iter().copied().chain([
            "structural_membership",
            "closed_calculation",
            "known_special_property",
            "unknown_future_route",
        ]) {
            let text = explain_searched_proof_why(kind, language);
            assert!(
                !text.type_tag.is_empty() && !text.rule_name.is_empty() && !text.message.is_empty()
            );
            if language != OutputLanguage::English {
                assert_ne!(
                    text.message,
                    explain_searched_proof_why(kind, OutputLanguage::English).message
                );
            }
        }
        for kind in [
            "and",
            "or",
            "forall",
            "exist",
            "chain",
            "unknown_future_fact",
        ] {
            let text = explain_compound_fact_why(kind, language);
            assert!(!text.rule_name.is_empty() && !text.message.is_empty());
            if language != OutputLanguage::English {
                assert_ne!(
                    text.message,
                    explain_compound_fact_why(kind, OutputLanguage::English).message
                );
            }
        }
    }
}
