//! Generated builtin-strategy detailed projection.
use super::store::project_verify_facts;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinStrategy;
use crate::json_output::helper::{object, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_atomic_builtin_strategy(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PosAddPosIsPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NonnegativeSumIsNonnegative")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveLeftStrict(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StrictAdditiveLeftStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveRightStrict(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StrictAdditiveRightStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NonzeroProduct")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxListMembersLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMaxListMembersLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxConstructorPartsLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMaxConstructorPartsLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinListMembersLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMinListMembersLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinConstructorPartsLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMinConstructorPartsLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonneg(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductNonnegativeBothNonneg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonpos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductNonnegativeBothNonpos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddCrossedLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedSubtrahendLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedMinuendLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedPositiveDenomLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedNegativeDenomLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowSharedExponentLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AbsVsSquareLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightNonnegativeShiftLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightNonnegativeShiftRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddLeftNonpositiveShiftLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddLeftNonpositiveShiftRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonpositiveToZero(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubNonpositiveToZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonnegativeFromZero(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubNonnegativeFromZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrMoreRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulScaleFactorOneOrMoreRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrLessLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulScaleFactorOneOrLessLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualAligned(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulComponentwiseLessEqualAligned")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualCrossed(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulComponentwiseLessEqualCrossed")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonNonnegativeFactorLessEqual(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CommonNonnegativeFactorLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothPos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductPositiveBothPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothNeg(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductPositiveBothNeg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("QuotientPositiveSameSignPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignNeg(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("QuotientPositiveSameSignNeg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseStrictLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseStrictRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedSubtrahendLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedMinuendLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedPositiveDenomLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedNegativeDenomLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowSharedExponentLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AbsVsSquareLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftStrict(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftLeftStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftLeftWeak")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightStrict(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftRightStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightWeak(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftRightWeak")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveToZero(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubPositiveToZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveFromZero(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubPositiveFromZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CommonPositiveFactorLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetSizeInNumericCarrier(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetSizeInNumericCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteExtremumSourceInCarrier(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteExtremumSourceInCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RefinedNumericCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureAdd(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureSub(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureMul(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureDiv(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureDiv")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosurePow(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAdd(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureSub(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureMul(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureDiv(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureDiv")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosurePow(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAbs(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAdd(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureSub(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMul(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMod(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureMod")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosurePowNat(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosurePowNat")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAbs(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAdd(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureMul(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureSub(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosurePow(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAbs(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddLeftPos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAddLeftPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddRightPos(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAddRightPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierMul(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierPow(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierPow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAbs(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierFiniteSetSize(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierFiniteSetSize")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionMembershipFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionMembershipFromRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowerSetMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RangeMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ClosedRangeMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntervalMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderMembership(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetBuilderMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetSubsetFromMembers(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ListSetSubsetFromMembers")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionSubsetFromBothOperands")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectSubsetFromLeftOperand")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectSubsetFromRightOperand")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusSubsetFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubsetOfIntersectFromBothBounds")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnRangeFiniteFromDomain(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FnRangeFiniteFromDomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetFiniteFromBase(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowerSetFiniteFromBase")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderFiniteFromParamSet(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetBuilderFiniteFromParamSet")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionFiniteFromBoth(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionFiniteFromBoth")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromBoth(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectFiniteFromBoth")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusFiniteFromLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusFiniteFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartFiniteFromFactors(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartFiniteFromFactors")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeNonemptyFromEndpointOrder(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ClosedRangeNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeNonemptyFromEndpointOrder(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RangeNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalNonemptyFromEndpointOrder(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntervalNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromLeft(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionNonemptyFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromRight(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionNonemptyFromRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartNonemptyFromAllFactors(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartNonemptyFromAllFactors")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnSetNonemptyFromCodomain(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FnSetNonemptyFromCodomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AnonymousFnNonemptyFromCodomain(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AnonymousFnNonemptyFromCodomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSeqSetNonemptyFromCodomain(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSeqSetNonemptyFromCodomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SeqSetNonemptyFromCodomain(p) => object(vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SeqSetNonemptyFromCodomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
    }
}
