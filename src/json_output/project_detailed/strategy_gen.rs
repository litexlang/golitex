//! Generated builtin-strategy detailed projection.
use super::store::project_verify_facts;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinStrategy;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FieldArithmeticCarrierConstructorTree;

pub(super) fn project_atomic_builtin_strategy(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteFunctionApplicationMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteFunctionApplicationMembership")),
            ("source", super::function_domain::project_finite_function_source(&p.source, runtime)),
            ("index", p.index.map(|index| string(index.to_string())).unwrap_or(JsonValue::Null)),
            ("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|fact| string(fact.readable_string())).collect())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSetMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FunctionSetMembership")),
            ("function_domain", super::function_domain::project_function_domain(&p.domain, runtime)),
            ("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|fact| string(fact.readable_string())).collect())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FieldArithmeticCarrierClosure(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FieldArithmeticCarrierClosure")),
            ("carrier", string(crate::ast::obj::Obj::StandardSet(p.carrier.clone()).readable_string())),
            ("constructor_tree", project_field_arithmetic_tree(&p.constructor_tree, runtime)),
            ("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|fact| string(fact.readable_string())).collect())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ListSetMembership")),
            ("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|fact| string(fact.readable_string())).collect())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetNonMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ListSetNonMembership")),
            ("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|fact| string(fact.readable_string())).collect())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::LiteralTupleProjectionMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("LiteralTupleProjectionMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PosAddPosIsPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NonnegativeSumIsNonnegative")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveLeftStrict(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StrictAdditiveLeftStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveRightStrict(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StrictAdditiveRightStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NonzeroProduct")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxListMembersLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMaxListMembersLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxConstructorPartsLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMaxConstructorPartsLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinListMembersLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMinListMembersLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinConstructorPartsLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetMinConstructorPartsLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonneg(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductNonnegativeBothNonneg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonpos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductNonnegativeBothNonpos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddCrossedLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedSubtrahendLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedMinuendLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedPositiveDenomLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedNegativeDenomLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowSharedExponentLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AbsVsSquareLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightNonnegativeShiftLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightNonnegativeShiftRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddLeftNonpositiveShiftLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddLeftNonpositiveShiftRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonpositiveToZero(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubNonpositiveToZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonnegativeFromZero(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubNonnegativeFromZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrMoreRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulScaleFactorOneOrMoreRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrLessLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulScaleFactorOneOrLessLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualAligned(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulComponentwiseLessEqualAligned")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualCrossed(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("MulComponentwiseLessEqualCrossed")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonNonnegativeFactorLessEqual(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CommonNonnegativeFactorLessEqual")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothPos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductPositiveBothPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothNeg(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ProductPositiveBothNeg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("QuotientPositiveSameSignPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignNeg(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("QuotientPositiveSameSignNeg")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseStrictLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddComponentwiseStrictRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedSubtrahendLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubSharedMinuendLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedPositiveDenomLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("DivSharedNegativeDenomLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowSharedExponentLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AbsVsSquareLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftStrict(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftLeftStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftLeftWeak")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightStrict(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftRightStrict")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightWeak(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("AddRightStrictShiftRightWeak")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveToZero(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubPositiveToZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveFromZero(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubPositiveFromZero")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CommonPositiveFactorLess")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetSizeInNumericCarrier(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSetSizeInNumericCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteExtremumSourceInCarrier(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteExtremumSourceInCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RefinedNumericCarrier")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureAdd(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureSub(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureMul(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureDiv(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosureDiv")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosurePow(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RealArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAdd(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureSub(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureMul(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureDiv(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureDiv")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosurePow(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAbs(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RationalArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAdd(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureSub(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMul(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMod(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureMod")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosurePowNat(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosurePowNat")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAbs(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntegerArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAdd(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureAdd")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureMul(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureSub(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureSub")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosurePow(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosurePow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAbs(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("NaturalArithmeticCarrierClosureAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddLeftPos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAddLeftPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddRightPos(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAddRightPos")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierMul(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierMul")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierPow(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierPow")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAbs(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierAbs")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierFiniteSetSize(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PositiveNaturalCarrierFiniteSetSize")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartMembership")),
            ("function_domain", super::function_domain::project_function_domain(&p.domain, runtime)),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionMembershipFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionMembershipFromRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowerSetMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RangeMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ClosedRangeMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntervalMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetBuilderMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StandardSetSubsetMembership(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StandardSetSubsetMembership")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnApplicationInCodomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FnApplicationInCodomain")),
            ("cite_signature_fact_id", string(p.cite_signature_fact_id.to_string())),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetSubsetFromMembers(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ListSetSubsetFromMembers")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionSubsetFromBothOperands")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectSubsetFromLeftOperand")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectSubsetFromRightOperand")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusSubsetFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubsetOfIntersectFromBothBounds")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnRangeFiniteFromDomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FnRangeFiniteFromDomain")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetFiniteFromBase(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PowerSetFiniteFromBase")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderFiniteFromParamSet(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetBuilderFiniteFromParamSet")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionFiniteFromBoth(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionFiniteFromBoth")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromBoth(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntersectFiniteFromBoth")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusFiniteFromLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SetMinusFiniteFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartFiniteFromFactors(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartFiniteFromFactors")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfFiniteSet(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SubsetOfFiniteSet")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeNonemptyFromEndpointOrder(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ClosedRangeNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeNonemptyFromEndpointOrder(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RangeNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalNonemptyFromEndpointOrder(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("IntervalNonemptyFromEndpointOrder")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromLeft(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionNonemptyFromLeft")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromRight(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("UnionNonemptyFromRight")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartNonemptyFromAllFactors(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("CartNonemptyFromAllFactors")),
            ("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnSetNonemptyFromCodomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FnSetNonemptyFromCodomain")),
            ("source_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.signature.clone())).readable_string())),
            ("source", super::function_domain::project_function_space_nonempty(&p.codomain_nonempty, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionGraphNonemptyFromDomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FunctionGraphNonemptyFromDomain")),
            ("source", super::function_domain::project_source(&p.source, runtime)),
            ("domain_comparison", super::function_domain::project_domain_nonempty(&p.domain_nonempty, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSpaceNonemptyFromEmptyDomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FunctionSpaceNonemptyFromEmptyDomain")),
            ("domain_comparison", super::function_domain::project_domain_empty(&p.domain_empty, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSeqSetNonemptyFromCodomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("FiniteSeqSetNonemptyFromCodomain")),
            ("source_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.signature.clone())).readable_string())),
            ("source", super::function_domain::project_function_space_nonempty(&p.codomain_nonempty, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SeqSetNonemptyFromCodomain(p) => object_for(runtime, vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SeqSetNonemptyFromCodomain")),
            ("source_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.signature.clone())).readable_string())),
            ("source", super::function_domain::project_function_space_nonempty(&p.codomain_nonempty, runtime)),
        ]),
    }
}

fn project_field_arithmetic_tree(tree: &FieldArithmeticCarrierConstructorTree, runtime: &Runtime) -> JsonValue {
    use FieldArithmeticCarrierConstructorTree::*;
    let binary = |kind, left, right| object_for(runtime, vec![
        ("constructor", string(kind)),
        ("left", project_field_arithmetic_tree(left, runtime)),
        ("right", project_field_arithmetic_tree(right, runtime)),
    ]);
    match tree {
        Leaf { requirement_index } => object_for(runtime, vec![
            ("constructor", string("leaf")),
            ("requirement_index", JsonValue::Number(*requirement_index as f64)),
        ]),
        Add { left, right } => binary("add", left, right),
        Sub { left, right } => binary("sub", left, right),
        Neg { argument } => object_for(runtime, vec![
            ("constructor", string("neg")),
            ("argument", project_field_arithmetic_tree(argument, runtime)),
        ]),
        Mul { left, right } => binary("mul", left, right),
        Div { left, right, nonzero_requirement_index } => object_for(runtime, vec![
            ("constructor", string("div")),
            ("left", project_field_arithmetic_tree(left, runtime)),
            ("right", project_field_arithmetic_tree(right, runtime)),
            ("nonzero_requirement_index", JsonValue::Number(*nonzero_requirement_index as f64)),
        ]),
    }
}
