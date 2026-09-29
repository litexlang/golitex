//! Generated equality builtin-rule detailed projection.
use super::store::project_verify_facts;
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::json_output::helper::{object, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_equality_builtin_rule(rule: &EqualitySearchProofByBuiltinRule, runtime: &Runtime) -> JsonValue {
    match rule {
        EqualitySearchProofByBuiltinRule::ByEqualIr(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ByEqualIr"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ByEqualToObjWithFreeParamsLookup(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ByEqualToObjWithFreeParamsLookup"))];
            entries.push(("cite_fact_id", string(p.cite_index_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_index_fact_id) { entries.push(("cite", string(fact.readable_string()))); }
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ByFnSetAlphaEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ByFnSetAlphaEqual"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ByAnonymousFnAlphaEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ByAnonymousFnAlphaEqual"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::BySetBuilderAlphaEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("BySetBuilderAlphaEqual"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::Calculation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("Calculation"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinArcsinLeftInverse"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosArccosLeftInverse"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("TanArctanLeftInverse"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CotArccotLeftInverse"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinSinRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosCosRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArctanTanRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccotCotRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactNegOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactNegOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactNegOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArctanExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArctanExactZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ArccotExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccotExactZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerProductSameBase(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerProductSameBase"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerOfPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerOfPower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerOfProduct"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReciprocalAsNegOnePower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotientAsMulNegOnePower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::OneToAnyPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("OneToAnyPower"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroToPosNatPower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtSquare"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOfSquare"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtProduct"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtQuotient(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtQuotient"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsOfNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsOfNegation"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsProduct"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsSquare"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogBaseSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogBaseSelf"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogOfOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogOfOne"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogOfPowerSameBase"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogArgPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogArgPower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogProduct"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogQuotient(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogQuotient"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogReciprocal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogReciprocal"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogChangeOfBase(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogChangeOfBase"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ZeroMod(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroMod"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ModOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("OneModAtLeastTwo"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("NestedSameModAbsorption"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MinIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinIdempotent"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MaxIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxIdempotent"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MinCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MaxCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsAbsAbsorption"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ExpOfLn(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ExpOfLn"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LnOfExp(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LnOfExp"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FloorOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FloorOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CeilOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CeilOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ModSelfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModSelfZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FloorOfCeilOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CeilOfFloorOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOfSquareEqualsAbs"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::QuotByOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotByOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::QuotSelfOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotSelfOne"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LcmCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmIdempotentAbs"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::GcdCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdIdempotentAbs"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdRightZeroAbs"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdLeftZeroAbs"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FactorialSuccessor(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FactorialSuccessor"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsNonnegEqualsSelf"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsNonposEqualsNegation"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfPositive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfPositive"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfNegative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfNegative"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxRightWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxLeftWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinLeftWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinRightWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::GcdDividesArgument(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdDividesArgument"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ProductModFactorZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductModFactorZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EqualityFromTwoSidedWeakOrder"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("DiffZeroFromEqualOperands"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EqualFromKnownDifferenceZero"))];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) { entries.push(("cite", string(fact.readable_string()))); }
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ZeroProductCancel(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroProductCancel"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfNegation"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignTimesAbsEqualsArg"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsEqualsSignTimesArg"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfProduct"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SubtractionFromKnownAddition"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotEuclideanDecomposition"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModDividendMinusRemainderZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SquareSumComponentZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SquareSumComponentZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinusOneOddNaturalPower"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmGcdProductAbs"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionEmptyRight"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionEmptyLeft"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectEmptyRight"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectEmptyLeft"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusSelfEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusEmptyRight"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusEmptyLeft"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectCommutative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionIdempotent"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectIdempotent"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectFromSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EmptySetFromNotNonempty"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetFiniteSetSize"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionAssociative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionAssociative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectAssociative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectAssociative"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectUnionDistributive"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusUnionDeMorgan"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusIntersectDeMorgan"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectSetMinusSelfEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetProductEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetReduceEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceEmpty"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SumEmptyRange(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumEmptyRange"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ProductEmptyRange(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductEmptyRange"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionAbsorptionFromSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusRecoversSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EmptySetFromSizeZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CartProjFactor(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CartProjFactor"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::TupleComponentAtIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("TupleComponentAtIndex"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSizeSetMinus"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSizeUnion"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ClosedRangeSingletonListSet"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SumSingleTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumSingleTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ProductSingleTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductSingleTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceAddZeroEqualsSum"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetReduceAddZeroEqualsSum"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowOfLogInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowOfLogInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionSetMinusDecomposition"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusIntersectSelf"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfImaginaryUnit"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfImaginaryUnit"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealEmbedding"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealEmbedding"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusI(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealPlusI"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealPlusI"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfImaginaryUnit"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModNestedDivisibleAbsorption"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SumSplitLastTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumSplitLastTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductSplitLastTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumListExpansion"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetProductListExpansion"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EulerEqualsExpOne"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LnOfEuler(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LnOfEuler"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfReal"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfReal"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealPlusImagScaled"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealPlusImagScaled"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfNonnegReal"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfImagScaled"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ClosedRangeLiteralExpansion"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("RangeLiteralExpansion"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetOfEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetOfSingleton"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FamilyUnionOfEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CartWithEmptyFactor"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionOverIntersectDistributive"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusChainToUnion"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FnRangeOfConstantAnonymousFn"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SeqEqualsFnOnN(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SeqEqualsFnOnN"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnClosedRange(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSeqEqualsFnOnClosedRange"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexUnionEmptyIndex"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexIntersectEmptyIndex"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexCartEmptyIndex"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::IndexUnionSingleton(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexUnionSingleton"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSeqZeroEqualsFnOnEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetBuilderObviouslyEmpty"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsSquaredOfRectForm"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ExpOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ExpOfSum"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::LogBasePower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogBasePower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfProduct"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfProduct"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfSum"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfSum"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceSingleTermWithAddZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumFubiniSwap"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumOverCartesianProduct"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::TanOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("TanOfZero"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfHalfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfHalfPi"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfPi"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfPi"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::CotOfHalfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CotOfHalfPi"))];
            let _ = p;
            object(entries)
        },
        EqualitySearchProofByBuiltinRule::PythagoreanIdentity(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PythagoreanIdentity"))];
            let _ = p;
            object(entries)
        },
    }
}
