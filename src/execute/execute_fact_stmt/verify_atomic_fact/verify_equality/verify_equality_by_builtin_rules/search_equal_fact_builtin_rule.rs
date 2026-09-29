use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Try equality builtin rules in order. First hit wins.
    // Definitional unfolds live in by_object_definition, not here.
    pub fn search_equal_fact_builtin_rule(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_equal_ir(fact, verify_state.clone())?
        {
            return Ok(Some(EqualitySearchProofByBuiltinRule::ByEqualIr(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_by_equal_to_obj_with_free_params_lookup(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRule::ByEqualToObjWithFreeParamsLookup(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_fn_set_alpha_equal(fact, verify_state.clone())?
        {
            return Ok(Some(EqualitySearchProofByBuiltinRule::ByFnSetAlphaEqual(
                proof,
            )));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_anonymous_fn_alpha_equal(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRule::ByAnonymousFnAlphaEqual(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_set_builder_alpha_equal(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRule::BySetBuilderAlphaEqual(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_calculation(fact, verify_state.clone())? {
            return Ok(Some(EqualitySearchProofByBuiltinRule::Calculation(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equal_from_known_difference_zero(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_power_laws(fact, verify_state.clone())?
        {
            return Ok(Some(map_power_law_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave2(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave2_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave3(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave3_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave4(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave4_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave5(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave5_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave6(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave6_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave7(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave7_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave8(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave8_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave9(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave9_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave10(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave10_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave11(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave11_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave12(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave12_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave13(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave13_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave14(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave14_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_equality_identities_wave15(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(map_equality_identities_wave15_proof(proof)));
        }
        if let Some(proof) = self
            .search_equal_fact_builtin_rule_closed_trig(fact, verify_state.clone())?
        {
            return Ok(Some(map_closed_trig_proof(proof)));
        }
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_inverse_trig(fact, verify_state)?
        {
            return Ok(Some(map_inverse_trig_proof(proof)));
        }
        Ok(None)
    }
}

fn map_power_law_proof(
    proof: super::by_power_laws::PowerLawEqualityBuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_power_laws::PowerLawEqualityBuiltinRuleProof as P;
    match proof {
        P::PowerProductSameBase(p) => EqualitySearchProofByBuiltinRule::PowerProductSameBase(p),
        P::PowerOfPower(p) => EqualitySearchProofByBuiltinRule::PowerOfPower(p),
        P::PowerOfProduct(p) => EqualitySearchProofByBuiltinRule::PowerOfProduct(p),
        P::ReciprocalAsNegOnePower(p) => {
            EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(p)
        }
        P::QuotientAsMulNegOnePower(p) => {
            EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(p)
        }
    }
}

fn map_equality_identities_wave2_proof(
    proof: super::by_equality_identities_wave2::EqualityIdentitiesWave2BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave2::EqualityIdentitiesWave2BuiltinRuleProof as W;
    match proof {
        W::OneToAnyPower(p) => EqualitySearchProofByBuiltinRule::OneToAnyPower(p),
        W::ZeroToPosNatPower(p) => EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(p),
        W::SqrtSquare(p) => EqualitySearchProofByBuiltinRule::SqrtSquare(p),
        W::SqrtZero(p) => EqualitySearchProofByBuiltinRule::SqrtZero(p),
        W::SqrtOne(p) => EqualitySearchProofByBuiltinRule::SqrtOne(p),
        W::SqrtOfSquare(p) => EqualitySearchProofByBuiltinRule::SqrtOfSquare(p),
        W::SqrtProduct(p) => EqualitySearchProofByBuiltinRule::SqrtProduct(p),
        W::SqrtQuotient(p) => EqualitySearchProofByBuiltinRule::SqrtQuotient(p),
        W::AbsOfNegation(p) => EqualitySearchProofByBuiltinRule::AbsOfNegation(p),
        W::AbsProduct(p) => EqualitySearchProofByBuiltinRule::AbsProduct(p),
        W::AbsSquare(p) => EqualitySearchProofByBuiltinRule::AbsSquare(p),
        W::LogBaseSelf(p) => EqualitySearchProofByBuiltinRule::LogBaseSelf(p),
        W::LogOfOne(p) => EqualitySearchProofByBuiltinRule::LogOfOne(p),
        W::LogOfPowerSameBase(p) => EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(p),
        W::LogArgPower(p) => EqualitySearchProofByBuiltinRule::LogArgPower(p),
        W::LogProduct(p) => EqualitySearchProofByBuiltinRule::LogProduct(p),
        W::LogQuotient(p) => EqualitySearchProofByBuiltinRule::LogQuotient(p),
        W::LogReciprocal(p) => EqualitySearchProofByBuiltinRule::LogReciprocal(p),
        W::LogChangeOfBase(p) => EqualitySearchProofByBuiltinRule::LogChangeOfBase(p),
        W::ZeroMod(p) => EqualitySearchProofByBuiltinRule::ZeroMod(p),
        W::ModOne(p) => EqualitySearchProofByBuiltinRule::ModOne(p),
        W::OneModAtLeastTwo(p) => EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(p),
        W::NestedSameModAbsorption(p) => {
            EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(p)
        }
        W::ModCompatibleSmallerModulus(p) => {
            EqualitySearchProofByBuiltinRule::ModCompatibleSmallerModulus(p)
        }
    }
}

fn map_equality_identities_wave3_proof(
    proof: super::by_equality_identities_wave3::EqualityIdentitiesWave3BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave3::EqualityIdentitiesWave3BuiltinRuleProof as W;
    match proof {
        W::MinIdempotent(p) => EqualitySearchProofByBuiltinRule::MinIdempotent(p),
        W::MaxIdempotent(p) => EqualitySearchProofByBuiltinRule::MaxIdempotent(p),
        W::MinCommutative(p) => EqualitySearchProofByBuiltinRule::MinCommutative(p),
        W::MaxCommutative(p) => EqualitySearchProofByBuiltinRule::MaxCommutative(p),
        W::AbsAbsAbsorption(p) => EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(p),
        W::ExpOfLn(p) => EqualitySearchProofByBuiltinRule::ExpOfLn(p),
        W::LnOfExp(p) => EqualitySearchProofByBuiltinRule::LnOfExp(p),
        W::FloorOfInteger(p) => EqualitySearchProofByBuiltinRule::FloorOfInteger(p),
        W::CeilOfInteger(p) => EqualitySearchProofByBuiltinRule::CeilOfInteger(p),
        W::ModSelfZero(p) => EqualitySearchProofByBuiltinRule::ModSelfZero(p),
    }
}

fn map_equality_identities_wave4_proof(
    proof: super::by_equality_identities_wave4::EqualityIdentitiesWave4BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave4::EqualityIdentitiesWave4BuiltinRuleProof as W;
    match proof {
        W::FloorOfCeilOfInteger(p) => EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(p),
        W::CeilOfFloorOfInteger(p) => EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(p),
        W::SqrtOfSquareEqualsAbs(p) => EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(p),
    }
}

fn map_equality_identities_wave5_proof(
    proof: super::by_equality_identities_wave5::EqualityIdentitiesWave5BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave5::EqualityIdentitiesWave5BuiltinRuleProof as W;
    match proof {
        W::QuotByOne(p) => EqualitySearchProofByBuiltinRule::QuotByOne(p),
        W::QuotSelfOne(p) => EqualitySearchProofByBuiltinRule::QuotSelfOne(p),
        W::LcmCommutative(p) => EqualitySearchProofByBuiltinRule::LcmCommutative(p),
        W::LcmIdempotentAbs(p) => EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(p),
        W::GcdCommutative(p) => EqualitySearchProofByBuiltinRule::GcdCommutative(p),
        W::GcdIdempotentAbs(p) => EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(p),
        W::GcdRightZeroAbs(p) => EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(p),
        W::GcdLeftZeroAbs(p) => EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(p),
        W::FactorialSuccessor(p) => EqualitySearchProofByBuiltinRule::FactorialSuccessor(p),
    }
}

fn map_equality_identities_wave6_proof(
    proof: super::by_equality_identities_wave6::EqualityIdentitiesWave6BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave6::EqualityIdentitiesWave6BuiltinRuleProof as W;
    match proof {
        W::AbsNonnegEqualsSelf(p) => EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(p),
        W::AbsNonposEqualsNegation(p) => {
            EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(p)
        }
        W::SignOfPositive(p) => EqualitySearchProofByBuiltinRule::SignOfPositive(p),
        W::SignOfNegative(p) => EqualitySearchProofByBuiltinRule::SignOfNegative(p),
        W::MaxRightWhenLessEqual(p) => EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(p),
        W::MaxLeftWhenLessEqual(p) => EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(p),
        W::MinLeftWhenLessEqual(p) => EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(p),
        W::MinRightWhenLessEqual(p) => EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(p),
    }
}

fn map_equality_identities_wave7_proof(
    proof: super::by_equality_identities_wave7::EqualityIdentitiesWave7BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave7::EqualityIdentitiesWave7BuiltinRuleProof as W;
    match proof {
        W::GcdDividesArgument(p) => EqualitySearchProofByBuiltinRule::GcdDividesArgument(p),
        W::ProductModFactorZero(p) => EqualitySearchProofByBuiltinRule::ProductModFactorZero(p),
        W::EqualityFromTwoSidedWeakOrder(p) => {
            EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(p)
        }
        W::DiffZeroFromEqualOperands(p) => {
            EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(p)
        }
        W::ZeroProductCancel(p) => EqualitySearchProofByBuiltinRule::ZeroProductCancel(p),
        W::SignOfNegation(p) => EqualitySearchProofByBuiltinRule::SignOfNegation(p),
        W::SignTimesAbsEqualsArg(p) => EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(p),
        W::AbsEqualsSignTimesArg(p) => EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(p),
        W::SignOfProduct(p) => EqualitySearchProofByBuiltinRule::SignOfProduct(p),
        W::SubtractionFromKnownAddition(p) => {
            EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(p)
        }
    }
}

fn map_equality_identities_wave8_proof(
    proof: super::by_equality_identities_wave8::EqualityIdentitiesWave8BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave8::EqualityIdentitiesWave8BuiltinRuleProof as W;
    match proof {
        W::QuotEuclideanDecomposition(p) => {
            EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(p)
        }
        W::ModDividendMinusRemainderZero(p) => {
            EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(p)
        }
        W::SquareSumComponentZero(p) => {
            EqualitySearchProofByBuiltinRule::SquareSumComponentZero(p)
        }
        W::MinusOneOddNaturalPower(p) => {
            EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(p)
        }
        W::LcmGcdProductAbs(p) => EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(p),
    }
}

fn map_equality_identities_wave9_proof(
    proof: super::by_equality_identities_wave9::EqualityIdentitiesWave9BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave9::EqualityIdentitiesWave9BuiltinRuleProof as W;
    match proof {
        W::UnionEmptyRight(p) => EqualitySearchProofByBuiltinRule::UnionEmptyRight(p),
        W::UnionEmptyLeft(p) => EqualitySearchProofByBuiltinRule::UnionEmptyLeft(p),
        W::IntersectEmptyRight(p) => EqualitySearchProofByBuiltinRule::IntersectEmptyRight(p),
        W::IntersectEmptyLeft(p) => EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(p),
        W::SetMinusSelfEmpty(p) => EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(p),
        W::SetMinusEmptyRight(p) => EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(p),
        W::SetMinusEmptyLeft(p) => EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(p),
        W::UnionCommutative(p) => EqualitySearchProofByBuiltinRule::UnionCommutative(p),
        W::IntersectCommutative(p) => EqualitySearchProofByBuiltinRule::IntersectCommutative(p),
        W::UnionIdempotent(p) => EqualitySearchProofByBuiltinRule::UnionIdempotent(p),
        W::IntersectIdempotent(p) => EqualitySearchProofByBuiltinRule::IntersectIdempotent(p),
        W::IntersectFromSubset(p) => EqualitySearchProofByBuiltinRule::IntersectFromSubset(p),
        W::EmptySetFromNotNonempty(p) => {
            EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(p)
        }
        W::PowerSetFiniteSetSize(p) => EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(p),
        W::UnionAssociative(p) => EqualitySearchProofByBuiltinRule::UnionAssociative(p),
        W::IntersectAssociative(p) => EqualitySearchProofByBuiltinRule::IntersectAssociative(p),
        W::IntersectUnionDistributive(p) => {
            EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(p)
        }
        W::SetMinusUnionDeMorgan(p) => EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(p),
        W::SetMinusIntersectDeMorgan(p) => {
            EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(p)
        }
        W::IntersectSetMinusSelfEmpty(p) => {
            EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(p)
        }
    }
}

fn map_equality_identities_wave10_proof(
    proof: super::by_equality_identities_wave10::EqualityIdentitiesWave10BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave10::EqualityIdentitiesWave10BuiltinRuleProof as W;
    match proof {
        W::FiniteSetSumEmpty(p) => EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(p),
        W::FiniteSetProductEmpty(p) => EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(p),
        W::FiniteSetReduceEmpty(p) => EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(p),
        W::ReduceEmpty(p) => EqualitySearchProofByBuiltinRule::ReduceEmpty(p),
        W::SumEmptyRange(p) => EqualitySearchProofByBuiltinRule::SumEmptyRange(p),
        W::ProductEmptyRange(p) => EqualitySearchProofByBuiltinRule::ProductEmptyRange(p),
    }
}


fn map_equality_identities_wave11_proof(
    proof: super::by_equality_identities_wave11::EqualityIdentitiesWave11BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave11::EqualityIdentitiesWave11BuiltinRuleProof as W;
    match proof {
        W::UnionAbsorptionFromSubset(p) => EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(p),
        W::SetMinusRecoversSubset(p) => EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(p),
        W::EmptySetFromSizeZero(p) => EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(p),
        W::CartProjFactor(p) => EqualitySearchProofByBuiltinRule::CartProjFactor(p),
        W::TupleComponentAtIndex(p) => EqualitySearchProofByBuiltinRule::TupleComponentAtIndex(p),
        W::FiniteSetSizeSetMinus(p) => EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(p),
        W::FiniteSetSizeUnion(p) => EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(p),
        W::ClosedRangeSingletonListSet(p) => EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(p),
        W::SumSingleTerm(p) => EqualitySearchProofByBuiltinRule::SumSingleTerm(p),
        W::ProductSingleTerm(p) => EqualitySearchProofByBuiltinRule::ProductSingleTerm(p),
        W::ReduceAddZeroEqualsSum(p) => EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(p),
        W::FiniteSetReduceAddZeroEqualsSum(p) => EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(p),
        W::PowOfLogInverse(p) => EqualitySearchProofByBuiltinRule::PowOfLogInverse(p),
    }
}

fn map_equality_identities_wave12_proof(
    proof: super::by_equality_identities_wave12::EqualityIdentitiesWave12BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave12::EqualityIdentitiesWave12BuiltinRuleProof as W;
    match proof {
        W::UnionSetMinusDecomposition(p) => {
            EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(p)
        }
        W::SetMinusIntersectSelf(p) => EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(p),
        W::ReOfImaginaryUnit(p) => EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(p),
        W::ImgOfImaginaryUnit(p) => EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(p),
        W::ReOfRealEmbedding(p) => EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(p),
        W::ImgOfRealEmbedding(p) => EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(p),
        W::ReOfRealPlusI(p) => EqualitySearchProofByBuiltinRule::ReOfRealPlusI(p),
        W::ImgOfRealPlusI(p) => EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(p),
        W::ComplexAbsOfImaginaryUnit(p) => {
            EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(p)
        }
        W::ModNestedDivisibleAbsorption(p) => {
            EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(p)
        }
        W::SumSplitLastTerm(p) => EqualitySearchProofByBuiltinRule::SumSplitLastTerm(p),
        W::ProductSplitLastTerm(p) => EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(p),
        W::FiniteSetSumListExpansion(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(p)
        }
        W::FiniteSetProductListExpansion(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(p)
        }
    }
}

fn map_equality_identities_wave13_proof(
    proof: super::by_equality_identities_wave13::EqualityIdentitiesWave13BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave13::EqualityIdentitiesWave13BuiltinRuleProof as W;
    match proof {
        W::EulerEqualsExpOne(p) => EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(p),
        W::LnOfEuler(p) => EqualitySearchProofByBuiltinRule::LnOfEuler(p),
        W::ReOfReal(p) => EqualitySearchProofByBuiltinRule::ReOfReal(p),
        W::ImgOfReal(p) => EqualitySearchProofByBuiltinRule::ImgOfReal(p),
        W::ReOfRealPlusImagScaled(p) => {
            EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(p)
        }
        W::ImgOfRealPlusImagScaled(p) => {
            EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(p)
        }
        W::ComplexAbsOfNonnegReal(p) => {
            EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(p)
        }
        W::ComplexAbsOfImagScaled(p) => {
            EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(p)
        }
        W::ClosedRangeLiteralExpansion(p) => {
            EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(p)
        }
        W::RangeLiteralExpansion(p) => EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(p),
        W::PowerSetOfEmpty(p) => EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(p),
        W::PowerSetOfSingleton(p) => EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(p),
        W::FamilyUnionOfEmpty(p) => EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(p),
        W::CartWithEmptyFactor(p) => EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(p),
        W::UnionOverIntersectDistributive(p) => {
            EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(p)
        }
        W::SetMinusChainToUnion(p) => EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(p),
        W::FnRangeOfConstantAnonymousFn(p) => {
            EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p)
        }
        W::SeqEqualsFnOnN(p) => EqualitySearchProofByBuiltinRule::SeqEqualsFnOnN(p),
        W::FiniteSeqEqualsFnOnClosedRange(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnClosedRange(p)
        }
    }
}

fn map_equality_identities_wave14_proof(
    proof: super::by_equality_identities_wave14::EqualityIdentitiesWave14BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave14::EqualityIdentitiesWave14BuiltinRuleProof as W;
    match proof {
        W::IndexUnionEmptyIndex(p) => EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(p),
        W::IndexIntersectEmptyIndex(p) => {
            EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(p)
        }
        W::IndexCartEmptyIndex(p) => EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(p),
        W::IndexUnionSingleton(p) => EqualitySearchProofByBuiltinRule::IndexUnionSingleton(p),
        W::FiniteSeqZeroEqualsFnOnEmpty(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(p)
        }
        W::SetBuilderObviouslyEmpty(p) => {
            EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(p)
        }
        W::ComplexAbsSquaredOfRectForm(p) => {
            EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(p)
        }
        W::ExpOfSum(p) => EqualitySearchProofByBuiltinRule::ExpOfSum(p),
        W::LogBasePower(p) => EqualitySearchProofByBuiltinRule::LogBasePower(p),
        W::ReOfProduct(p) => EqualitySearchProofByBuiltinRule::ReOfProduct(p),
        W::ImgOfProduct(p) => EqualitySearchProofByBuiltinRule::ImgOfProduct(p),
        W::SinOfSum(p) => EqualitySearchProofByBuiltinRule::SinOfSum(p),
        W::CosOfSum(p) => EqualitySearchProofByBuiltinRule::CosOfSum(p),
        W::ReduceSingleTermWithAddZero(p) => {
            EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(p)
        }
    }
}

fn map_equality_identities_wave15_proof(
    proof: super::by_equality_identities_wave15::EqualityIdentitiesWave15BuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_equality_identities_wave15::EqualityIdentitiesWave15BuiltinRuleProof as W;
    match proof {
        W::FiniteSetSumFubiniSwap(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(p)
        }
        W::FiniteSetSumOverCartesianProduct(p) => {
            EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(p)
        }
    }
}

fn map_closed_trig_proof(
    proof: super::by_closed_trig::ClosedTrigEqualityBuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_closed_trig::ClosedTrigEqualityBuiltinRuleProof as C;
    match proof {
        C::SinOfZero(p) => EqualitySearchProofByBuiltinRule::SinOfZero(p),
        C::CosOfZero(p) => EqualitySearchProofByBuiltinRule::CosOfZero(p),
        C::TanOfZero(p) => EqualitySearchProofByBuiltinRule::TanOfZero(p),
        C::SinOfHalfPi(p) => EqualitySearchProofByBuiltinRule::SinOfHalfPi(p),
        C::CosOfPi(p) => EqualitySearchProofByBuiltinRule::CosOfPi(p),
        C::SinOfPi(p) => EqualitySearchProofByBuiltinRule::SinOfPi(p),
        C::CotOfHalfPi(p) => EqualitySearchProofByBuiltinRule::CotOfHalfPi(p),
        C::PythagoreanIdentity(p) => EqualitySearchProofByBuiltinRule::PythagoreanIdentity(p),
    }
}

fn map_inverse_trig_proof(
    proof: super::by_inverse_trig::InverseTrigEqualityBuiltinRuleProof,
) -> EqualitySearchProofByBuiltinRule {
    use super::by_inverse_trig::InverseTrigEqualityBuiltinRuleProof as I;
    match proof {
        I::SinArcsinLeftInverse(p) => EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(p),
        I::CosArccosLeftInverse(p) => EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(p),
        I::TanArctanLeftInverse(p) => EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(p),
        I::CotArccotLeftInverse(p) => EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(p),
        I::ArcsinSinRightInverse(p) => EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(p),
        I::ArccosCosRightInverse(p) => EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(p),
        I::ArctanTanRightInverse(p) => EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(p),
        I::ArccotCotRightInverse(p) => EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(p),
        I::ArcsinExactZero(p) => EqualitySearchProofByBuiltinRule::ArcsinExactZero(p),
        I::ArcsinExactOne(p) => EqualitySearchProofByBuiltinRule::ArcsinExactOne(p),
        I::ArcsinExactNegOne(p) => EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(p),
        I::ArccosExactOne(p) => EqualitySearchProofByBuiltinRule::ArccosExactOne(p),
        I::ArccosExactZero(p) => EqualitySearchProofByBuiltinRule::ArccosExactZero(p),
        I::ArccosExactNegOne(p) => EqualitySearchProofByBuiltinRule::ArccosExactNegOne(p),
        I::ArctanExactZero(p) => EqualitySearchProofByBuiltinRule::ArctanExactZero(p),
        I::ArccotExactZero(p) => EqualitySearchProofByBuiltinRule::ArccotExactZero(p),
    }
}
