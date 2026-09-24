use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

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
