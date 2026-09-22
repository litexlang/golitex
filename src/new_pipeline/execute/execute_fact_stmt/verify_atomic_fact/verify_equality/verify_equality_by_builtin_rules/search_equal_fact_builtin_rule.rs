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
            self.search_equal_fact_builtin_rule_inverse_trig(fact, verify_state)?
        {
            return Ok(Some(map_inverse_trig_proof(proof)));
        }
        Ok(None)
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
