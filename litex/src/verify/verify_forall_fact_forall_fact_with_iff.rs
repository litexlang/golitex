use crate::error::{RuntimeError, VerifyError};
use crate::execute::Runtime;
use crate::fact::{ForallFact, ForallFactWithIff};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Runtime<'a> {
    /// Declare params, assume dom facts hold, then verify each then_fact.
    pub fn verify_forall_fact(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let fact_display_string = forall_fact.to_string();
        let fact_line_file = forall_fact.line_file;

        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact_display_string, fact_line_file)
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_forall_fact_well_defined(forall_fact, verify_state) {
                return Err(VerifyError::new(
                    fact_display_string,
                    Some(RuntimeError::WellDefinedError(e)),
                    fact_line_file,
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        self.runtime_context.push_env();
        let result = self.verify_forall_fact_body(forall_fact, &verify_state_for_children);
        self.runtime_context.pop_env();

        result
    }

    fn verify_forall_fact_body(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut infer_result = InferResult::new();
        for param_def in forall_fact.params_def_with_type.iter() {
            let param_infer_result = self
                .define_params_with_type(std::slice::from_ref(param_def), false)
                .map_err(|e| {
                    VerifyError::new(
                        format!("failed to define params in forall: {}", e.body_string()),
                        Some(RuntimeError::ExecError(e)),
                        forall_fact.line_file,
                    )
                })?;
            infer_result.new_infer_result_inside(param_infer_result);
        }

        for dom_fact in forall_fact.dom_facts.iter() {
            let dom_infer_result = self
                .store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact,
                )
                .map_err(|e| {
                    VerifyError::new(
                        format!("failed to assume dom fact in forall: {}", e.body_string()),
                        Some(RuntimeError::StoreFactError(e)),
                        forall_fact.line_file,
                    )
                })?;
            infer_result.new_infer_result_inside(dom_infer_result);
        }

        for then_fact in forall_fact.then_facts.iter() {
            let result = self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                forall_fact.to_string(),
                "forall: each then_fact verified under dom".to_string(),
                infer_result,
                forall_fact.line_file,
                crate::common::defaults::DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }

    /// Forall iff: two steps. Step 1: take then as part of dom, verify iff. Step 2: take iff as part of dom, verify then.
    pub fn verify_forall_fact_with_iff(
        &mut self,
        forall_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let fact_display_string = forall_iff.to_string();
        let line_file = forall_iff.line_file;

        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact_display_string, line_file)
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_forall_fact_with_iff_well_defined(forall_iff, verify_state)
            {
                return Err(VerifyError::new(
                    fact_display_string.clone(),
                    Some(RuntimeError::WellDefinedError(e)),
                    line_file,
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let f = &forall_iff.forall_fact;

        let mut dom_then = f.dom_facts.clone();
        dom_then.extend(f.then_facts.clone());
        let forall_then_implies_iff = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_then,
            forall_iff.iff_facts.clone(),
            line_file,
        );
        let result1 =
            self.verify_forall_fact(&forall_then_implies_iff, &verify_state_for_children)?;
        if result1.is_unknown() {
            return Ok(result1);
        }

        let mut dom_iff = f.dom_facts.clone();
        dom_iff.extend(forall_iff.iff_facts.clone());
        let forall_iff_implies_then = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_iff,
            f.then_facts.clone(),
            line_file,
        );
        let result2 =
            self.verify_forall_fact(&forall_iff_implies_then, &verify_state_for_children)?;
        if result2.is_unknown() {
            return Ok(result2);
        }

        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                fact_display_string,
                "forall iff: then=>iff and iff=>then verified".to_string(),
                InferResult::new(),
                line_file,
                crate::common::defaults::DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }
}
