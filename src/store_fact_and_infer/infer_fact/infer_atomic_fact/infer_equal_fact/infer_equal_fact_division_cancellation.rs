use crate::prelude::*;

impl Runtime {
    // Checked scalar quotients cancel a same-position operand only.
    // a/k=b/k => a=b requires k!=0; k/a=k/b => a=b requires k,a,b!=0.
    pub(super) fn infer_equal_fact_division_cancellation(
        &mut self,
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::InferEqualityResult>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(right)),
        ) = (&source.left, &source.right)
        else {
            return Ok(Vec::new());
        };
        let premise_state = state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        let mut rules = Vec::new();
        if left.right.ir() == right.right.ir() {
            if let Some(rule) = self.infer_equal_fact_common_denominator_cancellation(
                source,
                &left.left,
                &right.left,
                &left.right,
                premise_state,
                state,
            )? {
                rules.push(rule);
            }
        }
        if left.left.ir() == right.left.ir() {
            if let Some(rule) = self.infer_equal_fact_nonzero_numerator_cancellation(
                source,
                &left.right,
                &right.right,
                &left.left,
                premise_state,
                state,
            )? {
                rules.push(rule);
            }
        }
        Ok(rules)
    }

    fn infer_equal_fact_common_denominator_cancellation(
        &mut self,
        source: &EqualFact,
        left: &Obj,
        right: &Obj,
        common: &Obj,
        premise_state: VerifyState,
        state: VerifyState,
    ) -> RuntimeResult<Option<crate::store_fact_and_infer::InferEqualityResult>> {
        if self.cancellation_equality_already_known(left, right) {
            return Ok(None);
        }
        let Some([left_in_c_proof, right_in_c_proof, common_in_c_proof]) =
            self.cancellation_scalar_proofs([left, right, common], source, premise_state)?
        else {
            return Ok(None);
        };
        let denominator_nonzero_proof =
            self.cancellation_nonzero_proof(common, source, premise_state)?;
        if denominator_nonzero_proof.is_failed() {
            return Ok(None);
        }
        let equality: Fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: source.line_file.clone(),
        }
        .into();
        let Some(derived) = self.try_store_inferred_fact(&equality, state)? else {
            return Ok(None);
        };
        Ok(Some(
            crate::store_fact_and_infer::InferEqualityResult::CommonDenominatorCancellation(
                crate::store_fact_and_infer::InferEqualFactCommonDenominatorCancellationResult::new(
                    source.fact_id,
                    common.clone(),
                    left_in_c_proof,
                    right_in_c_proof,
                    common_in_c_proof,
                    denominator_nonzero_proof,
                    derived,
                ),
            ),
        ))
    }

    fn infer_equal_fact_nonzero_numerator_cancellation(
        &mut self,
        source: &EqualFact,
        left: &Obj,
        right: &Obj,
        common: &Obj,
        premise_state: VerifyState,
        state: VerifyState,
    ) -> RuntimeResult<Option<crate::store_fact_and_infer::InferEqualityResult>> {
        if self.cancellation_equality_already_known(left, right) {
            return Ok(None);
        }
        let Some([left_in_c_proof, right_in_c_proof, common_in_c_proof]) =
            self.cancellation_scalar_proofs([left, right, common], source, premise_state)?
        else {
            return Ok(None);
        };
        let numerator_nonzero_proof =
            self.cancellation_nonzero_proof(common, source, premise_state)?;
        if numerator_nonzero_proof.is_failed() {
            return Ok(None);
        }
        let left_denominator_nonzero_proof =
            self.cancellation_nonzero_proof(left, source, premise_state)?;
        if left_denominator_nonzero_proof.is_failed() {
            return Ok(None);
        }
        let right_denominator_nonzero_proof =
            self.cancellation_nonzero_proof(right, source, premise_state)?;
        if right_denominator_nonzero_proof.is_failed() {
            return Ok(None);
        }
        let equality: Fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: source.line_file.clone(),
        }
        .into();
        let Some(derived) = self.try_store_inferred_fact(&equality, state)? else {
            return Ok(None);
        };
        Ok(Some(
            crate::store_fact_and_infer::InferEqualityResult::NonzeroNumeratorCancellation(
                crate::store_fact_and_infer::InferEqualFactNonzeroNumeratorCancellationResult::new(
                    source.fact_id,
                    common.clone(),
                    left_in_c_proof,
                    right_in_c_proof,
                    common_in_c_proof,
                    numerator_nonzero_proof,
                    left_denominator_nonzero_proof,
                    right_denominator_nonzero_proof,
                    derived,
                ),
            ),
        ))
    }
}
