use crate::prelude::*;

impl Runtime {
    // Stored scalar differences sharing a minuend or subtrahend cancel.
    // Examples: a-k=b-k => a=b; k-a=k-b => a=b. Crossed positions do not cancel.
    pub(super) fn infer_equal_fact_subtractive_cancellation(
        &mut self,
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::InferEqualityResult>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(right)),
        ) = (&source.left, &source.right)
        else {
            return Ok(Vec::new());
        };
        let mut candidates = Vec::new();
        if left.right.ir() == right.right.ir() {
            candidates.push((left.left.as_ref(), right.left.as_ref(), left.right.as_ref()));
        }
        if left.left.ir() == right.left.ir() {
            candidates.push((
                left.right.as_ref(),
                right.right.as_ref(),
                left.left.as_ref(),
            ));
        }
        let premise_state = state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        let mut rules = Vec::new();
        for (left, right, common) in candidates {
            if self.cancellation_equality_already_known(left, right) {
                continue;
            }
            let Some([left_in_c_proof, right_in_c_proof, common_in_c_proof]) =
                self.cancellation_scalar_proofs([left, right, common], source, premise_state)?
            else {
                continue;
            };
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: left.clone(),
                right: right.clone(),
                line_file: source.line_file.clone(),
            }
            .into();
            let Some(derived) = self.try_store_inferred_fact_and_infer(&equality, state)? else {
                continue;
            };
            rules.push(
                crate::store_fact_and_infer::InferEqualityResult::SubtractiveCancellation(
                    crate::store_fact_and_infer::InferEqualFactSubtractiveCancellationResult::new(
                        source.fact_id,
                        common.clone(),
                        left_in_c_proof,
                        right_in_c_proof,
                        common_in_c_proof,
                        derived,
                    ),
                ),
            );
        }
        Ok(rules)
    }
}
