use super::helper::cancellation_candidates;
use crate::prelude::*;

impl Runtime {
    // Stored scalar products sharing a direct, certified nonzero factor cancel.
    // Example: k != 0, a * k = b * k => a = b; no later-premise retrigger.
    pub(super) fn infer_equal_fact_nonzero_factor_cancellation(
        &mut self,
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::InferEqualityResult>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(right)),
        ) = (&source.left, &source.right)
        else {
            return Ok(Vec::new());
        };
        let mut rules = Vec::new();
        let premise_state = state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        for (left, right, common) in
            cancellation_candidates([&left.left, &left.right], [&right.left, &right.right])
        {
            if self.cancellation_equality_already_known(&left, &right) {
                continue;
            }
            let Some([left_in_c_proof, right_in_c_proof, common_in_c_proof]) =
                self.cancellation_scalar_proofs([&left, &right, &common], source, premise_state)?
            else {
                continue;
            };
            let factor_nonzero_proof =
                self.cancellation_nonzero_proof(&common, source, premise_state)?;
            if factor_nonzero_proof.is_failed() {
                continue;
            }
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: source.line_file.clone(),
            }
            .into();
            let Some(derived) = self.try_store_inferred_fact(&equality, state)? else {
                continue;
            };
            rules.push(
                crate::store_fact_and_infer::InferEqualityResult::NonzeroFactorCancellation(
                    crate::store_fact_and_infer::InferEqualFactNonzeroFactorCancellationResult::new(
                        source.fact_id,
                        common,
                        left_in_c_proof,
                        right_in_c_proof,
                        common_in_c_proof,
                        factor_nonzero_proof,
                        derived,
                    ),
                ),
            );
        }
        Ok(rules)
    }
}
