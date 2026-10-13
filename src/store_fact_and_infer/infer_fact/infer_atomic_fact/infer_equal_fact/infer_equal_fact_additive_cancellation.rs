use super::helper::cancellation_candidates;
use crate::prelude::*;

impl Runtime {
    // Stored scalar sums sharing a direct addend publish the remaining equality.
    // Example: a + k = b + k => a = b; all four addend positions are allowed.
    pub(super) fn infer_equal_fact_additive_cancellation(
        &mut self,
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::InferEqualFactResult>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(right)),
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
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: source.line_file.clone(),
            }
            .into();
            let derived = self.store_inferred_fact(&equality)?;
            rules.push(
                crate::store_fact_and_infer::InferEqualFactResult::AdditiveCancellation(
                    crate::store_fact_and_infer::InferEqualFactAdditiveCancellationResult::new(
                        source.fact_id,
                        common,
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
