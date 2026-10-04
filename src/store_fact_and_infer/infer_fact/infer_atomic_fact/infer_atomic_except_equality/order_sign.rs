use crate::ast::fact::{AtomicFact, Fact, LessEqualFact, LessFact};
use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferStrictLowerBoundPositiveResult;

impl Runtime {
    // Stored b < x (or x > b), with an available 0 <= b certificate, gives 0 < x.
    // Example: 1 < x publishes positivity before log(x) WD needs it.
    // No strategy/forall search for the bound and no permission reset.
    pub(super) fn infer_strict_lower_bound_positive(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InferStrictLowerBoundPositiveResult>> {
        let (bound, value, source_fact_id, line_file) = match fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, f.fact_id, f.line_file.clone()),
            AtomicFact::GreaterFact(f) => (&f.right, &f.left, f.fact_id, f.line_file.clone()),
            _ => return Ok(None),
        };
        let zero = Obj::Literal(Literal::Number(Number { normalized_value: "0".into() }));
        // Already a positivity fact: do not infer the same fact recursively.
        if bound.ir() == zero.ir() {
            return Ok(None);
        }
        let nonnegative: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero.clone(),
            right: bound.clone(),
            line_file: line_file.clone(),
        }.into();
        let bound_nonnegative_proof = self.verify_fact(
            &nonnegative,
            verify_state.capped_at(VerifyStateLevel::KnownSpecialProperty),
        )?;
        if bound_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let positive: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero,
            right: value.clone(),
            line_file,
        }.into();
        let derived = Box::new(self.store_inferred_fact_and_infer(&positive, verify_state)?);
        Ok(Some(InferStrictLowerBoundPositiveResult {
            source_fact_id,
            bound_nonnegative_proof,
            derived,
        }))
    }
}
