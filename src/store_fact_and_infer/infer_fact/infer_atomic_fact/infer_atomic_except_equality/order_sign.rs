use crate::ast::fact::{AtomicFact, Fact, GreaterEqualFact, InFact, LessEqualFact, LessFact};
use crate::ast::obj::{Literal, Number, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{InferStrictLowerBoundPositiveResult, InferWeakIntegerLowerBoundInNResult};

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

    // Stored b <= n (or n >= b), n in Z and b >= 0 imply n in N.
    // Example: the integer induction domain n >= 0 publishes its N carrier
    // before nested function WD. Only bounded existing certificates are used.
    pub(super) fn infer_weak_integer_lower_bound_in_n(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InferWeakIntegerLowerBoundInNResult>> {
        let (bound, value, source_fact_id, line_file) = match fact {
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, f.fact_id, f.line_file.clone()),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, f.fact_id, f.line_file.clone()),
            _ => return Ok(None),
        };
        let natural = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: value.clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: line_file.clone(),
        });
        // N membership itself publishes a nonnegative bound. Do not cycle
        // back to an already stored membership through that projection.
        let natural_key = (natural.prop_name(), true);
        let natural_ir = natural.ir();
        let already_stored = self.execution_environments_stack.iter().rev().any(|env| {
            match env.facts.known_atomic_except_equality_facts.by_prop.get(&natural_key) {
                Some(knowns) => knowns.iter().any(|known| known.ir() == natural_ir),
                None => false,
            }
        });
        if already_stored {
            return Ok(None);
        }
        let integer: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: value.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: line_file.clone(),
        }.into();
        let premise_state = verify_state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        let integer_proof = self.verify_fact(&integer, premise_state)?;
        if integer_proof.is_failed() {
            return Ok(None);
        }
        let zero = Obj::Literal(Literal::Number(Number { normalized_value: "0".into() }));
        let nonnegative: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero.clone(),
            right: bound.clone(),
            line_file: line_file.clone(),
        }.into();
        let mut bound_nonnegative_proof = self.verify_fact(&nonnegative, premise_state)?;
        if bound_nonnegative_proof.is_failed() {
            let nonnegative_dual: Fact = GreaterEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: bound.clone(),
                right: zero,
                line_file,
            }.into();
            bound_nonnegative_proof = self.verify_fact(&nonnegative_dual, premise_state)?;
            if bound_nonnegative_proof.is_failed() {
                return Ok(None);
            }
        }
        let derived = Box::new(self.store_inferred_fact_and_infer(&natural.into(), verify_state)?);
        Ok(Some(InferWeakIntegerLowerBoundInNResult {
            source_fact_id,
            integer_proof,
            bound_nonnegative_proof,
            derived,
        }))
    }
}
