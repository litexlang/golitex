use crate::prelude::*;

// The four direct shared-operand positions; no alias or AC search.
pub(super) fn cancellation_candidates(left: [&Obj; 2], right: [&Obj; 2]) -> Vec<(Obj, Obj, Obj)> {
    let mut candidates = Vec::new();
    for i in 0..2 {
        for j in 0..2 {
            if left[i].ir() == right[j].ir() {
                candidates.push((left[1 - i].clone(), right[1 - j].clone(), left[i].clone()));
            }
        }
    }
    candidates
}

impl Runtime {
    pub(super) fn cancellation_nonzero_proof(
        &mut self,
        operand: &Obj,
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact: Fact = NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: operand.clone(),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: "0".into(),
            })),
            line_file: source.line_file.clone(),
        }
        .into();
        self.verify_fact(&fact, state)
    }

    pub(super) fn cancellation_equality_already_known(&self, left: &Obj, right: &Obj) -> bool {
        let left = left.ir();
        let right = right.ir();
        self.execution_environments_stack.iter().rev().any(|env| {
            env.facts
                .known_equivalence_classes
                .same_class(&left, &right)
        })
    }

    pub(super) fn cancellation_scalar_proofs(
        &mut self,
        operands: [&Obj; 3],
        source: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<[VerifyFactResult; 3]>> {
        let mut proofs = Vec::new();
        for operand in operands {
            let membership: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: operand.clone(),
                set: Obj::StandardSet(StandardSet::C),
                line_file: source.line_file.clone(),
            }
            .into();
            let proof = self.verify_fact(&membership, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        let mut proofs = proofs.into_iter();
        Ok(Some([
            proofs.next().expect("left scalar proof"),
            proofs.next().expect("right scalar proof"),
            proofs.next().expect("shared scalar proof"),
        ]))
    }
}
