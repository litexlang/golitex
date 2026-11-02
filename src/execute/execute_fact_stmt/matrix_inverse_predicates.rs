//! Complex square-matrix inverse relations. Definitions never require a selected inverse.
use super::native_matrix::{matrix_number, matrix_space};
use crate::prelude::*;

pub struct BuiltinIsMatrixInvDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct BuiltinMatrixInversibleDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct MatrixInversibleFromDeterminantProof {
    pub determinant_nonzero: Box<VerifyFactResult>,
}
pub struct IsMatrixInvSelectedProof {
    pub determinant_nonzero: Box<VerifyFactResult>,
}
pub struct NotMatrixInversibleFromDeterminantProof {
    pub determinant_zero: Box<VerifyFactResult>,
}

impl Runtime {
    // The selected inverse is a candidate on its proved domain. This fixed
    // constructor rule reuses the determinant evidence, without unfolding an
    // already-checked real matrix into a complex function a second time.
    pub(crate) fn prove_selected_matrix_inverse(
        &mut self,
        f: &IsMatrixInvFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<IsMatrixInvSelectedProof>> {
        let Obj::MatrixOperator(MatrixOperator::Inverse(inverse)) = &f.inverse else {
            return Ok(None);
        };
        if inverse.matrix.ir() != f.matrix.ir() || inverse.order.ir() != f.order.ir() {
            return Ok(None);
        }
        let requirement = self.matrix_inverse_nonzero(&f.matrix, &f.order);
        let proof = self.verify_fact(&requirement, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(IsMatrixInvSelectedProof {
            determinant_nonzero: Box::new(proof),
        }))
    }
    pub(crate) fn matrix_inverse_predicate_domain(
        &mut self,
        fact: &AtomicFact,
    ) -> Option<Vec<Fact>> {
        let (matrix, inverse, order) = match fact {
            AtomicFact::IsMatrixInvFact(f) => (&f.matrix, Some(&f.inverse), &f.order),
            AtomicFact::NotIsMatrixInvFact(f) => (&f.matrix, Some(&f.inverse), &f.order),
            AtomicFact::MatrixInversibleFact(f) => (&f.matrix, None, &f.order),
            AtomicFact::NotMatrixInversibleFact(f) => (&f.matrix, None, &f.order),
            _ => return None,
        };
        let mut requirements = vec![
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: order.clone(),
                set: Obj::StandardSet(StandardSet::N),
                line_file: None,
            }
            .into(),
            self.native_matrix_membership(matrix, StandardSet::C, order, order)
                .into(),
        ];
        if let Some(inverse) = inverse {
            requirements.push(
                self.native_matrix_membership(inverse, StandardSet::C, order, order)
                    .into(),
            );
        }
        Some(requirements)
    }

    pub(crate) fn matrix_inverse_candidate_clauses(&mut self, f: &IsMatrixInvFact) -> Vec<Fact> {
        let mut clauses = Vec::new();
        for (left, right) in [(&f.matrix, &f.inverse), (&f.inverse, &f.matrix)] {
            clauses.push(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: Obj::MatrixOperator(MatrixOperator::Multiply(MatrixMultiply {
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                        rows: Box::new(f.order.clone()),
                        inner: Box::new(f.order.clone()),
                        cols: Box::new(f.order.clone()),
                    })),
                    right: Obj::MatrixOperator(MatrixOperator::IdentityMatrix(IdentityMatrix {
                        order: Box::new(f.order.clone()),
                    })),
                    line_file: None,
                }
                .into(),
            );
        }
        clauses
    }

    pub(crate) fn matrix_inverse_existence(&mut self, matrix: &Obj, order: &Obj) -> Fact {
        let binding = self.fresh_internal_param();
        let inverse = Obj::Identifier(IdentifierObj::from_bound_name(&binding));
        let candidate = IsMatrixInvFact {
            fact_id: self.global_ids.allocate_fact_id(),
            matrix: matrix.clone(),
            inverse,
            order: order.clone(),
            line_file: None,
        };
        Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binding],
                    param_type: ParamType::Obj(matrix_space(
                        Obj::StandardSet(StandardSet::C),
                        order.clone(),
                        order.clone(),
                    )),
                }],
            },
            facts: vec![QuantifierFreeFact::AtomicFact(candidate.into())],
            line_file: None,
        })
    }

    pub(crate) fn matrix_inverse_nonzero(&mut self, matrix: &Obj, order: &Obj) -> Fact {
        NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::MatrixOperator(MatrixOperator::Determinant(Determinant {
                matrix: Box::new(matrix.clone()),
                order: Box::new(order.clone()),
            })),
            right: matrix_number(0),
            line_file: None,
        }
        .into()
    }

    // det(A) != 0 implies existence of a two-sided inverse over C.
    // The premise uses the caller's already-decreased state; this rule cannot
    // recursively prove itself through its own determinant bridge.
    pub(crate) fn prove_matrix_inversible_from_determinant(
        &mut self,
        f: &MatrixInversibleFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixInversibleFromDeterminantProof>> {
        let requirement = self.matrix_inverse_nonzero(&f.matrix, &f.order);
        let proof = self.verify_fact(&requirement, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(MatrixInversibleFromDeterminantProof {
            determinant_nonzero: Box::new(proof),
        }))
    }

    // det(A) = 0 excludes a two-sided inverse (including exact scalar evidence).
    pub(crate) fn prove_matrix_not_inversible_from_determinant(
        &mut self,
        f: &NotMatrixInversibleFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<NotMatrixInversibleFromDeterminantProof>> {
        let nonzero = self.matrix_inverse_nonzero(&f.matrix, &f.order);
        let Fact::AtomicFact(nonzero) = nonzero else {
            unreachable!()
        };
        let requirement = negate_atomic_fact(&nonzero, self.global_ids.allocate_fact_id())
            .expect("nonzero has a negation");
        let proof = self.verify_fact(&Fact::AtomicFact(requirement), state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NotMatrixInversibleFromDeterminantProof {
            determinant_zero: Box::new(proof),
        }))
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/native_matrix/inverse_predicates.rs"]
mod tests;
