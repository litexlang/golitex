//! Native entry definitions, scalar verification, then complete-domain extensionality.
use super::matrix_entry_normalization_proof::*;
use super::result::equal_fact_result_from_success;
use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
use crate::execute::execute_fact_stmt::native_matrix::matrix_head_object;
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    ProveAndStoreThenFactResult, VerifyForallFactProof, VerifyForallFactResult,
    VerifyForallFactSuccess,
};
use crate::prelude::*;

pub(crate) const MATRIX_ENTRY_NODE_LIMIT: usize = 256;
const MATRIX_ENTRY_DEPTH_LIMIT: usize = 32;

impl Runtime {
    pub(in crate::execute) fn search_matrix_structural_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixStructuralEqualityProof>> {
        if !structural_matrix(&fact.left) && !structural_matrix(&fact.right) {
            return Ok(None);
        }
        // The entry expansion is deliberately not a general function search.
        for right_domain in self
            .complete_function_domains(&fact.right, state)?
            .into_iter()
            .take(8)
        {
            if !right_domain.signature.dom_facts.is_empty()
                || right_domain.signature.set_bound_parameters.groups.len() != 2
                || right_domain
                    .signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .any(|g| g.params.len() != 1)
            {
                continue;
            }
            let Ok(domain_match) =
                self.verify_complete_function_domain(&fact.left, &right_domain.signature, state)?
            else {
                continue;
            };
            // No inclusion facts or new domain assumptions are manufactured.
            if !matches!(
                domain_match.comparison,
                FunctionDomainComparisonProof::AlphaEquivalent
            ) {
                continue;
            }
            let Some(Fact::ForallFact(pointwise)) =
                crate::execute::execute_by_stmt::build_pointwise_forall(
                    self,
                    &fact.left,
                    &fact.right,
                    &domain_match.source.signature,
                )?
            else {
                continue;
            };
            let (outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
                let Ok(introduced_params) =
                    rt.introduce_typed_parameters(&pointwise.typed_parameters, state)?
                else {
                    return Ok(None);
                };
                let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(entry))] =
                    pointwise.then_facts.as_slice()
                else {
                    return Ok(None);
                };
                let VerifyEqualFactWellDefinedResult::Success(wd) =
                    rt.verify_equal_fact_well_definedness(entry, state)?
                else {
                    return Ok(None);
                };
                let mut remaining = MATRIX_ENTRY_NODE_LIMIT;
                let Some(left) =
                    rt.normalize_matrix_entry(&entry.left, state, 0, &mut remaining)?
                else {
                    return Ok(None);
                };
                let Some(right) =
                    rt.normalize_matrix_entry(&entry.right, state, 0, &mut remaining)?
                else {
                    return Ok(None);
                };
                let scalar: Fact = EqualFact {
                    fact_id: rt.global_ids.allocate_fact_id(),
                    left: left.value.clone(),
                    right: right.value.clone(),
                    line_file: entry.line_file.clone(),
                }
                .into();
                // Inherit the strategy's BuiltinRule ceiling and rewrite bit.
                // Normalization never invokes an independent truth search.
                let scalar_equality = rt.verify_fact(&scalar, state)?;
                if scalar_equality.is_failed() {
                    return Ok(None);
                }
                let verify_result = equal_fact_result_from_success(
                    entry,
                    wd,
                    EqualFactSearchedProof::ByBuiltinStrategy(
                        EqualitySearchProofByBuiltinStrategy::MatrixEntryReduction(
                            MatrixEntryReductionProof {
                                left,
                                right,
                                scalar_equality,
                            },
                        ),
                    ),
                );
                let store_and_infer = rt.store_fact_and_infer(&Fact::from(entry.clone()), state)?;
                Ok(Some((
                    introduced_params,
                    ProveAndStoreThenFactResult {
                        verify_result,
                        store_and_infer,
                    },
                )))
            })?;
            let Some((introduced_params, then)) = outcome else {
                continue;
            };
            let pointwise =
                VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Success(
                    VerifyForallFactProof::ByLocalIntroduction(VerifyForallFactSuccess {
                        fact: pointwise,
                        introduced_params,
                        assumed_dom_facts: vec![],
                        proved_then_facts: vec![then],
                        local_env,
                    }),
                )));
            return Ok(Some(MatrixStructuralEqualityProof {
                right_domain,
                domain_match,
                pointwise,
            }));
        }
        Ok(None)
    }

    fn normalize_matrix_entry(
        &mut self,
        source: &Obj,
        state: VerifyState,
        depth: usize,
        remaining: &mut usize,
    ) -> RuntimeResult<Option<MatrixEntryNormalizationProof>> {
        if depth >= MATRIX_ENTRY_DEPTH_LIMIT || *remaining == 0 {
            return Ok(None);
        }
        *remaining -= 1;
        let VerifyObjWellDefinedResult::Success(source_wd) =
            self.verify_obj_well_definedness(source, state)?
        else {
            return Ok(None);
        };
        let (value, step) = match source {
            Obj::FnObj(call) if structural_matrix(&matrix_head_object(&call.head)) => {
                let head = matrix_head_object(&call.head);
                let Some(callable) = self
                    .parent_checked_matrix_callables(&head, state)?
                    .into_iter()
                    .next()
                else {
                    return Ok(None);
                };
                let Some(body) = self.matrix_component_body(call, &callable) else {
                    return Ok(None);
                };
                let Some(continuation) =
                    self.normalize_matrix_entry(&body, state, depth + 1, remaining)?
                else {
                    return Ok(None);
                };
                (
                    continuation.value.clone(),
                    MatrixEntryNormalizationStep::NativeCall(MatrixEntryNativeCallProof {
                        callable: Box::new(callable),
                        body,
                        continuation: Box::new(continuation),
                    }),
                )
            }
            Obj::ArithmeticOperator(op)
                if matches!(
                    op,
                    ArithmeticOperator::Add(_)
                        | ArithmeticOperator::Sub(_)
                        | ArithmeticOperator::Mul(_)
                ) =>
            {
                let (a, b) = match op {
                    ArithmeticOperator::Add(p) => (&p.left, &p.right),
                    ArithmeticOperator::Sub(p) => (&p.left, &p.right),
                    ArithmeticOperator::Mul(p) => (&p.left, &p.right),
                    _ => unreachable!(),
                };
                let Some(a) = self.normalize_matrix_entry(a, state, depth + 1, remaining)? else {
                    return Ok(None);
                };
                let Some(b) = self.normalize_matrix_entry(b, state, depth + 1, remaining)? else {
                    return Ok(None);
                };
                let left = Box::new(a.value.clone());
                let right = Box::new(b.value.clone());
                let (op, step) = match op {
                    ArithmeticOperator::Add(_) => (
                        ArithmeticOperator::Add(Add { left, right }),
                        MatrixEntryNormalizationStep::Add(Box::new(a), Box::new(b)),
                    ),
                    ArithmeticOperator::Sub(_) => (
                        ArithmeticOperator::Sub(Sub { left, right }),
                        MatrixEntryNormalizationStep::Subtract(Box::new(a), Box::new(b)),
                    ),
                    ArithmeticOperator::Mul(_) => (
                        ArithmeticOperator::Mul(Mul { left, right }),
                        MatrixEntryNormalizationStep::Multiply(Box::new(a), Box::new(b)),
                    ),
                    _ => unreachable!(),
                };
                (Obj::ArithmeticOperator(op), step)
            }
            Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => {
                let Some(inner) =
                    self.normalize_matrix_entry(&p.arg, state, depth + 1, remaining)?
                else {
                    return Ok(None);
                };
                (
                    Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate {
                        arg: Box::new(inner.value.clone()),
                    })),
                    MatrixEntryNormalizationStep::Conjugate(Box::new(inner)),
                )
            }
            _ => (source.clone(), MatrixEntryNormalizationStep::Unchanged),
        };
        Ok(Some(MatrixEntryNormalizationProof {
            source_wd,
            value,
            step,
        }))
    }
}

fn structural_matrix(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::MatrixOperator(
            MatrixOperator::Add(_)
                | MatrixOperator::Subtract(_)
                | MatrixOperator::Scale(_)
                | MatrixOperator::Transpose(_)
                | MatrixOperator::ConjugateTranspose(_)
                | MatrixOperator::ZeroMatrix(_)
        )
    )
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/native_matrix/structural.rs"]
mod tests;
