//! Reindex a commutative associative finite fold using a checked bijection.
use super::helper::finite_pullback_map;
use super::reduce_rule_helper::ReduceObjectMatchProof;
use crate::ast::fact::{BijectiveFact, EqualFact, Fact};
use crate::ast::obj::{IteratedOperator, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FiniteSetReduceReindexProof {
    pub operator_match: ReduceObjectMatchProof,
    pub seed_match: ReduceObjectMatchProof,
    pub bijection: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_finite_set_reduce_reindex(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetReduceReindexProof>> {
        // With AC(op) and bijective(Y,X,g), fold(X,f,op,s)=fold(Y,f o g,op,s).
        // Enclosing unordered-fold WD retains AC, carrier and callback certificates.
        for (source, pullback) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let (
                Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(source)),
                Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(pullback)),
            ) = (source, pullback)
            else {
                continue;
            };
            // Only the total homogeneous signature triggers both laws in fold WD.
            let Some(signature) = self.resolve_callable_fn_set(&source.op) else {
                continue;
            };
            if !signature.dom_facts.is_empty()
                || signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
                    != 2
                || signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .any(|g| !g.params.is_empty() && g.param_type.ir() != signature.ret_set.ir())
            {
                continue;
            }
            let Some(map) = finite_pullback_map(&pullback.func, &pullback.set, &source.func) else {
                continue;
            };
            let Some(operator_match) = self.match_reduce_object(&source.op, &pullback.op) else {
                continue;
            };
            let Some(seed_match) = self.match_reduce_object(&source.seed, &pullback.seed) else {
                continue;
            };
            let premise: Fact = BijectiveFact {
                fact_id: self.global_ids.allocate_fact_id(),
                domain: pullback.set.as_ref().clone(),
                codomain: source.set.as_ref().clone(),
                function: map,
                line_file: fact.line_file.clone(),
            }
            .into();
            let bijection = self.verify_builtin_rule_premise(&premise, state)?;
            if !bijection.is_failed() {
                return Ok(Some(FiniteSetReduceReindexProof {
                    operator_match,
                    seed_match,
                    bijection,
                }));
            }
        }
        Ok(None)
    }
}
