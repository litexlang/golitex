//! A bijection permutes a finite product without changing its factors.
use super::helper::finite_pullback_map;
use crate::ast::fact::{BijectiveFact, EqualFact, Fact};
use crate::ast::obj::{IteratedOperator, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FiniteSetProductReindexProof {
    pub bijection: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_finite_set_product_reindex(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetProductReindexProof>> {
        // bijective(Y,X,g) => product(X,f)=product(Y,fn(y Y)R {f(g(y))}).
        // Enclosing aggregate WD checks both finite domains and numeric callbacks.
        for (source, pullback) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let (
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(source)),
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(pullback)),
            ) = (source, pullback)
            else {
                continue;
            };
            let Some(map) = finite_pullback_map(&pullback.func, &pullback.set, &source.func) else {
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
                return Ok(Some(FiniteSetProductReindexProof { bijection }));
            }
        }
        Ok(None)
    }
}
