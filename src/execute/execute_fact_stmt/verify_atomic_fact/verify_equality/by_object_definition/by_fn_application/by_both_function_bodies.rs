//! Equality of two applications by checked, bounded body substitution.
//! Each application retains its own argument/guard evidence. Returned
//! functions are applied one layer at a time by the existing normalizer.

use super::normalize_function_body::FunctionBodyNormalizationProof;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct ByBothFunctionBodiesObjectDefinitionProof {
    pub left_normalization: FunctionBodyNormalizationProof,
    pub right_normalization: FunctionBodyNormalizationProof,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_both_function_bodies(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ByBothFunctionBodiesObjectDefinitionProof>> {
        if !matches!((&fact.left, &fact.right), (Obj::FnObj(_), Obj::FnObj(_))) {
            return Ok(None);
        }
        let Some(left_normalization) =
            self.normalize_function_body(&fact.left, &fact.right, state)?
        else {
            return Ok(None);
        };
        let Some(right_normalization) =
            self.normalize_function_body(&fact.right, &fact.left, state)?
        else {
            return Ok(None);
        };
        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_normalization.expanded_body.clone(),
            right: right_normalization.expanded_body.clone(),
            line_file: fact.line_file.clone(),
        };
        // The definition dispatcher already reduced the truth ceiling. Do
        // not reopen definition search while checking the resulting bodies.
        let residual_equal = self.verify_equal_fact(&residual, state.without_rewrite())?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ByBothFunctionBodiesObjectDefinitionProof {
            left_normalization,
            right_normalization,
            residual_equal,
        }))
    }
}
