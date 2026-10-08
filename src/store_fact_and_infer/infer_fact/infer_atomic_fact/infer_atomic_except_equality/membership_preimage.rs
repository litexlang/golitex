//! Stored preimage membership exposes its certified input and output conditions.
use crate::ast::fact::InFact;
use crate::ast::obj::{FunctionSpace, Obj};
use crate::execute::execute_fact_stmt::function_preimage::{
    function_preimage_scope_active, FunctionPreimageScope,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactPreimageResult, InferInFactPreimageSetResult,
};

impl Runtime {
    // x in a point/set preimage supplies input carriers, guards, and output condition.
    // Example: x in preimage(reciprocal,2) supplies x != 0 and reciprocal(x)=2.
    pub(super) fn infer_in_fact_preimage(
        &mut self,
        member: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        for (root, path) in self.exact_property_object_values(&member.set) {
            if !matches!(
                &root,
                Obj::FunctionSpace(FunctionSpace::Preimage(_) | FunctionSpace::PreimageSet(_))
            ) {
                continue;
            }
            if function_preimage_scope_active(&root) {
                continue;
            }
            let _scope = FunctionPreimageScope::new(&root);
            let Ok(construction) = self.verify_function_preimage_construction(&root, state)? else {
                continue;
            };
            let base = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: member.element.clone(),
                set: construction.builder.param_set.as_ref().clone(),
                line_file: member.line_file.clone(),
            };
            let mut derived = Vec::new();
            self.store_new_set_builder_projection(&base.into(), state, &mut derived)?;
            let mut substitution = std::collections::HashMap::new();
            substitution.insert(
                construction.builder.param_binding.id,
                member.element.clone(),
            );
            for condition in &construction.builder.facts {
                let condition = self
                    .inst_quantifier_free_fact(condition, &substitution)
                    .map_err(|error| {
                        crate::runtime::RuntimeError::InternalBug(format!(
                            "preimage projection substitution: {error}"
                        ))
                    })?;
                let fact = crate::instantiate::quantifier_free_fact_to_fact(condition);
                self.store_new_set_builder_projection(&fact, state, &mut derived)?;
            }
            let source_equal = KnownEqualityPathProof::new(path);
            return Ok(Some(match root {
                Obj::FunctionSpace(FunctionSpace::Preimage(_)) => {
                    InferAtomicExceptEqualityResult::InFactPreimage(InferInFactPreimageResult {
                        source_fact_id: member.fact_id,
                        source_equal,
                        construction,
                        derived,
                    })
                }
                Obj::FunctionSpace(FunctionSpace::PreimageSet(_)) => {
                    InferAtomicExceptEqualityResult::InFactPreimageSet(
                        InferInFactPreimageSetResult {
                            source_fact_id: member.fact_id,
                            source_equal,
                            construction,
                            derived,
                        },
                    )
                }
                _ => unreachable!("only point/set preimage roots selected"),
            }));
        }
        Ok(None)
    }
}
