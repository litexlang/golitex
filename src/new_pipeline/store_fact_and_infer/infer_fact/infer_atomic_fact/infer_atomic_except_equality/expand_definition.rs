use crate::new_pipeline::ast::fact::NormalAtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::helper::flatten_def_prop_params;
use crate::new_pipeline::store_fact_and_infer::{
    InferExpandDefinitionResult, InferNormalAtomicFactResult,
};

impl Runtime {
    // When: stored `$P(args)` and `P` is a concrete prop with iff facts.
    // Infers: each instantiated iff fact (one layer), stored via store_inferred.
    // Example: `prop same(x set, y set): x = y` and `$same(a, b)` → store `a = b`.
    pub(super) fn infer_normal_atomic_fact(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<InferNormalAtomicFactResult> {
        let name = normal.predicate.local_name();
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Ok(InferNormalAtomicFactResult::NoInfer);
        }
        let Some(definition) = self.def_prop_visible_in_stack(name) else {
            return Ok(InferNormalAtomicFactResult::NoInfer);
        };
        if definition.iff_facts.is_empty() {
            return Ok(InferNormalAtomicFactResult::NoInfer);
        }
        let definition = definition.clone();
        let flat = flatten_def_prop_params(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(InferNormalAtomicFactResult::NoInfer);
        }
        let mut subst = std::collections::HashMap::new();
        for (param, arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
        }
        let mut derived = Vec::new();
        for iff_fact in &definition.iff_facts {
            let Ok(instantiated) = self.inst_fact(iff_fact, &subst) else {
                continue;
            };
            derived.push(self.store_inferred_fact_and_infer(&instantiated)?);
        }
        if derived.is_empty() {
            return Ok(InferNormalAtomicFactResult::NoInfer);
        }
        Ok(InferNormalAtomicFactResult::ExpandDefinition(
            InferExpandDefinitionResult { derived },
        ))
    }
}
