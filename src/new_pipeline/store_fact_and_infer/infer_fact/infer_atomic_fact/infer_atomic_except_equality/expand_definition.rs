use crate::new_pipeline::ast::fact::{Fact, NormalAtomicFact};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::helper::flatten_def_prop_params;

impl Runtime {
    // When: stored `$P(args)` and `P` is a concrete prop with iff facts.
    // Infers: each instantiated iff fact (one layer).
    // Example: `prop same(x set, y set): x = y` and `$same(a, b)` → store `a = b`.
    pub(super) fn infer_expand_definition_stage(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<()> {
        let name = normal.predicate.local_name();
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Ok(());
        }
        let Some(definition) = self.def_prop_visible_in_stack(name) else {
            return Ok(());
        };
        if definition.iff_facts.is_empty() {
            return Ok(());
        }
        let definition = definition.clone();
        let flat = flatten_def_prop_params(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(());
        }
        let mut subst = std::collections::HashMap::new();
        for (param, arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
        }
        for iff_fact in &definition.iff_facts {
            let Ok(instantiated) = self.inst_fact(iff_fact, &subst) else {
                continue;
            };
            match instantiated {
                Fact::AtomicFact(atomic) => {
                    // Index only — avoid cyclic re-expansion through nested NormalAtomic.
                    self.store_atomic_fact(&atomic)?;
                }
                other => {
                    let _ = self.store_fact_and_infer(&other)?;
                }
            }
        }
        Ok(())
    }
}
