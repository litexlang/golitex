//! Declaration-owned conversion of a checked membership carrier.
//! No equality-index traversal, proof search, storage, or permission reset.
use crate::ast::fact::InFact;
use crate::ast::obj::Obj;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashSet;

impl Runtime {
    /// The caller has established formation of the source membership, including
    /// the instance arguments and guards. Each step substitutes one checked
    /// HaveObjEqual definition. Only outer template constructors are expanded;
    /// an ordinary identifier stops conversion. Definitions are nonrecursive;
    /// the visited set additionally rejects a repeated instantiated carrier.
    pub(crate) fn expand_template_membership(
        &mut self,
        source: &InFact,
    ) -> RuntimeResult<Vec<InFact>> {
        if !matches!(&source.set, Obj::InstantiatedTemplateObj(_)) {
            return Ok(Vec::new());
        }
        let mut carrier = source.set.clone();
        let mut seen = HashSet::new();
        let mut steps = Vec::new();
        while let Obj::InstantiatedTemplateObj(instance) = &carrier {
            if !seen.insert(carrier.ir()) {
                return Ok(Vec::new());
            }
            let Some(rhs) = self.expanded_have_obj_equal_rhs_of_instantiated_template(instance)?
            else {
                break;
            };
            carrier = rhs;
            steps.push(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: source.element.clone(),
                set: carrier.clone(),
                line_file: source.line_file.clone(),
            });
        }
        Ok(steps)
    }
}
