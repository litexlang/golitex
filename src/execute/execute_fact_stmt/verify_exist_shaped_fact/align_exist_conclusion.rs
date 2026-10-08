//! Alpha-align local existential binders before matching free forall arguments.

use crate::ast::fact::ExistShapedFact;
use crate::ast::obj::{IdentifierObj, Obj};
use crate::runtime::Runtime;
use std::collections::HashMap;

impl Runtime {
    pub(super) fn align_exist_conclusion(
        &mut self,
        source: &ExistShapedFact,
        goal: &ExistShapedFact,
    ) -> Option<ExistShapedFact> {
        let source_binders: Vec<_> = source
            .plain()
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        let goal_binders: Vec<_> = goal
            .plain()
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        if source_binders.len() != goal_binders.len() {
            return None;
        }
        let mut substitution = HashMap::new();
        for (source, goal) in source_binders.iter().zip(&goal_binders) {
            substitution.insert(
                source.id,
                Obj::Identifier(IdentifierObj::from_bound_name(goal)),
            );
        }
        let mut aligned = source.plain().clone();
        let mut index = 0;
        for group in &mut aligned.typed_parameters.groups {
            group.param_type = self
                .inst_param_type(&group.param_type, &substitution)
                .ok()?;
            for binder in &mut group.params {
                *binder = goal_binders[index].clone();
                index += 1;
            }
        }
        aligned.facts = source
            .plain()
            .facts
            .iter()
            .map(|f| self.inst_quantifier_free_fact(f, &substitution))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        Some(match source {
            ExistShapedFact::Exist(_) => ExistShapedFact::Exist(aligned),
            ExistShapedFact::ExistUnique(_) => ExistShapedFact::ExistUnique(aligned),
            ExistShapedFact::NotExist(_) => ExistShapedFact::NotExist(aligned),
        })
    }
}
