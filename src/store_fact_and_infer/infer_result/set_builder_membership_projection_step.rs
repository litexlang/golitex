use super::InferSetBuilderProjectionResult;
use crate::runtime::FactId;

pub struct SetBuilderMembershipProjectionStep {
    pub source_membership: crate::ast::fact::InFact,
    pub builder: crate::ast::obj::SetBuilder,
    pub equality_path: Vec<(crate::ast::obj::Obj, crate::ast::obj::Obj, FactId)>,
    pub template_expansion: bool,
    pub projections: Vec<InferSetBuilderProjectionResult>,
}

impl SetBuilderMembershipProjectionStep {
    pub fn stored_conclusions(
        &self,
    ) -> impl Iterator<Item = &crate::store_fact_and_infer::StoreInferredFactResult> {
        self.projections.iter().flat_map(|p| {
            std::iter::once(p.stored()).chain(
                if let InferSetBuilderProjectionResult::BaseMembership(base) = p {
                    base.inferences
                        .iter()
                        .flat_map(|r| r.stored_conclusions())
                        .collect()
                } else {
                    Vec::new()
                },
            )
        })
    }
}
