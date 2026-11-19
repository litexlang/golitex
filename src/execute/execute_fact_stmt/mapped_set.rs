//! Bounded image membership is the existence of an input assignment.

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    // For `z $in {a + b for a $in A, b $in B}`, build the same clause for
    // membership verification and inference: `exist a A, b B st {z = a + b}`.
    pub(crate) fn mapped_set_membership_clause(
        &mut self,
        set: &MappedSet,
        membership: &InFact,
    ) -> RuntimeResult<Fact> {
        let (typed_parameters, body) = self.fresh_mapped_set_parameters(set)?;
        let equality = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: membership.element.clone(),
            right: body,
            line_file: membership.line_file.clone(),
        };
        Ok(Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters,
            facts: vec![QuantifierFreeFact::AtomicFact(equality.into())],
            line_file: membership.line_file.clone(),
        }))
    }

    // For `{a + b for a $in A, b $in B} $subset C`, check
    // `forall a A, b B: a + b $in C` with the shared verifier.
    pub(crate) fn mapped_set_subset_clause(
        &mut self,
        set: &MappedSet,
        subset: &SubsetFact,
    ) -> RuntimeResult<Fact> {
        let (typed_parameters, body) = self.fresh_mapped_set_parameters(set)?;
        let membership = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: body,
            set: subset.right.clone(),
            line_file: subset.line_file.clone(),
        };
        Ok(Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters,
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(membership.into())],
            line_file: subset.line_file.clone(),
        }))
    }

    pub(crate) fn mapped_set_displayed_witnesses(
        &mut self,
        set: &MappedSet,
        membership: &InFact,
    ) -> RuntimeResult<Option<(Vec<Obj>, Vec<Fact>)>> {
        let parameters = set
            .parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|param| (param.id, group.param_type.as_ref()))
            })
            .collect::<Vec<_>>();
        let ids = parameters.iter().map(|(id, _)| *id).collect::<Vec<_>>();
        let Some(matched) =
            self.match_forall_conclusion_args(&[&set.body], &[&membership.element], &ids)?
        else {
            return Ok(None);
        };
        let (substitution, _, _) = matched.into_parts(self.result_detail())?;
        let mut witnesses = Vec::with_capacity(parameters.len());
        let mut requirements = Vec::with_capacity(parameters.len() + 1);
        for (id, domain) in parameters {
            let witness = substitution[&id].clone();
            requirements.push(Fact::AtomicFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: witness.clone(),
                    set: domain.clone(),
                    line_file: membership.line_file.clone(),
                }
                .into(),
            ));
            witnesses.push(witness);
        }
        let body = self
            .inst_obj(&set.body, &substitution)
            .map_err(|error| RuntimeError::InternalBug(error.to_string()))?;
        requirements.push(Fact::AtomicFact(
            EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: membership.element.clone(),
                right: body,
                line_file: membership.line_file.clone(),
            }
            .into(),
        ));
        Ok(Some((witnesses, requirements)))
    }

    fn fresh_mapped_set_parameters(
        &mut self,
        set: &MappedSet,
    ) -> RuntimeResult<(TypedParameterList, Obj)> {
        let mut substitution = HashMap::new();
        let mut groups = Vec::with_capacity(set.parameters.groups.len());
        for group in &set.parameters.groups {
            let mut params = Vec::with_capacity(group.params.len());
            for original in &group.params {
                let fresh = self.fresh_internal_param();
                substitution.insert(
                    original.id,
                    Obj::Identifier(IdentifierObj::from_bound_name(&fresh)),
                );
                params.push(fresh);
            }
            groups.push(TypedParameterGroup {
                params,
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            });
        }
        let body = self
            .inst_obj(&set.body, &substitution)
            .map_err(|error| RuntimeError::InternalBug(error.to_string()))?;
        Ok((TypedParameterList { groups }, body))
    }
}
