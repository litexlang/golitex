use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(in crate::inference) fn infer_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let Some(exist_fact) = self.build_not_forall_counterexample_exist_fact(not_forall)? else {
            return Ok(SuccessInferResult::new());
        };

        let inferred_fact: Fact = exist_fact.into();
        let mut out = SuccessInferResult::new();
        out.new_fact(&inferred_fact);
        out.new_infer_result_inside(
            self.store_fact_without_forall_coverage_check_and_infer_with_state(
                inferred_fact,
                inference_state,
            )?,
        );
        Ok(out)
    }

    fn build_not_forall_counterexample_exist_fact(
        &self,
        not_forall: &NotForallFact,
    ) -> Result<Option<ExistFactEnum>, RuntimeError> {
        let forall = &not_forall.forall_fact;
        if forall.typed_parameters.number_of_params() == 0 || forall.then_facts.is_empty() {
            return Ok(None);
        }

        let source_bindings = forall.typed_parameters.collect_param_bindings();
        let (exist_names, full_param_to_exist_obj) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings);
        let mut param_to_exist_obj: HashMap<String, Obj> = HashMap::new();
        let mut exist_groups: Vec<TypedParameterGroup> = Vec::new();
        let mut name_index = 0;
        for group in forall.typed_parameters.groups.iter() {
            let param_type = self.inst_param_type(
                &group.param_type,
                &param_to_exist_obj,
                SubstitutionMode::Exact,
            )?;
            let group_exist_names =
                exist_names[name_index..name_index + group.params.len()].to_vec();
            for binding in group.params.iter() {
                let name = binding.name();
                insert_symbol_substitution(
                    &mut param_to_exist_obj,
                    binding,
                    full_param_to_exist_obj[name].clone(),
                );
            }
            name_index += group.params.len();
            exist_groups.push(TypedParameterGroup::new(group_exist_names, param_type));
        }

        let mut body_facts: Vec<QuantifierFreeFact> = Vec::new();
        for dom_fact in forall.dom_facts.iter() {
            let Some(dom_body_fact) =
                self.fact_to_quantifier_free_fact(dom_fact, &param_to_exist_obj)?
            else {
                return Ok(None);
            };
            body_facts.push(dom_body_fact.into());
        }

        let mut negated_then_branches: Vec<AndChainAtomicFact> = Vec::new();
        for then_fact in forall.then_facts.iter() {
            let Some(then_body_fact) =
                self.then_fact_to_quantifier_free_fact(then_fact, &param_to_exist_obj)?
            else {
                return Ok(None);
            };
            let Ok(mut branches) = Self::demorgan_negate_exist_body_conjunct(&then_body_fact)
            else {
                return Ok(None);
            };
            negated_then_branches.append(&mut branches);
        }
        if negated_then_branches.is_empty() {
            return Ok(None);
        }

        body_facts.push(if negated_then_branches.len() == 1 {
            and_chain_atomic_to_or_and_chain_atomic(negated_then_branches.remove(0)).into()
        } else {
            QuantifierFreeFact::OrFact(OrFact::new(negated_then_branches, forall.line_file.clone()))
                .into()
        });

        Ok(Some(ExistFactEnum::ExistFact(ExistentialSpec::new(
            TypedParameterList::new(exist_groups),
            body_facts,
            forall.line_file.clone(),
        )?)))
    }

    fn fact_to_quantifier_free_fact(
        &self,
        fact: &Fact,
        param_to_exist_obj: &HashMap<String, Obj>,
    ) -> Result<Option<QuantifierFreeFact>, RuntimeError> {
        let instantiated =
            self.inst_fact(fact, param_to_exist_obj, SubstitutionMode::Exact, None)?;
        Ok(match instantiated {
            Fact::AtomicFact(f) => Some(QuantifierFreeFact::AtomicFact(f)),
            Fact::AndFact(f) => Some(QuantifierFreeFact::AndFact(f)),
            Fact::ChainFact(f) => Some(QuantifierFreeFact::ChainFact(f)),
            Fact::OrFact(f) => Some(QuantifierFreeFact::OrFact(f)),
            Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => None,
        })
    }

    fn then_fact_to_quantifier_free_fact(
        &self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_exist_obj: &HashMap<String, Obj>,
    ) -> Result<Option<QuantifierFreeFact>, RuntimeError> {
        let instantiated = self.inst_exist_or_and_chain_atomic_fact(
            fact,
            param_to_exist_obj,
            SubstitutionMode::Exact,
            None,
        )?;
        Ok(match instantiated {
            ExistOrAndChainAtomicFact::AtomicFact(f) => Some(QuantifierFreeFact::AtomicFact(f)),
            ExistOrAndChainAtomicFact::AndFact(f) => Some(QuantifierFreeFact::AndFact(f)),
            ExistOrAndChainAtomicFact::ChainFact(f) => Some(QuantifierFreeFact::ChainFact(f)),
            ExistOrAndChainAtomicFact::OrFact(f) => Some(QuantifierFreeFact::OrFact(f)),
            ExistOrAndChainAtomicFact::ExistFact(_) => None,
        })
    }
}

fn and_chain_atomic_to_or_and_chain_atomic(fact: AndChainAtomicFact) -> QuantifierFreeFact {
    match fact {
        AndChainAtomicFact::AtomicFact(f) => QuantifierFreeFact::AtomicFact(f),
        AndChainAtomicFact::AndFact(f) => QuantifierFreeFact::AndFact(f),
        AndChainAtomicFact::ChainFact(f) => QuantifierFreeFact::ChainFact(f),
    }
}
