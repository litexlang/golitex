use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn infer_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
    ) -> Result<InferResult, RuntimeError> {
        let Some(exist_fact) = self.build_not_forall_counterexample_exist_fact(not_forall)? else {
            return Ok(InferResult::new());
        };

        let inferred_fact: Fact = exist_fact.into();
        let mut out = InferResult::new();
        out.new_fact(&inferred_fact);
        out.new_infer_result_inside(
            self.store_fact_without_forall_coverage_check_and_infer(inferred_fact)?,
        );
        Ok(out)
    }

    fn build_not_forall_counterexample_exist_fact(
        &self,
        not_forall: &NotForallFact,
    ) -> Result<Option<ExistFactEnum>, RuntimeError> {
        let forall = &not_forall.forall_fact;
        if forall.params_def_with_type.number_of_params() == 0 || forall.then_facts.is_empty() {
            return Ok(None);
        }

        let mut param_to_exist_obj: HashMap<String, Obj> = HashMap::new();
        let mut exist_groups: Vec<ParamGroupWithParamType> = Vec::new();
        for group in forall.params_def_with_type.groups.iter() {
            for name in group.params.iter() {
                param_to_exist_obj.insert(
                    name.clone(),
                    obj_for_bound_param_in_scope(name.clone(), ParamObjType::Exist),
                );
            }
            let param_type =
                self.inst_param_type(&group.param_type, &param_to_exist_obj, ParamObjType::Forall)?;
            exist_groups.push(ParamGroupWithParamType::new(
                group.params.clone(),
                param_type,
            ));
        }

        let mut body_facts: Vec<OrAndChainAtomicFact> = Vec::new();
        for dom_fact in forall.dom_facts.iter() {
            let Some(dom_body_fact) =
                self.fact_to_exist_body_fact(dom_fact, &param_to_exist_obj)?
            else {
                return Ok(None);
            };
            body_facts.push(dom_body_fact);
        }

        let mut negated_then_branches: Vec<AndChainAtomicFact> = Vec::new();
        for then_fact in forall.then_facts.iter() {
            let Some(then_body_fact) =
                self.then_fact_to_exist_body_fact(then_fact, &param_to_exist_obj)?
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
            and_chain_atomic_to_or_and_chain_atomic(negated_then_branches.remove(0))
        } else {
            OrAndChainAtomicFact::OrFact(OrFact::new(
                negated_then_branches,
                forall.line_file.clone(),
            ))
        });

        Ok(Some(ExistFactEnum::ExistFact(ExistFactBody::new(
            ParamDefWithType::new(exist_groups),
            body_facts,
            forall.line_file.clone(),
        ))))
    }

    fn fact_to_exist_body_fact(
        &self,
        fact: &Fact,
        param_to_exist_obj: &HashMap<String, Obj>,
    ) -> Result<Option<OrAndChainAtomicFact>, RuntimeError> {
        let instantiated = self.inst_fact(fact, param_to_exist_obj, ParamObjType::Forall, None)?;
        Ok(match instantiated {
            Fact::AtomicFact(f) => Some(OrAndChainAtomicFact::AtomicFact(f)),
            Fact::AndFact(f) => Some(OrAndChainAtomicFact::AndFact(f)),
            Fact::ChainFact(f) => Some(OrAndChainAtomicFact::ChainFact(f)),
            Fact::OrFact(f) => Some(OrAndChainAtomicFact::OrFact(f)),
            Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => None,
        })
    }

    fn then_fact_to_exist_body_fact(
        &self,
        fact: &ExistOrAndChainAtomicFact,
        param_to_exist_obj: &HashMap<String, Obj>,
    ) -> Result<Option<OrAndChainAtomicFact>, RuntimeError> {
        let instantiated = self.inst_exist_or_and_chain_atomic_fact(
            fact,
            param_to_exist_obj,
            ParamObjType::Forall,
            None,
        )?;
        Ok(match instantiated {
            ExistOrAndChainAtomicFact::AtomicFact(f) => Some(OrAndChainAtomicFact::AtomicFact(f)),
            ExistOrAndChainAtomicFact::AndFact(f) => Some(OrAndChainAtomicFact::AndFact(f)),
            ExistOrAndChainAtomicFact::ChainFact(f) => Some(OrAndChainAtomicFact::ChainFact(f)),
            ExistOrAndChainAtomicFact::OrFact(f) => Some(OrAndChainAtomicFact::OrFact(f)),
            ExistOrAndChainAtomicFact::ExistFact(_) => None,
        })
    }
}

fn and_chain_atomic_to_or_and_chain_atomic(fact: AndChainAtomicFact) -> OrAndChainAtomicFact {
    match fact {
        AndChainAtomicFact::AtomicFact(f) => OrAndChainAtomicFact::AtomicFact(f),
        AndChainAtomicFact::AndFact(f) => OrAndChainAtomicFact::AndFact(f),
        AndChainAtomicFact::ChainFact(f) => OrAndChainAtomicFact::ChainFact(f),
    }
}
