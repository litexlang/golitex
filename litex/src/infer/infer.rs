use crate::error::InferError;
use crate::execute::Executor;
use crate::fact::{
    AndFact, AtomicFact, ChainFact, EqualFact, ExistFact, Fact, ForallFact,
    ForallFactWithIff, InFact, NormalAtomicFact, OrFact,
};
use crate::obj::{FnSetObj, Obj};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;

impl<'a> Executor<'a> {
    pub fn infer(&mut self, fact: &Fact) -> Result<(), InferError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.infer_forall_fact(forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self.infer_forall_fact_with_iff(forall_fact_with_iff),
        }
    }

    fn infer_atomic_fact(&mut self, _atomic_fact: &AtomicFact) -> Result<(), InferError> {
        match _atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => self.infer_normal_atomic_fact(normal_atomic_fact),
            _ => Ok(()),
        }
    }

    fn infer_exist_fact(&mut self, _exist_fact: &ExistFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_and_fact(&mut self, _and_fact: &AndFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_chain_fact(&mut self, _chain_fact: &ChainFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_forall_fact(&mut self, _forall_fact: &ForallFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_forall_fact_with_iff(
        &mut self,
        _forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_equal_fact(&mut self, _equal_fact: &EqualFact) -> Result<(), InferError> {
        Ok(())
    }

    fn infer_in_fact(&mut self, in_fact: &InFact) -> Result<(), InferError> {
        match &in_fact.set {
            Obj::FnSetWithDom(fn_set_with_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithDom(fn_set_with_dom.clone());

                let env = self.runtime_context.top_level_env();
                env.known_fn_in_fn_set.insert(key, fn_set_obj);

                Ok(())
            }
            Obj::FnSetWithoutDom(fn_set_without_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithoutDom(fn_set_without_dom.clone());

                self.runtime_context.top_level_env().known_fn_in_fn_set.insert(key, fn_set_obj);

                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn infer_normal_atomic_fact(&mut self, normal_atomic_fact: &NormalAtomicFact) -> Result<(), InferError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let predicate_definition = match self.runtime_context.get_predicate_definition_by_name(&predicate_name) {
            Some(predicate_definition) => predicate_definition.clone(),
            None => unreachable!(),
        };

        let param_type_facts =
            ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &predicate_definition.params_def_with_type,
                &normal_atomic_fact.body,
            )
            .map_err(|previous_error| {
                InferError::new(
                    format!("failed to infer parameter type facts for `{}`", normal_atomic_fact),
                    normal_atomic_fact.line_file_index,
                    Some(previous_error),
                )
            })?;

        for param_type_fact in param_type_facts.iter() {
            self.store_fact_without_well_defined_verified_and_infer(param_type_fact)
                .map_err(|previous_error| {
                    InferError::new(
                        format!("failed to store parameter type fact while inferring `{}`", normal_atomic_fact),
                        normal_atomic_fact.line_file_index,
                        Some(previous_error.into()),
                    )
                })?;
        }

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        );

        for iff_fact in predicate_definition.iff_facts.iter() {
            let instantiated_iff_fact = iff_fact.instantiate(&param_to_arg_map);

            self.store_fact_without_well_defined_verified_and_infer(&instantiated_iff_fact)
                .map_err(|previous_error| {
                    InferError::new(
                        format!("failed to store instantiated iff fact while inferring `{}`", normal_atomic_fact),
                        normal_atomic_fact.line_file_index,
                        Some(previous_error.into()),
                    )
                })?;
        }

        Ok(())
    }
}