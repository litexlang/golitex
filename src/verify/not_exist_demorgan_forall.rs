//! From `not exist x st {F1,...,Fn}` derive `forall x: not F1 or ... or not Fn`.

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn build_not_exist_demorgan_forall_fact(
        &self,
        not_exist: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        if !not_exist.is_not_exist() {
            return Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "internal: build_not_exist_demorgan_forall_fact expects NotExistFact"
                        .to_string(),
                ),
            )));
        }
        if not_exist.params_def_with_type().number_of_params() == 0 {
            return Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "not exist: cannot derive forall (no parameters)".to_string(),
                    not_exist.line_file(),
                ),
            )));
        }

        let facts = not_exist.facts();
        if facts.is_empty() {
            return Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "not exist: cannot derive forall (empty body)".to_string(),
                    not_exist.line_file(),
                ),
            )));
        }

        let lf = not_exist.line_file();
        let source_bindings = not_exist.params_def_with_type().collect_param_bindings();
        let (forall_names, full_param_to_forall_obj) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings, ParamObjType::Forall);
        let mut param_to_forall_obj: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        let mut name_index = 0;
        for group in not_exist.params_def_with_type().groups.iter() {
            let param_type = self.inst_param_type(
                &group.param_type,
                &param_to_forall_obj,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
            )?;
            let group_forall_names =
                forall_names[name_index..name_index + group.params.len()].to_vec();
            for binding in group.params.iter() {
                let name = binding.name();
                insert_symbol_substitution(
                    &mut param_to_forall_obj,
                    binding,
                    full_param_to_forall_obj[name].clone(),
                );
            }
            name_index += group.params.len();
            forall_groups.push(ParamGroupWithParamType::new(group_forall_names, param_type));
        }

        let mut disjuncts: Vec<AndChainAtomicFact> = Vec::new();
        for conjunct in facts.iter() {
            let forall_conjunct = self.inst_quantifier_free_fact(
                conjunct,
                &param_to_forall_obj,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
                None,
            )?;
            let mut part = Self::demorgan_negate_exist_body_conjunct(&forall_conjunct)?;
            disjuncts.append(&mut part);
        }

        let then_fact = if disjuncts.len() == 1 {
            disjuncts.remove(0).into()
        } else {
            ExistOrAndChainAtomicFact::OrFact(OrFact::new(disjuncts, lf.clone()))
        };
        Ok(ForallFact::new_canonical_forall(
            ParamDefWithType::new(forall_groups),
            vec![],
            vec![then_fact],
            lf,
        )?)
    }

    pub(crate) fn demorgan_negate_exist_body_conjunct(
        conjunct: &QuantifierFreeFact,
    ) -> Result<Vec<AndChainAtomicFact>, RuntimeError> {
        let lf = conjunct.line_file();
        match conjunct {
            QuantifierFreeFact::AtomicFact(a) => Ok(vec![AndChainAtomicFact::AtomicFact(
                Self::demorgan_negate_atomic_or_err(a)?,
            )]),
            QuantifierFreeFact::AndFact(af) => {
                if af.facts.is_empty() {
                    return Err(RuntimeError::from(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "not exist: empty `and` in body".to_string(),
                            lf,
                        ),
                    )));
                }
                let mut out = Vec::with_capacity(af.facts.len());
                for a in af.facts.iter() {
                    out.push(AndChainAtomicFact::AtomicFact(
                        Self::demorgan_negate_atomic_or_err(a)?,
                    ));
                }
                Ok(out)
            }
            QuantifierFreeFact::ChainFact(cf) => {
                let atomics = cf
                    .facts()
                    .map_err(RuntimeError::wrap_new_fact_as_store_conflict)?;
                if atomics.is_empty() {
                    return Err(RuntimeError::from(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "not exist: empty chain in body".to_string(),
                            lf,
                        ),
                    )));
                }
                let mut out = Vec::with_capacity(atomics.len());
                for a in atomics.iter() {
                    out.push(AndChainAtomicFact::AtomicFact(
                        Self::demorgan_negate_atomic_or_err(a)?,
                    ));
                }
                Ok(out)
            }
            QuantifierFreeFact::OrFact(_) => Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "not exist: automatic forall derivation does not support `or` inside a body conjunct"
                        .to_string(),
                    lf,
                ),
            ))),
        }
    }

    fn demorgan_negate_atomic_or_err(a: &AtomicFact) -> Result<AtomicFact, RuntimeError> {
        a.logical_negation().map_err(|negation_error| {
            RuntimeError::from(NewFactRuntimeError(RuntimeErrorStruct::new(
                None,
                "not exist: automatic forall derivation does not support this logical negation"
                    .to_string(),
                a.line_file(),
                Some(negation_error),
                vec![],
            )))
        })
    }
}
