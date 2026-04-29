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
        let mut param_to_forall_obj: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        for group in not_exist.params_def_with_type().groups.iter() {
            for name in group.params.iter() {
                param_to_forall_obj.insert(
                    name.clone(),
                    obj_for_bound_param_in_scope(name.clone(), ParamObjType::Forall),
                );
            }
            let param_type =
                self.inst_param_type(&group.param_type, &param_to_forall_obj, ParamObjType::Exist)?;
            forall_groups.push(ParamGroupWithParamType::new(
                group.params.clone(),
                param_type,
            ));
        }

        let mut disjuncts: Vec<AndChainAtomicFact> = Vec::new();
        for conjunct in facts.iter() {
            let forall_conjunct = self.inst_exist_body_fact(
                conjunct,
                &param_to_forall_obj,
                ParamObjType::Exist,
                None,
            )?;
            let Some(forall_conjunct) = exist_body_fact_as_or_and_chain_atomic_fact(forall_conjunct)
            else {
                return Err(RuntimeError::from(NewFactRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("not exist: `{}` in body cannot be negated here", FORALL_BANG),
                        conjunct.line_file(),
                    ),
                )));
            };
            let mut part = Self::demorgan_negate_exist_body_conjunct(&forall_conjunct)?;
            disjuncts.append(&mut part);
        }

        let then_fact = if disjuncts.len() == 1 {
            disjuncts.remove(0).into()
        } else {
            ExistOrAndChainAtomicFact::OrFact(OrFact::new(disjuncts, lf.clone()))
        };
        Ok(ForallFact::new(
            ParamDefWithType::new(forall_groups),
            vec![],
            vec![then_fact],
            lf,
        )?)
    }

    pub(crate) fn demorgan_negate_exist_body_conjunct(
        conjunct: &OrAndChainAtomicFact,
    ) -> Result<Vec<AndChainAtomicFact>, RuntimeError> {
        let lf = conjunct.line_file();
        match conjunct {
            OrAndChainAtomicFact::AtomicFact(a) => Ok(vec![AndChainAtomicFact::AtomicFact(
                Self::demorgan_negate_atomic_or_err(a)?,
            )]),
            OrAndChainAtomicFact::AndFact(af) => {
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
            OrAndChainAtomicFact::ChainFact(cf) => {
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
            OrAndChainAtomicFact::OrFact(_) => Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "not exist: automatic forall derivation does not support `or` inside a body conjunct"
                        .to_string(),
                    lf,
                ),
            ))),
        }
    }

    fn demorgan_negate_atomic_or_err(a: &AtomicFact) -> Result<AtomicFact, RuntimeError> {
        match a {
            AtomicFact::FnEqualFact(_) | AtomicFact::FnEqualInFact(_) => Err(
                RuntimeError::from(NewFactRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "not exist: automatic forall derivation does not support negating $fn_eq / $fn_eq_in here"
                            .to_string(),
                        a.line_file(),
                    ),
                )),
            ),
            _ => Ok(a.make_reversed()),
        }
    }
}

fn exist_body_fact_as_or_and_chain_atomic_fact(fact: ExistBodyFact) -> Option<OrAndChainAtomicFact> {
    match fact {
        ExistBodyFact::AtomicFact(f) => Some(OrAndChainAtomicFact::AtomicFact(f)),
        ExistBodyFact::AndFact(f) => Some(OrAndChainAtomicFact::AndFact(f)),
        ExistBodyFact::ChainFact(f) => Some(OrAndChainAtomicFact::ChainFact(f)),
        ExistBodyFact::OrFact(f) => Some(OrAndChainAtomicFact::OrFact(f)),
        ExistBodyFact::InlineForall(_) => None,
    }
}
