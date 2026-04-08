use super::kuratowski_by_stmt::{kuratowski_encode_tuple_boxes, kuratowski_pair_tagged_set};
use crate::prelude::*;
use std::collections::HashMap;

fn boxed_objs_from_args(args: &[Obj]) -> Vec<Box<Obj>> {
    args.iter().cloned().map(Box::new).collect()
}

impl Runtime {
    pub fn exec_by_fn_stmt(
        &mut self,
        stmt: &ByFnStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let stmt_exec = Stmt::ByFnStmt(stmt.clone());

        let fn_set = match self.get_cloned_object_in_fn_set(&stmt.function) {
            Some(fs) => fs,
            None => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        format!(
                            "by fn: `{}` is not known to belong to a fn set",
                            stmt.function
                        ),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        let fn_head_atom = match &stmt.function {
            Obj::Identifier(id) => Atom::Identifier(id.clone()),
            Obj::IdentifierWithMod(i) => Atom::IdentifierWithMod(i.clone()),
            _ => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        "by fn: expected a function identifier".to_string(),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        let param_names = ParamGroupWithSet::collect_param_names(&fn_set.params_def_with_set);
        if param_names.is_empty() {
            return Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec,
                    "by fn: fn set has no parameters".to_string(),
                    None,
                    vec![],
                ),
            ));
        }

        let generated_forall_param_names = self.generate_random_unused_names(param_names.len());
        let mut original_param_to_forall_obj: HashMap<String, Obj> =
            HashMap::with_capacity(param_names.len());
        let mut forall_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set.params_def_with_set.len());
        let mut flat_index: usize = 0;
        for param_def_with_set in fn_set.params_def_with_set.iter() {
            let next_flat_index = flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_forall_param_names[flat_index..next_flat_index].to_vec();
            let instantiated_set = self
                .inst_obj(&param_def_with_set.set, &original_param_to_forall_obj)
                .map_err(|inst_error| {
                    RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        "by fn: failed to instantiate generated parameter set".to_string(),
                        Some(inst_error.into()),
                        vec![],
                    ))
                })?;
            forall_param_defs_with_type.push(ParamGroupWithParamType::new(
                generated_names_for_current_group.clone(),
                ParamType::Obj(instantiated_set),
            ));
            for (original_name, generated_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                original_param_to_forall_obj.insert(
                    original_name.clone(),
                    Obj::Identifier(Identifier::new(generated_name.clone())),
                );
            }
            flat_index = next_flat_index;
        }

        let forall_args: Vec<Obj> = param_names
            .iter()
            .map(|param_name| {
                original_param_to_forall_obj
                    .get(param_name)
                    .unwrap()
                    .clone()
            })
            .collect();
        let forall_tuple_struct = Tuple::new(forall_args.clone());
        let encoded_arg_tuple =
            kuratowski_encode_tuple_boxes(&forall_tuple_struct.args).map_err(|_| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: could not encode generated parameter tuple".to_string(),
                    None,
                    vec![],
                ))
            })?;

        let fn_call = Obj::FnObj(FnObj::new(
            fn_head_atom.clone(),
            vec![boxed_objs_from_args(&forall_args)],
        ));

        let pair_in_fn = kuratowski_pair_tagged_set(encoded_arg_tuple, fn_call);

        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(fn_set.dom_facts.len());
        for dom_fact in fn_set.dom_facts.iter() {
            forall_dom_facts.push(
                self.inst_or_and_chain_atomic_fact(dom_fact, &original_param_to_forall_obj)
                    .map_err(|inst_error| {
                        RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            stmt_exec.clone(),
                            "by fn: failed to instantiate generated domain fact".to_string(),
                            Some(inst_error.into()),
                            vec![],
                        ))
                    })?
                    .to_exist_or_and_chain_atomic_fact(),
            );
        }

        let forall_in = ForallFact::new(
            forall_param_defs_with_type,
            forall_dom_facts,
            vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact::new(pair_in_fn, stmt.function.clone(), stmt.line_file.clone()),
            ))],
            stmt.line_file.clone(),
        );

        let generated_name_count = 1 + param_names.len();
        let mut generated_names = self
            .generate_random_unused_names(generated_name_count)
            .into_iter();
        let element_name = generated_names.next().unwrap();
        let mut exist_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set.params_def_with_set.len());
        let mut original_param_to_exist_obj: HashMap<String, Obj> =
            HashMap::with_capacity(param_names.len());

        for param_def_with_set in fn_set.params_def_with_set.iter() {
            let mut exist_param_names: Vec<String> =
                Vec::with_capacity(param_def_with_set.params.len());
            for _ in param_def_with_set.params.iter() {
                exist_param_names.push(generated_names.next().unwrap());
            }

            let instantiated_set = self
                .inst_obj(&param_def_with_set.set, &original_param_to_exist_obj)
                .map_err(|inst_error| {
                    RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        "by fn: failed to instantiate witness parameter set".to_string(),
                        Some(inst_error.into()),
                        vec![],
                    ))
                })?;

            exist_param_defs_with_type.push(ParamGroupWithParamType::new(
                exist_param_names.clone(),
                ParamType::Obj(instantiated_set),
            ));

            for (original_name, exist_name) in param_def_with_set
                .params
                .iter()
                .zip(exist_param_names.iter())
            {
                original_param_to_exist_obj.insert(
                    original_name.clone(),
                    Obj::Identifier(Identifier::new(exist_name.clone())),
                );
            }
        }

        let exist_args: Vec<Obj> = param_names
            .iter()
            .map(|param_name| original_param_to_exist_obj.get(param_name).unwrap().clone())
            .collect();
        let exist_tuple_struct = Tuple::new(exist_args.clone());
        let exist_encoded_arg_tuple = kuratowski_encode_tuple_boxes(&exist_tuple_struct.args)
            .map_err(|_| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: could not encode existential witness tuple".to_string(),
                    None,
                    vec![],
                ))
            })?;
        let exist_fn_call = Obj::FnObj(FnObj::new(
            fn_head_atom.clone(),
            vec![boxed_objs_from_args(&exist_args)],
        ));
        let exist_pair = kuratowski_pair_tagged_set(exist_encoded_arg_tuple, exist_fn_call);

        let mut exist_facts: Vec<OrAndChainAtomicFact> =
            Vec::with_capacity(fn_set.dom_facts.len() + 1);
        for dom_fact in fn_set.dom_facts.iter() {
            exist_facts.push(
                self.inst_or_and_chain_atomic_fact(dom_fact, &original_param_to_exist_obj)
                    .map_err(|inst_error| {
                        RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            stmt_exec.clone(),
                            "by fn: failed to instantiate witness domain fact".to_string(),
                            Some(inst_error.into()),
                            vec![],
                        ))
                    })?,
            );
        }
        exist_facts.push(OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(
                Obj::Identifier(Identifier::new(element_name.clone())),
                exist_pair,
                stmt.line_file.clone(),
            ),
        )));

        let exist_fact = ExistFact::new(
            exist_param_defs_with_type,
            exist_facts,
            stmt.line_file.clone(),
        );

        let forall_exist = ForallFact::new(
            vec![ParamGroupWithParamType::new(
                vec![element_name],
                ParamType::Obj(stmt.function.clone()),
            )],
            vec![],
            vec![ExistOrAndChainAtomicFact::ExistFact(exist_fact)],
            stmt.line_file.clone(),
        );

        // `infer` on forall facts is empty; mirror `by_enumerate` so pipeline JSON shows the facts.
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&Fact::ForallFact(forall_in.clone()));
        let infer_in = self
            .store_fact_without_well_defined_verified_and_infer(Fact::ForallFact(forall_in))
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store Kuratowski membership fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_in);

        infer_result.new_fact(&Fact::ForallFact(forall_exist.clone()));
        let infer_exist = self
            .store_fact_without_well_defined_verified_and_infer(Fact::ForallFact(forall_exist))
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store element characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_exist);

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![]),
        ))
    }
}
