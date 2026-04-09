use crate::prelude::*;
use std::collections::HashMap;

fn boxed_objs_from_args(args: &[Obj]) -> Vec<Box<Obj>> {
    args.iter().cloned().map(Box::new).collect()
}

impl Runtime {
    pub fn exec_by_fn_stmt(
        &mut self,
        stmt: &ByFnStmt,
    ) -> Result<StmtExecResult, RuntimeError> {
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

        let mut generated_forall_names = self
            .generate_random_unused_names(param_names.len() + 1)
            .into_iter();
        let forall_element_name = generated_forall_names.next().unwrap();
        let generated_forall_param_names: Vec<String> = generated_forall_names.collect();
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
        let forall_element_obj = Obj::Identifier(Identifier::new(forall_element_name.clone()));
        let fn_call = Obj::FnObj(FnObj::new(
            fn_head_atom.clone(),
            vec![boxed_objs_from_args(&forall_args)],
        ));
        let pair_in_fn = Obj::Tuple(Tuple::new(vec![Obj::Tuple(Tuple::new(forall_args)), fn_call]));

        let forall_in = ForallFact::new(
            vec![ParamGroupWithParamType::new(
                vec![forall_element_name],
                ParamType::Obj(stmt.function.clone()),
            )],
            vec![],
            vec![ExistOrAndChainAtomicFact::ExistFact(ExistFact::new(
                forall_param_defs_with_type,
                {
                    let mut facts: Vec<OrAndChainAtomicFact> =
                        Vec::with_capacity(fn_set.dom_facts.len() + 1);
                    for dom_fact in fn_set.dom_facts.iter() {
                        facts.push(
                            self.inst_or_and_chain_atomic_fact(dom_fact, &original_param_to_forall_obj)
                                .map_err(|inst_error| {
                                    RuntimeError::from(
                                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                            stmt_exec.clone(),
                                            "by fn: failed to instantiate generated domain fact"
                                                .to_string(),
                                            Some(inst_error.into()),
                                            vec![],
                                        ),
                                    )
                                })?,
                        );
                    }
                    facts.push(OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                        EqualFact::new(
                            forall_element_obj,
                            pair_in_fn,
                            stmt.line_file.clone(),
                        ),
                    )));
                    facts
                },
                stmt.line_file.clone(),
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
        let exist_fn_call = Obj::FnObj(FnObj::new(
            fn_head_atom.clone(),
            vec![boxed_objs_from_args(&exist_args)],
        ));
        let exist_pair = Obj::Tuple(Tuple::new(vec![
            Obj::Tuple(Tuple::new(exist_args)),
            exist_fn_call,
        ]));
        let exist_element_obj = Obj::Identifier(Identifier::new(element_name.clone()));

        let exist_fact = ExistFact::new(
            vec![ParamGroupWithParamType::new(
                vec![element_name],
                ParamType::Obj(stmt.function.clone()),
            )],
            vec![OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact::new(
                    exist_element_obj,
                    exist_pair,
                    stmt.line_file.clone(),
                ),
            ))],
            stmt.line_file.clone(),
        );

        let forall_exist = ForallFact::new(
            exist_param_defs_with_type,
            {
                let mut dom_facts: Vec<ExistOrAndChainAtomicFact> =
                    Vec::with_capacity(fn_set.dom_facts.len());
                for dom_fact in fn_set.dom_facts.iter() {
                    dom_facts.push(
                        self.inst_or_and_chain_atomic_fact(dom_fact, &original_param_to_exist_obj)
                            .map_err(|inst_error| {
                                RuntimeError::from(
                                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                        stmt_exec.clone(),
                                        "by fn: failed to instantiate witness domain fact"
                                            .to_string(),
                                        Some(inst_error.into()),
                                        vec![],
                                    ),
                                )
                            })?
                            .to_exist_or_and_chain_atomic_fact(),
                    );
                }
                dom_facts
            },
            vec![ExistOrAndChainAtomicFact::ExistFact(exist_fact)],
            stmt.line_file.clone(),
        );

        // `store_fact...` on forall facts already feeds the stored fact back through `infer`,
        // so avoid pre-recording the same fact here or JSON `infer_facts` will show duplicates.
        let mut infer_result = InferResult::new();
        let infer_in = self
            .store_fact_without_well_defined_verified_and_infer(Fact::ForallFact(forall_in))
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store graph-element characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_in);

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

        Ok(StmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![]),
        ))
    }
}
