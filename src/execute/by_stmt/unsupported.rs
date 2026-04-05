use crate::prelude::*;

fn param_defs_with_type_from_fn_set_with_dom(
    fn_set_with_params: &FnSetWithParams,
) -> Vec<ParamGroupWithParamType> {
    let mut param_defs_with_type: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(fn_set_with_params.params_def_with_set.len());
    for param_def_with_set in fn_set_with_params.params_def_with_set.iter() {
        param_defs_with_type.push(ParamGroupWithParamType::new(
            param_def_with_set.params.clone(),
            ParamType::Obj(param_def_with_set.set.clone()),
        ));
    }
    param_defs_with_type
}

fn kuratowski_encode_tuple_boxes(args: &[Box<Obj>]) -> Result<Obj, &'static str> {
    if args.is_empty() {
        return Err("empty tuple");
    }
    if args.len() == 1 {
        return Ok((*args[0]).clone());
    }
    let mut acc = (*args[args.len() - 1]).clone();
    for i in (0..args.len() - 1).rev() {
        acc = kuratowski_pair_tagged_set((*args[i]).clone(), acc);
    }
    Ok(acc)
}

fn kuratowski_pair_tagged_set(left: Obj, right: Obj) -> Obj {
    let singleton = Obj::ListSet(ListSet::new(vec![left.clone()]));
    let unordered_pair = Obj::ListSet(ListSet::new(vec![left, right]));
    Obj::ListSet(ListSet::new(vec![singleton, unordered_pair]))
}

fn kuratowski_encode_tuple_args(
    args: &[Box<Obj>],
    stmt: &ByTupleStmt,
) -> Result<Obj, RuntimeError> {
    if args.is_empty() {
        return Err(RuntimeError::ExecStmtError(
            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                Stmt::ByTuple(stmt.clone()),
                "by tuple: empty tuple has no Kuratowski encoding".to_string(),
                None,
                vec![],
            ),
        ));
    }
    if args.len() == 1 {
        return Ok((*args[0]).clone());
    }
    let mut acc = (*args[args.len() - 1]).clone();
    for i in (0..args.len() - 1).rev() {
        acc = kuratowski_pair_tagged_set((*args[i]).clone(), acc);
    }
    Ok(acc)
}

impl Runtime {
    pub fn exec_by_fn_stmt(
        &mut self,
        stmt: &ByFnStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let stmt_exec = Stmt::ByFnStmt(stmt.clone());

        let fn_set = match self.get_cloned_fn_set_where_fn_belongs_to(&stmt.function) {
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

        let param_names =
            ParamGroupWithSet::collect_param_names(&fn_set.params_def_with_set);
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

        let tuple_elements: Vec<Obj> = param_names
            .iter()
            .map(|n| Obj::Identifier(Identifier::new(n.clone())))
            .collect();
        let tuple_struct = Tuple::new(tuple_elements);
        let encoded_arg_tuple = match kuratowski_encode_tuple_boxes(&tuple_struct.args) {
            Ok(o) => o,
            Err(_) => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        "by fn: could not encode parameter tuple".to_string(),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        let mut function_args: Vec<Box<Obj>> = Vec::with_capacity(param_names.len());
        for param_name in param_names.iter() {
            function_args.push(Box::new(Obj::Identifier(Identifier::new(
                param_name.clone(),
            ))));
        }
        let fn_body_groups = vec![function_args];
        let fn_call = Obj::FnObj(FnObj::new(fn_head_atom, fn_body_groups));

        let pair_in_fn = kuratowski_pair_tagged_set(encoded_arg_tuple, fn_call.clone());

        let param_defs_with_type = param_defs_with_type_from_fn_set_with_dom(&fn_set);
        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(fn_set.dom_facts.len());
        for dom_fact in fn_set.dom_facts.iter() {
            forall_dom_facts.push(dom_fact.clone().to_exist_or_and_chain_atomic_fact());
        }

        let forall_in = ForallFact::new(
            param_defs_with_type.clone(),
            forall_dom_facts.clone(),
            vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact::new(
                    pair_in_fn,
                    stmt.function.clone(),
                    stmt.line_file.clone(),
                ),
            ))],
            stmt.line_file.clone(),
        );

        let random_name = self.generate_a_random_unused_name();
        let exist_fact = ExistFact::new(
            vec![ParamGroupWithParamType::new(
                vec![random_name.clone()],
                ParamType::Obj((*fn_set.ret_set).clone()),
            )],
            vec![OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact::new(
                    fn_call,
                    Obj::Identifier(Identifier::new(random_name)),
                    stmt.line_file.clone(),
                ),
            ))],
            stmt.line_file.clone(),
        );

        let forall_exist = ForallFact::new(
            param_defs_with_type,
            forall_dom_facts,
            vec![ExistOrAndChainAtomicFact::ExistFact(exist_fact)],
            stmt.line_file.clone(),
        );

        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(Fact::ForallFact(forall_in))
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store Kuratowski membership fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;

        let forall_infer = self
            .store_fact_without_well_defined_verified_and_infer(Fact::ForallFact(forall_exist))
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store range existence fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(forall_infer);

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![]),
        ))
    }

    pub fn exec_by_cart_stmt(
        &mut self,
        stmt: &ByCartStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByCartStmt(stmt.clone()))
    }

    pub fn exec_by_tuple_stmt(
        &mut self,
        stmt: &ByTupleStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let stmt_exec = Stmt::ByTuple(stmt.clone());

        let tuple_struct = match &stmt.obj {
            Obj::Tuple(tuple) => tuple.clone(),
            _ => {
                if let Some(t) = self.get_obj_equal_to_tuple(&stmt.obj.to_string()) {
                    t
                } else {
                    return Err(RuntimeError::ExecStmtError(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            stmt_exec,
                            format!("by tuple: `{}` is not known to denote a tuple", stmt.obj),
                            None,
                            vec![],
                        ),
                    ));
                }
            }
        };

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state)
            .map_err(|e| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("by tuple: `{}` is not well-defined", stmt.obj),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let encoded = kuratowski_encode_tuple_args(&tuple_struct.args, stmt)?;

        let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            stmt.obj.clone(),
            encoded,
            stmt.line_file.clone(),
        )));

        match self.store_fact_without_well_defined_verified_and_infer(equal_fact) {
            Ok(infer_result) => {
                self.store_tuple_obj_and_cart(
                    &stmt.obj.to_string(),
                    Some(tuple_struct),
                    None,
                    stmt.line_file.clone(),
                );
                Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                    NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![]),
                ))
            }
            Err(store_error) => Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec,
                    "by tuple: failed to store definitional equality".to_string(),
                    Some(store_error.into()),
                    vec![],
                ),
            )),
        }
    }
}
