use crate::prelude::*;

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
        Self::stmt_unsupported(Stmt::ByFnStmt(stmt.clone()))
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
