use super::kuratowski_by_stmt::kuratowski_encode_tuple_boxes;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_tuple_stmt(&mut self, stmt: &ByTupleStmt) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();

        let tuple_struct = match &stmt.obj {
            Obj::Tuple(tuple) => tuple.clone(),
            _ => {
                if let Some(t) = self.get_obj_equal_to_tuple(&stmt.obj.to_string()) {
                    t
                } else {
                    return Err(RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt_exec;
                        let __message =
                            format!("by tuple: `{}` is not known to denote a tuple", stmt.obj);
                        let __cause = None;
                        let __inside = vec![];
                        let __line_file = __stmt.line_file();
                        let __previous_error = if __message.is_empty() {
                            __cause
                        } else {
                            Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                        };
                        RuntimeErrorStruct::new(
                            Some(__stmt),
                            __message,
                            __line_file,
                            __previous_error,
                            __inside,
                        )
                    }));
                }
            }
        };

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state)
            .map_err(|e| {
                RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt_exec.clone();
                    let __message = format!("by tuple: `{}` is not well-defined", stmt.obj);
                    let __cause = Some(e);
                    let __inside = vec![];
                    let __line_file = __stmt.line_file();
                    let __previous_error = if __message.is_empty() {
                        __cause
                    } else {
                        Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                    };
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        __message,
                        __line_file,
                        __previous_error,
                        __inside,
                    )
                })
            })?;

        let encoded = kuratowski_encode_tuple_boxes(&tuple_struct.args).map_err(|msg| {
            RuntimeError::ExecStmtError({
                let __stmt: Stmt = stmt_exec.clone();
                let __message = format!("by tuple: {}", msg);
                let __cause = None;
                let __inside = vec![];
                let __line_file = __stmt.line_file();
                let __previous_error = if __message.is_empty() {
                    __cause
                } else {
                    Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                };
                RuntimeErrorStruct::new(
                    Some(__stmt),
                    __message,
                    __line_file,
                    __previous_error,
                    __inside,
                )
            })
        })?;

        let equal_fact = EqualFact::new(stmt.obj.clone(), encoded, stmt.line_file.clone()).into();

        match self.store_fact_without_well_defined_verified_and_infer(equal_fact) {
            Ok(infer_result) => {
                self.store_tuple_obj_and_cart(
                    &stmt.obj.to_string(),
                    Some(tuple_struct),
                    None,
                    stmt.line_file.clone(),
                );
                Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
            }
            Err(store_error) => Err(RuntimeError::ExecStmtError({
                let __stmt: Stmt = stmt_exec;
                let __message = "by tuple: failed to store definitional equality".to_string();
                let __cause = Some(store_error);
                let __inside = vec![];
                let __line_file = __stmt.line_file();
                let __previous_error = if __message.is_empty() {
                    __cause
                } else {
                    Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                };
                RuntimeErrorStruct::new(
                    Some(__stmt),
                    __message,
                    __line_file,
                    __previous_error,
                    __inside,
                )
            })),
        }
    }
}
