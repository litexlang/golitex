use super::kuratowski_by_stmt::kuratowski_encode_tuple_boxes;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_tuple_stmt(
        &mut self,
        stmt: &ByTupleStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt_exec = stmt.clone().into();

        let tuple_struct = match &stmt.obj {
            Obj::Tuple(tuple) => tuple.clone(),
            _ => {
                if let Some(t) = self.get_obj_equal_to_tuple(&stmt.obj.to_string()) {
                    t
                } else {
                    return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            stmt_exec,
                            format!("by tuple: `{}` is not known to denote a tuple", stmt.obj),
                            None,
                            vec![],
                        )));
                }
            }
        };

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("by tuple: `{}` is not well-defined", stmt.obj),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let encoded = kuratowski_encode_tuple_boxes(&tuple_struct.args).map_err(|msg| {
            RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                stmt_exec.clone(),
                format!("by tuple: {}", msg),
                None,
                vec![],
            ))
        })?;

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
                Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
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
