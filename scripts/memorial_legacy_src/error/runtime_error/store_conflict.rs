//! Conversion of fact-construction failures into storage conflicts.

use super::{NewFactRuntimeError, RuntimeError, RuntimeErrorStruct};

impl RuntimeError {
    pub fn wrap_new_fact_as_store_conflict(e: RuntimeError) -> RuntimeError {
        match e {
            RuntimeError::NewFactError(s) => NewFactRuntimeError(RuntimeErrorStruct::new(
                s.statement.clone(),
                s.msg.clone(),
                s.line_file.clone(),
                Some(NewFactRuntimeError(*s).into()),
                vec![],
            ))
            .into(),
            _ => e,
        }
    }
}
