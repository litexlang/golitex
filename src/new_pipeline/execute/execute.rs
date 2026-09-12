use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::{AtomObj, Identifier, Number, Obj};
use crate::new_pipeline::ast::stmt::{DefinitionStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude;
use std::rc::Rc;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<()> {
        match stmt {
            Stmt::Fact(fact) => self.exec_fact(fact),
            Stmt::Definition(DefinitionStmt::LetObjStmt(_)) => {
                // Parse already occupied the name. Definition storage comes later.
                Ok(())
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: only Fact and let are wired for the tracer".to_string(),
            )),
        }
    }

    fn exec_fact(&mut self, fact: &Fact) -> RuntimeResult<()> {
        match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) => {
                let legacy = bridge_equal_fact(equal)?;
                self.execute_fact_statement2(&legacy.into())?;
                Ok(())
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_fact: only equality facts are wired for the tracer".to_string(),
            )),
        }
    }
}

fn bridge_equal_fact(equal: &EqualFact) -> RuntimeResult<prelude::EqualFact> {
    Ok(prelude::EqualFact {
        fact_id: prelude::FactId::new(equal.fact_id.value()),
        left: bridge_obj(&equal.left)?,
        right: bridge_obj(&equal.right)?,
        line_file: (equal.span.line, Rc::from(equal.span.path.to_string())),
    })
}

fn bridge_obj(obj: &Obj) -> RuntimeResult<prelude::Obj> {
    match obj {
        Obj::Number(Number { normalized_value }) => {
            Ok(prelude::Number::new(normalized_value.clone()).into())
        }
        Obj::Add(add) => Ok(prelude::Add::new(
            bridge_obj(add.left.as_ref())?,
            bridge_obj(add.right.as_ref())?,
        )
        .into()),
        Obj::Atom(AtomObj::Identifier(Identifier { name })) => {
            Ok(prelude::Identifier::new(name.clone()).into())
        }
        _ => Err(RuntimeError::Unsupported(
            "new_pipeline: object bridge only supports Number, Add, and Identifier for the tracer"
                .to_string(),
        )),
    }
}
