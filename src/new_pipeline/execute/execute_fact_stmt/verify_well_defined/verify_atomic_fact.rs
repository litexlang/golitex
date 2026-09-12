use super::VerifyObjResult;
use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub struct AtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<VerifyObjResult>,
}

impl Runtime {
    // Classify atomic fact shape, then WD each argument object.
    pub fn verify_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<AtomicFactWellDefinedProof> {
        let args = atomic_fact_arg_objs(fact)?;
        let mut well_defined_of_each_parameter = Vec::new();
        for arg in args {
            well_defined_of_each_parameter
                .push(self.verify_obj_well_definedness(arg, verify_state.clone())?);
        }
        Ok(AtomicFactWellDefinedProof {
            well_defined_of_each_parameter,
        })
    }
}

// Tracer: equality is wired; other atomic shapes come next.
fn atomic_fact_arg_objs(fact: &AtomicFact) -> RuntimeResult<Vec<&Obj>> {
    match fact {
        AtomicFact::EqualFact(EqualFact { left, right, .. }) => Ok(vec![left, right]),
        _ => Err(RuntimeError::Unsupported(
            "verify_atomic_fact_well_definedness: only EqualFact args are wired for the tracer"
                .to_string(),
        )),
    }
}
