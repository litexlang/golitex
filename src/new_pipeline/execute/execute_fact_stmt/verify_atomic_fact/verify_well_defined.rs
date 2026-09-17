use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    VerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Classify atomic fact shape, then WD each argument object.
    // First soft-missing argument → Failed; otherwise Success with proof.
    pub fn verify_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactWellDefinedResult> {
        let args = atomic_fact_arg_objs(fact);
        let mut succeeded_args = Vec::new();
        for (failed_arg_index, arg) in args.into_iter().enumerate() {
            match self.verify_obj_well_definedness(arg, verify_state.clone())? {
                VerifyObjWellDefinedResult::FailToVerifyWellDefined(reason) => {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult {
                            failed_arg_index,
                            succeeded_args,
                            reason,
                        },
                    ));
                }
                success => succeeded_args.push(success),
            }
        }
        Ok(VerifyAtomicFactWellDefinedResult::Success(
            AtomicFactWellDefinedProof {
                well_defined_of_each_parameter: succeeded_args,
            },
        ))
    }
}

fn atomic_fact_arg_objs(fact: &AtomicFact) -> Vec<&Obj> {
    match fact {
        AtomicFact::EqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::InFact(f) => vec![&f.element, &f.set],
        AtomicFact::NotInFact(f) => vec![&f.element, &f.set],
        AtomicFact::LessFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::IsSetFact(f) => vec![&f.set],
        AtomicFact::NotIsSetFact(f) => vec![&f.set],
        AtomicFact::IsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::NotIsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::IsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::NotIsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::IsTupleFact(f) => vec![&f.set],
        AtomicFact::NotIsTupleFact(f) => vec![&f.set],
        AtomicFact::IsCartFact(f) => vec![&f.set],
        AtomicFact::NotIsCartFact(f) => vec![&f.set],
        AtomicFact::FnEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
        AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
    }
}
