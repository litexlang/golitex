use crate::ast::fact::AtomicFact;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    VerifyAtomicFactWellDefinedResult,
    PredicateSignatureWellDefinedFailure, PredicateSignatureWellDefinedProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Atomic-except-equality only. EqualFact uses verify_equal_fact_well_definedness.
    // WD each argument object, then resolve the predicate signature.
    // First soft-missing argument → Failed; otherwise Success with proof.
    pub fn verify_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactWellDefinedResult> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Err(RuntimeError::InternalBug(
                "EqualFact well-definedness must use verify_equal_fact_well_definedness"
                    .to_string(),
            ));
        }
        let args = atomic_except_equality_fact_arg_objs(fact);
        let mut succeeded_args = Vec::new();
        for arg in args {
            match self.verify_obj_well_definedness(arg, verify_state.clone())? {
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Argument(reason),
                    ));
                }
                VerifyObjWellDefinedResult::Success(proof) => succeeded_args.push(proof),
            }
        }
        // A checked goal may not borrow a declaration from its later proof
        // body. For example, `claim: ? $chosen(0)` must fail here if chosen
        // has not been declared, even if the body defines it locally.
        let user_signature = match fact {
            AtomicFact::NormalAtomicFact(normal) => Some((&normal.predicate, normal.body.len())),
            AtomicFact::NotNormalAtomicFact(normal) => Some((&normal.predicate, normal.body.len())),
            _ => None,
        };
        let predicate_signature = match user_signature {
            Some((predicate, actual_arity)) => {
                let signature = if let Some(def) = self.def_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::Prop {
                        predicate: predicate.clone(),
                        arity: def.typed_parameters.groups.iter().map(|g| g.params.len()).sum(),
                    }
                } else if let Some(def) = self.def_abstract_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::AbstractProp {
                        predicate: predicate.clone(), arity: def.params.len(),
                    }
                } else {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Undefined {
                                predicate: predicate.clone(),
                            },
                        },
                    ));
                };
                let (PredicateSignatureWellDefinedProof::Prop { arity, .. }
                    | PredicateSignatureWellDefinedProof::AbstractProp { arity, .. }) = &signature
                    else { unreachable!("resolved user predicate signature") };
                if *arity != actual_arity {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Arity {
                                predicate: predicate.clone(), expected: *arity, actual: actual_arity,
                            },
                        },
                    ));
                }
                signature
            }
            _ => PredicateSignatureWellDefinedProof::Builtin,
        };
        Ok(VerifyAtomicFactWellDefinedResult::Success(
            AtomicFactWellDefinedProof {
                well_defined_of_each_parameter: succeeded_args,
                predicate_signature,
            },
        ))
    }

    // For and/chain mixed storage: EqualFact uses equality WD then converts;
    // other atomics use atomic-except-equality WD.
    pub(crate) fn verify_atomic_component_well_definedness(
        &mut self,
        atomic: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactWellDefinedResult> {
        match atomic {
            AtomicFact::EqualFact(equal_fact) => {
                match self.verify_equal_fact_well_definedness(equal_fact, verify_state)? {
                    VerifyEqualFactWellDefinedResult::Success(proof) => {
                        Ok(VerifyAtomicFactWellDefinedResult::Success(proof.into()))
                    }
                    VerifyEqualFactWellDefinedResult::Failed(reason) => {
                        Ok(VerifyAtomicFactWellDefinedResult::Failed(reason.into()))
                    }
                }
            }
            _ => self.verify_atomic_fact_well_definedness(atomic, verify_state),
        }
    }
}

fn atomic_except_equality_fact_arg_objs(fact: &AtomicFact) -> Vec<&Obj> {
    match fact {
        AtomicFact::EqualFact(_) => unreachable!("EqualFact rejected above"),
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
        AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::ProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::ProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::PrimeFact(f) => vec![&f.value],
        AtomicFact::NotPrimeFact(f) => vec![&f.value],
        AtomicFact::CoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotCoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::DvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotDvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::InjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotInjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::SurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotSurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::BijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotBijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::IsChoiceFunctionForFact(f) => vec![&f.index, &f.set, &f.family, &f.choice],
        AtomicFact::NotIsChoiceFunctionForFact(f) => vec![&f.index, &f.set, &f.family, &f.choice],
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/execute/predicate_signature_wd/tests.rs"]
mod predicate_signature_tests;
