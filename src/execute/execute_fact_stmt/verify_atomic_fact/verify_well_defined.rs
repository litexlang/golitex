//! Tier 1 frozen backbone: atomic-except-equality WD pipeline
//! (argument WD → predicate signature/arity → known-cite → predicate-domain handoff).
//! Predicate-family domain routing lives in Tier 2 `dispatch_predicate_domain_wd.rs`.

use super::dispatch_predicate_domain_wd::atomic_except_equality_fact_arg_objs;
use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, DetailedAtomicFactWellDefinedProof,
    FailToVerifyAtomicFactWellDefinedResult, PredicateDomainProof,
    PredicateSignatureWellDefinedFailure, PredicateSignatureWellDefinedProof,
    VerifyAtomicFactWellDefinedResult,
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
        for arg in &args {
            match self.verify_obj_well_definedness(arg, verify_state.clone())? {
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Argument {
                            fact: fact.clone(),
                            reason,
                        },
                    ));
                }
                VerifyObjWellDefinedResult::Success(proof) => {
                    self.result_detail()
                        .require(proof.detail(), "atomic WD argument")?;
                    if self.result_detail() == crate::result_detail::OutputDetail::Detailed {
                        succeeded_args.push(proof);
                    }
                }
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
                let builtin_arity = match predicate {
                    crate::ast::names::AtomicName::Plain { name } => {
                        crate::builtin_theorem::builtin_certificate_arity(name)
                    }
                    _ => None,
                };
                let signature = if builtin_arity.is_some() {
                    PredicateSignatureWellDefinedProof::Builtin
                } else if let Some(def) = self.def_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::Prop {
                        predicate: predicate.clone(),
                        arity: def
                            .typed_parameters
                            .groups
                            .iter()
                            .map(|g| g.params.len())
                            .sum(),
                    }
                } else if let Some(def) = self.def_abstract_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::AbstractProp {
                        predicate: predicate.clone(),
                        arity: def.params.len(),
                    }
                } else {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            fact: fact.clone(),
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Undefined {
                                predicate: predicate.clone(),
                            },
                        },
                    ));
                };
                let arity = match &signature {
                    PredicateSignatureWellDefinedProof::Prop { arity, .. }
                    | PredicateSignatureWellDefinedProof::AbstractProp { arity, .. } => *arity,
                    PredicateSignatureWellDefinedProof::Builtin => {
                        builtin_arity.expect("resolved builtin certificate signature")
                    }
                };
                if arity != actual_arity {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            fact: fact.clone(),
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Arity {
                                predicate: predicate.clone(),
                                expected: arity,
                                actual: actual_arity,
                            },
                        },
                    ));
                }
                signature
            }
            _ => PredicateSignatureWellDefinedProof::Builtin,
        };
        if let Some(cite) = self.lookup_known_atomic_fact(fact) {
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::ByKnownFact(cite),
                    }
                })?,
            ));
        }

        self.dispatch_atomic_predicate_domain_well_definedness(
            fact,
            &args,
            succeeded_args,
            predicate_signature,
            verify_state,
        )
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

#[cfg(test)]
#[path = "../../../../tests/unit/execute/predicate_signature_wd/tests.rs"]
mod predicate_signature_tests;
