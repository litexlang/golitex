use crate::ast::fact::{AtomicFact, ExistShapedFact, Fact};
use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::VerifyExistShapedFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::VerifyForallFactWithIffWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_or_fact::VerifyOrFactWellDefinedResult;
use crate::execute::execute_fact_stmt::well_defined_results::well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Thin Fact WD dispatcher: match shape, then call verify_xxx_fact_well_definedness.
    // Prefer calling the fine-grained entry when the Fact shape is already known.
    pub fn verify_fact_well_definedness(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        match fact {
            Fact::AtomicFact(fact) => Ok(self.wrap_atomic_fact_wd(fact, verify_state)?),
            Fact::AndFact(and_fact) => Ok(self.wrap_and_fact_wd(and_fact, verify_state)?),
            Fact::ChainFact(chain_fact) => Ok(self.wrap_chain_fact_wd(chain_fact, verify_state)?),
            Fact::OrFact(or_fact) => Ok(self.wrap_or_fact_wd(or_fact, verify_state)?),
            Fact::ExistFact(exist_fact) => Ok(self.wrap_exist_fact_wd(&ExistShapedFact::Exist(exist_fact.clone()), verify_state)?),
            Fact::ExistUniqueFact(exist_fact) => Ok(self.wrap_exist_fact_wd(&ExistShapedFact::ExistUnique(exist_fact.clone()), verify_state)?),
            Fact::NotExistFact(exist_fact) => Ok(self.wrap_exist_fact_wd(&ExistShapedFact::NotExist(exist_fact.clone()), verify_state)?),
            Fact::ForallFact(forall_fact) => Ok(self.wrap_forall_fact_wd(forall_fact, verify_state)?),
            Fact::ForallFactWithIff(forall_iff) => {
                Ok(self.wrap_forall_fact_with_iff_wd(forall_iff, verify_state)?)
            }
            Fact::NotForall(not_forall) => {
                Ok(self.wrap_not_forall_fact_wd(not_forall, verify_state)?)
            }
        }
    }
}

impl Runtime {
    pub(crate) fn wrap_atomic_fact_wd(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => {
                Ok(
                    match self.verify_equal_fact_well_definedness(equal_fact, verify_state)? {
                        VerifyEqualFactWellDefinedResult::Success(proof) => {
                            VerifyFactWellDefinedResult::Success(FactWellDefinedProof::Equality(
                                proof,
                            ))
                        }
                        VerifyEqualFactWellDefinedResult::Failed(reason) => {
                            VerifyFactWellDefinedResult::Failed(
                                FailToVerifyFactWellDefinedResult::Equality(reason),
                            )
                        }
                    },
                )
            }
            _ => Ok(
                match self.verify_atomic_fact_well_definedness(fact, verify_state)? {
                    VerifyAtomicFactWellDefinedResult::Success(proof) => {
                        VerifyFactWellDefinedResult::Success(
                            FactWellDefinedProof::AtomicExceptEquality(proof),
                        )
                    }
                    VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                        VerifyFactWellDefinedResult::Failed(
                            FailToVerifyFactWellDefinedResult::AtomicExceptEquality(reason),
                        )
                    }
                },
            ),
        }
    }

    pub(crate) fn wrap_and_fact_wd(
        &mut self,
        fact: &crate::ast::fact::AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_and_fact_well_definedness(fact, verify_state)? {
                VerifyAndFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::AndFact {
                        components: proof.components,
                    })
                }
                VerifyAndFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(FailToVerifyFactWellDefinedResult::AndFact(
                        reason,
                    ))
                }
            },
        )
    }

    pub(crate) fn wrap_chain_fact_wd(
        &mut self,
        fact: &crate::ast::fact::ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_chain_fact_well_definedness(fact, verify_state)? {
                VerifyChainFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ChainFact {
                        adjacent: proof.adjacent,
                    })
                }
                VerifyChainFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::ChainFact(reason),
                    )
                }
            },
        )
    }

    pub(crate) fn wrap_or_fact_wd(
        &mut self,
        fact: &crate::ast::fact::OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(match self.verify_or_fact_well_definedness(fact, verify_state)? {
            VerifyOrFactWellDefinedResult::Success(proof) => {
                VerifyFactWellDefinedResult::Success(FactWellDefinedProof::OrFact(proof))
            }
            VerifyOrFactWellDefinedResult::Failed(reason) => {
                VerifyFactWellDefinedResult::Failed(FailToVerifyFactWellDefinedResult::OrFact(
                    reason,
                ))
            }
        })
    }

    pub(crate) fn wrap_exist_fact_wd(
        &mut self,
        fact: &crate::ast::fact::ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_exist_shaped_fact_well_definedness(fact, verify_state)? {
                VerifyExistShapedFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ExistFact(proof))
                }
                VerifyExistShapedFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::ExistFact(reason),
                    )
                }
            },
        )
    }

    pub(crate) fn wrap_forall_fact_wd(
        &mut self,
        fact: &crate::ast::fact::ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_forall_fact_well_definedness(fact, verify_state)? {
                VerifyForallFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(proof))
                }
                VerifyForallFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::ForallFact(reason),
                    )
                }
            },
        )
    }

    pub(crate) fn wrap_forall_fact_with_iff_wd(
        &mut self,
        fact: &crate::ast::fact::ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_forall_fact_with_iff_well_definedness(fact, verify_state)? {
                VerifyForallFactWithIffWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFactWithIff(
                        proof,
                    ))
                }
                VerifyForallFactWithIffWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::ForallFactWithIff(reason),
                    )
                }
            },
        )
    }

    pub(crate) fn wrap_not_forall_fact_wd(
        &mut self,
        fact: &crate::ast::fact::NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_not_forall_fact_well_definedness(fact, verify_state)? {
                VerifyNotForallFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::NotForall(proof))
                }
                VerifyNotForallFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::NotForall(reason),
                    )
                }
            },
        )
    }
}

impl Runtime {
    // Infer-produced fact: WD must succeed, then store_fact + infer_fact.
    // WD success is stored into ExecEnv (store_well_defined_fact).
    // Example: membership projection stores `a $in R` through this path.
    pub(crate) fn store_inferred_fact_and_infer(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<crate::store_fact_and_infer::StoreFactAndInferResult> {
        match self.try_store_inferred_fact_and_infer(fact)? {
            Some(ok) => Ok(ok),
            None => Err(crate::runtime::RuntimeError::InternalBug(
                "inferred fact failed well-definedness check".to_string(),
            )),
        }
    }

    // Soft variant: WD failure yields None (rule may skip) instead of SessionError.
    // Example: optional order flip when `(-1)*x` is not yet known real.
    pub(crate) fn try_store_inferred_fact_and_infer(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<
        Option<crate::store_fact_and_infer::StoreFactAndInferResult>,
    > {
        let verify_state = VerifyState {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
};
        let wd = self.verify_fact_well_definedness(fact, verify_state)?;
        if wd.is_failed() {
            return Ok(None);
        }
        Ok(Some(self.store_fact_and_infer(fact)?))
    }
}
