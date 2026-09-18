use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::VerifyExistFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::VerifyForallFactWithIffWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::VerifyOrFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

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
            Fact::ExistFact(exist_fact) => Ok(self.wrap_exist_fact_wd(exist_fact, verify_state)?),
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
        fact: &crate::new_pipeline::ast::fact::AndFact,
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
        fact: &crate::new_pipeline::ast::fact::ChainFact,
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
        fact: &crate::new_pipeline::ast::fact::OrFact,
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
        fact: &crate::new_pipeline::ast::fact::ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        Ok(
            match self.verify_exist_fact_well_definedness(fact, verify_state)? {
                VerifyExistFactWellDefinedResult::Success(proof) => {
                    VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ExistFact(proof))
                }
                VerifyExistFactWellDefinedResult::Failed(reason) => {
                    VerifyFactWellDefinedResult::Failed(
                        FailToVerifyFactWellDefinedResult::ExistFact(reason),
                    )
                }
            },
        )
    }

    pub(crate) fn wrap_forall_fact_wd(
        &mut self,
        fact: &crate::new_pipeline::ast::fact::ForallFact,
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
        fact: &crate::new_pipeline::ast::fact::ForallFactWithIff,
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
        fact: &crate::new_pipeline::ast::fact::NotForallFact,
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
