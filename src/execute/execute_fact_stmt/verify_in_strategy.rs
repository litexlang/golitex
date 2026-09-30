//! Proof search inside a strategy subtree.
//!
//! Truth search: known, cite-only / zero-premise builtin, nested strategy.
//! Forbidden for truth: premise-producing builtin, by-def, known forall, rewrite.
//! WD of a strategy premise uses top-level WD without store (expression must be
//! meaningful); that is separate from the strategy truth steps.

use crate::ast::fact::{AtomicFact, Fact};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    atomic_except_equality_fact_result_from_search_fail,
    atomic_except_equality_fact_result_from_success,
    atomic_except_equality_fact_result_from_wd_fail, AtomicExceptEqualityFactSearchedProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::{
    VerifyAtomicFactWellDefinedResult, VerifyEqualFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;

impl Runtime {
    // Top-level entry: builtin strategy first, then user-defined strategy.
    pub fn verify_by_strategy_atomic_except_equality(
        &mut self,
        fact: &AtomicFact,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        let ctx = StrategySearch::top();
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_builtin_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(result),
            ));
        }
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_known_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(result),
            ));
        }
        Ok(None)
    }

    // Top-level equality strategy entry.
    pub fn verify_by_strategy_equal(
        &mut self,
        fact: &crate::ast::fact::EqualFact,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        let ctx = StrategySearch::top();
        if let Some(result) = self.search_equal_fact_proof_by_builtin_strategy(fact, ctx)? {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }
        Ok(None)
    }

    // Strategy-subtree fact proof: WD, then known, then nested strategy.
    pub(crate) fn verify_fact_in_strategy(
        &mut self,
        fact: &Fact,
        ctx: StrategySearch,
    ) -> RuntimeResult<VerifyFactResult> {
        match fact {
            Fact::AtomicFact(atomic) => self.verify_atomic_fact_in_strategy(atomic, ctx),
            // Rare non-atomic strategy requirements: known-only top-level verify.
            _ => self.verify_fact(fact, VerifyState::strategy_wd()),
        }
    }

    fn verify_atomic_fact_in_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<VerifyFactResult> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_in_strategy(equal_fact, ctx)
            }
            _ => self.verify_atomic_except_equality_in_strategy(fact, ctx),
        }
    }

    fn verify_atomic_except_equality_in_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<VerifyFactResult> {
        // WD only (nested fn apps need domain checks). Truth search stays
        // known / cite-only / nested strategy — not premise-producing bt rules.
        let wd_state = VerifyState::top_level().without_well_defined_storage();
        let well_defined_proof = match self
            .verify_atomic_fact_well_definedness(fact, wd_state)?
        {
            VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
            VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                return Ok(atomic_except_equality_fact_result_from_wd_fail(reason));
            }
        };
        match self.search_atomic_except_equality_in_strategy(fact, ctx)? {
            Some(searched_proof) => Ok(atomic_except_equality_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(atomic_except_equality_fact_result_from_search_fail(
                fact,
                well_defined_proof,
            )),
        }
    }

    fn search_atomic_except_equality_in_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        let cite_state = VerifyState::strategy_wd();
        // Cite-only / zero-premise builtin arms (can_use_builtin_rule_round=0).
        // E.g. N+ membership lifts to Z without opening a premise-producing rule.
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_builtin_rule(fact, cite_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                result,
            )));
        }
        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_known_atomic_fact(
            fact,
            cite_state,
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(result),
            ));
        }
        // Depth already accounts for this layer via verify_strategy_requirements'
        // after_layer. At 0, only known (+ cite-only builtin) is allowed.
        if !ctx.can_use_strategy() {
            return Ok(None);
        }
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_builtin_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(result),
            ));
        }
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_known_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(result),
            ));
        }
        Ok(None)
    }

    fn verify_equal_fact_in_strategy(
        &mut self,
        fact: &crate::ast::fact::EqualFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<VerifyFactResult> {
        let wd_state = VerifyState::top_level().without_well_defined_storage();
        let well_defined_proof =
            match self.verify_equal_fact_well_definedness(fact, wd_state)? {
                VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                VerifyEqualFactWellDefinedResult::Failed(reason) => {
                    return Ok(equal_fact_result_from_wd_fail(reason));
                }
            };
        match self.search_equal_fact_in_strategy(fact, ctx)? {
            Some(searched_proof) => Ok(equal_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(equal_fact_result_from_search_fail(fact, well_defined_proof)),
        }
    }

    fn search_equal_fact_in_strategy(
        &mut self,
        fact: &crate::ast::fact::EqualFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        // Same-object evidence is available independently of strategy depth
        // and builtin fuel, just as at the ordinary equality entry.
        if let Some(proof) = search_equal_fact_proof_by_they_are_the_same(fact) {
            return Ok(Some(proof.into()));
        }
        let cite_state = VerifyState::strategy_wd();
        // Cite-only / calculation equality arms under can_use_builtin_rule_round=0.
        if let Some(result) = self.search_equal_fact_builtin_rule(fact, cite_state.clone())? {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinRule(result)));
        }
        if let Some(result) = self
            .search_equal_fact_proof_by_equivalence_class(fact, cite_state)?
        {
            return Ok(Some(EqualFactSearchedProof::ByEquivalenceClass(result)));
        }
        if !ctx.can_use_strategy() {
            return Ok(None);
        }
        if let Some(result) = self.search_equal_fact_proof_by_builtin_strategy(fact, ctx)? {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }
        Ok(None)
    }
}
