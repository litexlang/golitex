//! Source-direction helpers confined to the exp/ln builtin leaves.
use crate::ast::fact::{Fact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn exp_ln_strict_source_order(
        &mut self,
        left: &Obj,
        right: &Obj,
        target: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: target.line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&premise, state)?;
        if !proof.is_failed() {
            return Ok(Some(proof));
        }
        // Keep the actual reverse-written fact and citation, without requesting
        // a builtin direction conversion below the parent premise ceiling.
        let reverse: Fact = GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: right.clone(),
            right: left.clone(),
            line_file: target.line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }

    pub(super) fn exp_ln_weak_source_order(
        &mut self,
        left: &Obj,
        right: &Obj,
        target: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: target.line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&premise, state)?;
        if !proof.is_failed() {
            return Ok(Some(proof));
        }
        // Keep the actual reverse-written fact and citation, without requesting
        // a builtin direction conversion below the parent premise ceiling.
        let reverse: Fact = GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: right.clone(),
            right: left.clone(),
            line_file: target.line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }
}
