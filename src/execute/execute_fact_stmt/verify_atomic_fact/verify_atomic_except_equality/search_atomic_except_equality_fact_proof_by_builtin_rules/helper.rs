//! Actual source-direction evidence for elementary function order builtin leaves.
use crate::ast::fact::{Fact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact};
use crate::ast::obj::Obj;
use crate::ast::line_file::SourceLine;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn strict_order_premise(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: line_file.clone(),
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
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }

    pub(super) fn weak_order_premise(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: Option<SourceLine>,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let premise: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: line_file.clone(),
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
            line_file: line_file.clone(),
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(proof))
    }
}
