use super::by_builtin_rewrite_result::ClosedNumericEqualSubstitutionBuiltinRewriteProof;
use super::helper::replace_obj_matching_ir;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::ClosedNumericExpr;
use crate::runtime::runtime_ids::FactId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashSet;

impl Runtime {
    // Builtin rewrite: substitute known_closed_numeric_equal representatives into the goal.
    // Mathematical property / examples: see ClosedNumericEqualSubstitutionBuiltinRewriteProof.
    //
    // All visible closed-numeric hits that appear as subterms are applied in
    // one shot (cite every used FactId), so `a + b = 30` works after
    // `have a R = 10` and `have b R = 20`.
    //
    // Each stored representative is re-classified as ClosedNumericExpr at
    // the boundary (skip corrupt / non-closed payloads).
    pub fn search_equal_fact_by_closed_numeric_equal_substitution(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedNumericEqualSubstitutionBuiltinRewriteProof>> {
        let entries = self.visible_closed_numeric_equal_entries();
        let mut rewritten_left = fact.left.clone();
        let mut rewritten_right = fact.right.clone();
        let mut cited_equal_fact_ids = Vec::new();

        for (from_ir, closed, fact_id) in &entries {
            let closed_obj = closed.to_obj();
            let next_left = replace_obj_matching_ir(&rewritten_left, from_ir, &closed_obj);
            let next_right = replace_obj_matching_ir(&rewritten_right, from_ir, &closed_obj);
            if next_left.ir() == rewritten_left.ir() && next_right.ir() == rewritten_right.ir() {
                continue;
            }
            rewritten_left = next_left;
            rewritten_right = next_right;
            cited_equal_fact_ids.push(*fact_id);
        }

        if cited_equal_fact_ids.is_empty() {
            return Ok(None);
        }

        let residual_fact_id = self.global_ids.allocate_fact_id();
        let residual = EqualFact {
            fact_id: residual_fact_id,
            left: rewritten_left.clone(),
            right: rewritten_right.clone(),
            line_file: fact.line_file.clone(),
        };
        let residual_state = VerifyState {
            can_use_builtin_rule_round: verify_state.can_use_builtin_rule_round,
            can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
            can_use_rewrite: false,
            store_well_defined_fact: false,
};
        let residual_equal = self.verify_equal_fact(&residual, residual_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ClosedNumericEqualSubstitutionBuiltinRewriteProof {
            rewritten_left,
            rewritten_right,
            cited_equal_fact_ids,
            residual_equal,
        }))
    }

    // Visible known_closed_numeric_equal rows, with the representative already classified.
    pub(crate) fn visible_closed_numeric_equal_entries(
        &self,
    ) -> Vec<(ObjIR, ClosedNumericExpr, FactId)> {
        let mut seen: HashSet<u64> = HashSet::new();
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (key, entries) in env.facts.known_closed_numeric_equal.iter() {
                for (closed, fact_id) in entries {
                    let id = fact_id.value();
                    let Some(closed_expr) = ClosedNumericExpr::try_from_obj(closed) else {
                        continue;
                    };
                    if seen.insert(id) {
                        out.push((key.clone(), closed_expr, *fact_id));
                    }
                }
            }
        }
        out
    }

    // One-shot closed-numeric index substitution on a single object (eval / rewrite).
    // Example: after `have a R = 10`, `a + 1` → `(10 + 1, [fact_id])`.
    pub(crate) fn rewrite_obj_by_known_closed_numeric_equal(
        &self,
        obj: &Obj,
    ) -> (Obj, Vec<FactId>) {
        let entries = self.visible_closed_numeric_equal_entries();
        let mut rewritten = obj.clone();
        let mut cited = Vec::new();
        for (from_ir, closed, fact_id) in &entries {
            let closed_obj = closed.to_obj();
            let next = replace_obj_matching_ir(&rewritten, from_ir, &closed_obj);
            if next.ir() == rewritten.ir() {
                continue;
            }
            rewritten = next;
            cited.push(*fact_id);
        }
        (rewritten, cited)
    }
}
