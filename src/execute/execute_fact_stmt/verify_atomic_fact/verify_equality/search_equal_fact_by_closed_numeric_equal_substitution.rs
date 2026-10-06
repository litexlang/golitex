use super::by_builtin_rewrite_result::ClosedNumericEqualSubstitutionBuiltinRewriteProof;
use super::helper::replace_scalar_subterms;
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
        let (rewritten_left, mut cited_equal_fact_ids) =
            rewrite_closed_numeric_subterms(&fact.left, &entries);
        let (rewritten_right, right_citations) =
            rewrite_closed_numeric_subterms(&fact.right, &entries);
        for id in right_citations {
            if !cited_equal_fact_ids.contains(&id) {
                cited_equal_fact_ids.push(id);
            }
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
        let residual_state = verify_state.without_rewrite();
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
        rewrite_closed_numeric_subterms(obj, &entries)
    }
}

// Apply the closed numeric index simultaneously to original scalar subterms.
// Prefer a stored numeral when one exists; rows for one key retain their
// existing visibility order. Every selected equality is cited. In particular,
// with a=0 and cos(a)=1, replace the whole cos(a), not its argument first.
pub(crate) fn rewrite_closed_numeric_subterms(
    obj: &Obj,
    entries: &[(ObjIR, ClosedNumericExpr, FactId)],
) -> (Obj, Vec<FactId>) {
    let mut cited = Vec::new();
    let rewritten = replace_scalar_subterms(obj, &mut |part, _| {
        let ir = part.ir();
        let selected = entries.iter().find(|(from, value, _)| {
            from == &ir && matches!(value, ClosedNumericExpr::Number(_))
        }).or_else(|| entries.iter().find(|(from, _, _)| from == &ir));
        let (_, value, id) = selected?;
        let value = value.to_obj();
        if value.ir() == ir {
            return None;
        }
        if !cited.contains(id) {
            cited.push(*id);
        }
        Some(value)
    });
    (rewritten, cited)
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/closed_numeric_subterm_priority/tests.rs"]
mod closed_numeric_subterm_priority_tests;
