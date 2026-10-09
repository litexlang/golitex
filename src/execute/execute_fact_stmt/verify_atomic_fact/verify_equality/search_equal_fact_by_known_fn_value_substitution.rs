use crate::prelude::*;

impl Runtime {
    // Substitute available direct function-value equations under scalar
    // constructors, then check the residual without another rewrite/unfold.
    // Example: f(x)=x+3 makes 2*f(x)=2*x+6 a single checked equality.
    pub fn search_equal_fact_by_known_fn_value_substitution(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<super::known_fn_value_substitution_builtin_rewrite_proof::KnownFnValueSubstitutionBuiltinRewriteProof>>{
        let mut cited_equal_fact_ids = Vec::new();
        let rewritten_left =
            rewrite_known_fn_value_subterms(self, &fact.left, &mut cited_equal_fact_ids);
        let rewritten_right =
            rewrite_known_fn_value_subterms(self, &fact.right, &mut cited_equal_fact_ids);
        if cited_equal_fact_ids.is_empty() {
            return Ok(None);
        }

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: rewritten_left.clone(),
            right: rewritten_right.clone(),
            line_file: fact.line_file.clone(),
        };
        let residual_equal = self.verify_equal_fact(
            &residual,
            verify_state.capped_at(VerifyStateLevel::Strategy),
        )?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            super::known_fn_value_substitution_builtin_rewrite_proof::KnownFnValueSubstitutionBuiltinRewriteProof::new(
                rewritten_left,
                rewritten_right,
                cited_equal_fact_ids,
                residual_equal,
            ),
        ))
    }
}

fn rewrite_known_fn_value_subterms(
    runtime: &Runtime,
    obj: &Obj,
    cited_equal_fact_ids: &mut Vec<FactId>,
) -> Obj {
    super::helper::replace_scalar_subterms(obj, &mut |part, rebuilt| {
        if rebuilt || !matches!(part, Obj::FnObj(_)) {
            return None;
        }
        let mut selected = None;
        for (value, path) in runtime.exact_property_object_values(part) {
            if path.len() != 1 || value.ir() == part.ir() {
                continue;
            }
            // The exact-property reader deduplicates endpoints. Several
            // different values are an author choice, not a search product.
            if selected.is_some() {
                return None;
            }
            selected = Some((value, path[0].2));
        }
        let (value, fact_id) = selected?;
        if !cited_equal_fact_ids.contains(&fact_id) {
            cited_equal_fact_ids.push(fact_id);
        }
        Some(value)
    })
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/known_fn_value_substitution/tests.rs"]
mod known_fn_value_substitution_tests;
