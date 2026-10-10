use super::by_object_definition::by_fn_application::normalize_function_body::{
    AnonymousFunctionBodyExpansionProof, FunctionBodySourceProof,
};
use super::fn_application_unfold_substitution_builtin_rewrite_proof::FnApplicationUnfoldSubstitutionBuiltinRewriteProof;
use crate::prelude::*;

impl Runtime {
    // If f equals a checked anonymous function, substitute its body once under
    // scalar constructors. Example: f(t)=t+1 gives 2*f(x)=2+2*x directly.
    // The caller has checked endpoint WD and consumed the fallback permission.
    // Only original outermost calls unfold; arguments and inserted bodies stay
    // opaque to this pass. Keep the selected body's own carrier/guard checks.
    // The head equality may be a forall premise; no have-fn definition is needed.
    pub fn search_equal_fact_by_fn_application_unfold_substitution(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FnApplicationUnfoldSubstitutionBuiltinRewriteProof>> {
        // Preserve explicit beta endpoints: if one side alone becomes the
        // existing opposite side, leave that opposite expression untouched.
        let left_preview = preview_fn_equal_to_anonymous_function_subterms(self, &fact.left)?;
        let right_preview = preview_fn_equal_to_anonymous_function_subterms(self, &fact.right)?;
        let left_only = left_preview.ir() == fact.right.ir();
        let right_only = !left_only && right_preview.ir() == fact.left.ir();
        let mut expansions = Vec::new();
        let rewritten_left = if right_only {
            fact.left.clone()
        } else {
            rewrite_fn_equal_to_anonymous_function_subterms(
                self,
                &fact.left,
                verify_state,
                &mut expansions,
            )?
        };
        let rewritten_right = if left_only {
            fact.right.clone()
        } else {
            rewrite_fn_equal_to_anonymous_function_subterms(
                self,
                &fact.right,
                verify_state,
                &mut expansions,
            )?
        };
        if expansions.is_empty() {
            return Ok(None);
        }
        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: rewritten_left.clone(),
            right: rewritten_right.clone(),
            line_file: fact.line_file.clone(),
        };
        // Finish with bounded algebraic search, without another definition or
        // rewrite round. One-layer expansion can still produce a large tree.
        let residual_equal = self.verify_equal_fact(
            &residual,
            verify_state.capped_at(VerifyStateLevel::Strategy),
        )?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            FnApplicationUnfoldSubstitutionBuiltinRewriteProof::new(
                expansions,
                rewritten_left,
                rewritten_right,
                residual_equal,
            ),
        ))
    }
}

fn rewrite_fn_equal_to_anonymous_function_subterms(
    runtime: &mut Runtime,
    obj: &Obj,
    state: VerifyState,
    expansions: &mut Vec<AnonymousFunctionBodyExpansionProof>,
) -> RuntimeResult<Obj> {
    // Collect from the untouched tree so neither a replacement nor its
    // arguments can enter the same rewrite pass.
    let mut calls = Vec::new();
    super::helper::replace_scalar_subterms(obj, &mut |part, rebuilt| {
        if !rebuilt {
            if let Obj::FnObj(call) = part {
                calls.push(call.clone());
            }
        }
        None
    });
    let first = expansions.len();
    for call in calls {
        if call.body.len() != 1 {
            continue;
        }
        let head = super::helper::fn_obj_prefix_obj(&call, 0);
        let mut candidates = Vec::new();
        for (value, path) in runtime.exact_property_object_values(&head) {
            if path.len() != 1 {
                continue;
            }
            if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = value {
                candidates.push((
                    function,
                    FunctionBodySourceProof::KnownEquality(KnownEqualityPathProof::new(path)),
                ));
            }
        }
        if let Some(proof) =
            runtime.checked_anonymous_function_body_expansion(&call, state, None, candidates)?
        {
            if proof.expanded_body.ir() != proof.application.ir() {
                expansions.push(proof);
            }
        }
    }
    let mut next = first;
    Ok(super::helper::replace_scalar_subterms(
        obj,
        &mut |part, rebuilt| {
            if rebuilt {
                return None;
            }
            let step = expansions.get(next)?;
            if part.ir() != step.application.ir() {
                return None;
            }
            next += 1;
            Some(step.expanded_body.clone())
        },
    ))
}

fn preview_fn_equal_to_anonymous_function_subterms(
    runtime: &mut Runtime,
    obj: &Obj,
) -> RuntimeResult<Obj> {
    let mut calls = Vec::new();
    super::helper::replace_scalar_subterms(obj, &mut |part, rebuilt| {
        if !rebuilt {
            if let Obj::FnObj(call) = part {
                calls.push(call.clone());
            }
        }
        None
    });
    let mut replacements = Vec::new();
    for call in calls {
        if let Some(body) = runtime.expanded_named_or_literal_anon_fn_application_body(&call)? {
            if body.function_equal.path.len() != 1 {
                continue;
            }
            replacements.push((Obj::FnObj(call), body.expanded_body));
        }
    }
    let mut next = 0;
    Ok(super::helper::replace_scalar_subterms(
        obj,
        &mut |part, rebuilt| {
            if rebuilt {
                return None;
            }
            let (call, body) = replacements.get(next)?;
            if part.ir() != call.ir() {
                return None;
            }
            next += 1;
            Some(body.clone())
        },
    ))
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/fn_application_unfold_substitution/tests.rs"]
mod fn_application_unfold_substitution_tests;
