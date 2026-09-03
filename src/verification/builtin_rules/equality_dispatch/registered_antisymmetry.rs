//! Equality from registered antisymmetric predicates.

use crate::prelude::*;

impl Runtime {
    // Antisymmetry rule for registered user-defined props.
    // Example: from `$p(a, b)` and `$p(b, a)`, prove `a = b`.
    pub(super) fn try_verify_equality_from_known_antisymmetric_props(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let mut prop_names: Vec<String> = Vec::new();
        for env in self.iter_environments_from_top() {
            for (prop_name, properties) in env
                .predicate_algebraic_properties
                .properties_by_predicate
                .iter()
            {
                if !properties.is_antisymmetric {
                    continue;
                }
                if !prop_names.iter().any(|name| name == prop_name) {
                    prop_names.push(prop_name.clone());
                }
            }
        }

        for prop_name in prop_names {
            let Some(left_to_right) =
                self.verify_user_prop_subgoal(&prop_name, equal_fact, builtin_state)?
            else {
                continue;
            };
            let Some(right_to_left) = self.verify_user_prop_subgoal(
                &prop_name,
                &EqualFact::new_from_refs(right, left, line_file.clone()),
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(Self::wrap_registered_antisymmetric_predicate_result(
                equal_fact,
                prop_name,
                left_to_right,
                right_to_left,
            )));
        }

        Ok(None)
    }

    /// `Combine`: retain the two successful premise Results in theorem
    /// argument order and add only the antisymmetry application owned by this
    /// verifier layer.
    pub(super) fn wrap_registered_antisymmetric_predicate_result(
        equal_fact: &EqualFact,
        prop_name: String,
        left_to_right: VerifyFactResult,
        right_to_left: VerifyFactResult,
    ) -> ProveFactResult {
        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            equal_fact.clone().into(),
            format!(
                "equality from registered antisymmetric prop `{}`",
                prop_name
            ),
            BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(
                RegisteredAntisymmetricPredicateBuiltinRuleEvidence::new(
                    equal_fact.clone().into(),
                    prop_name,
                ),
            ),
            vec![left_to_right, right_to_left],
        )
        .into()
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/verification/builtin_rules/equality_dispatch/registered_antisymmetric_predicate_result_tests.rs"]
mod registered_antisymmetric_predicate_result_tests;
