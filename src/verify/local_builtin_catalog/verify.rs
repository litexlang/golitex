use super::registered_local_builtin_rules;
use crate::prelude::*;
use crate::verify::rule_schema::{match_conclusion, MatchLimits, RuleSourceRef};
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn try_verify_atomic_fact_with_local_builtin_catalog(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let mut rules = registered_local_builtin_rules()?;
        rules.sort_by(|left, right| {
            left.schema()
                .premises
                .len()
                .cmp(&right.schema().premises.len())
                .then_with(|| left.id().cmp(right.id()))
        });

        for rule in rules {
            if rule.schema().head_key != crate::verify::rule_schema::atomic_fact_head(goal) {
                continue;
            }
            let Some(substitution) =
                match_conclusion(rule.schema(), goal, MatchLimits::default()).unwrap_or(None)
            else {
                continue;
            };

            let mut param_to_arg_map = HashMap::new();
            for (variable, binding) in rule.schema().variables.iter().zip(substitution.bindings()) {
                insert_symbol_substitution(
                    &mut param_to_arg_map,
                    &variable.binding,
                    binding.clone(),
                );
            }

            let goal_line_file = goal.line_file();
            let mut step_results = Vec::new();
            let mut candidate_failed = false;
            for template in &rule.schema().parameter_requirements {
                let instantiated = self.inst_atomic_fact(
                    template,
                    &param_to_arg_map,
                    ParamObjType::Forall,
                    Some(&goal_line_file),
                )?;
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&instantiated, builtin_state)?;
                if !result.is_true() {
                    candidate_failed = true;
                    break;
                }
                step_results.push(result);
            }
            if candidate_failed {
                continue;
            }

            for template in &rule.schema().premises {
                let instantiated = self.inst_quantifier_free_fact(
                    template,
                    &param_to_arg_map,
                    ParamObjType::Forall,
                    Some(&goal_line_file),
                )?;
                // The local rule has already consumed the one premise-producing builtin step.
                // Compound structure may organize known/directly evaluable leaves, but cannot
                // reset that budget or reopen general proof search.
                let result = self.verify_builtin_rule_premise(&instantiated, builtin_state)?;
                if !result.is_true() {
                    candidate_failed = true;
                    break;
                }
                step_results.push(result);
            }
            if candidate_failed {
                continue;
            }

            let RuleSourceRef::LocalBuiltin {
                rule_id,
                semantic_fingerprint,
            } = &rule.schema().source
            else {
                unreachable!("local catalog returned a non-local schema")
            };
            let evidence = RegisteredLocalBuiltinRuleEvidence {
                rule_id: rule_id.clone(),
                semantic_fingerprint: semantic_fingerprint.clone(),
                bindings: substitution.bindings().to_vec(),
                parameter_requirement_count: rule.schema().parameter_requirements.len(),
            };
            let result = FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_and_steps(
                goal.clone().into(),
                InferResult::new(),
                format!("local builtin {}", rule.id().as_str()),
                BuiltinRuleEvidence::RegisteredLocal(evidence),
                step_results,
            );
            return Ok(Some(result.into()));
        }
        Ok(None)
    }
}
