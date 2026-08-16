use super::registered_local_builtin_rules;
use crate::prelude::*;
use crate::verify::rule_schema::{match_conclusion, MatchLimits, RuleSourceRef};
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn try_verify_atomic_fact_with_local_builtin_catalog(
        &mut self,
        goal: &AtomicFact,
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
            for template in rule
                .schema()
                .parameter_requirements
                .iter()
                .chain(rule.schema().premises.iter())
            {
                let instantiated = self.inst_atomic_fact(
                    template,
                    &param_to_arg_map,
                    ParamObjType::Forall,
                    Some(&goal_line_file),
                )?;
                // Deliberately restricted: a local schema may cite an already
                // known atomic fact. It cannot recurse into another builtin,
                // computation, resolve, definition unfolding, or a strategy.
                let result = match &instantiated {
                    AtomicFact::EqualFact(equal_fact) => {
                        self.verify_equal_fact_with_known_fact(equal_fact)
                    }
                    _ => self.verify_non_equational_atomic_fact_with_known_fact(&instantiated)?,
                };
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
