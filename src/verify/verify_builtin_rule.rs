use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
};

impl Runtime {
    pub(crate) fn verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let leaf_result = self.verify_builtin_rule_leaf(goal)?;
        if leaf_result.is_true() {
            return Ok(leaf_result);
        }

        let builtin_state = UseBuiltinRuleVerifyState::new();
        self.verify_atomic_fact_with_one_builtin_rule(goal, &builtin_state)
    }

    pub(crate) fn verify_builtin_rule_leaf(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_known_non_forall_atomic_fact(goal)?;
        if known_result.is_true() {
            return Ok(known_result);
        }
        Ok(self
            .verify_atomic_fact_by_builtin_computation(goal)
            .filter(StmtResult::is_true)
            .unwrap_or_else(|| StmtUnknown::new().into()))
    }

    pub(crate) fn verify_known_non_forall_atomic_fact(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        match goal {
            AtomicFact::EqualFact(fact) => Ok(self.verify_objs_are_equal_known_only(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
            )),
            _ => self.verify_non_equational_atomic_fact_with_known_atomic_facts(goal),
        }
    }

    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        child: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let leaf_result = self.verify_builtin_rule_leaf(child)?;
        if leaf_result.is_true() {
            return Ok(leaf_result);
        }
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        self.verify_atomic_fact_with_one_builtin_rule(child, builtin_state)
    }

    fn verify_atomic_fact_by_builtin_computation(&self, fact: &AtomicFact) -> Option<StmtResult> {
        match fact {
            AtomicFact::InFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return None;
                };
                let number = fact
                    .element
                    .evaluate_to_normalized_decimal_number()
                    .or_else(|| match self.resolve_obj(&fact.element) {
                        Obj::Number(number) => Some(number),
                        _ => None,
                    })?;
                Some(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                    fact, &number, set,
                ))
            }
            AtomicFact::NotInFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return None;
                };
                let number = fact
                    .element
                    .evaluate_to_normalized_decimal_number()
                    .or_else(|| match self.resolve_obj(&fact.element) {
                        Obj::Number(number) => Some(number),
                        _ => None,
                    })?;
                Some(
                    builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                        fact, &number, set,
                    ),
                )
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                (self.verify_number_comparison_builtin_rule(fact) == Some(true)).then(|| {
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        fact.clone().into(),
                        "number comparison".to_string(),
                        Vec::new(),
                    )
                    .into()
                })
            }
            AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_) => {
                self.verify_prime_fact_by_computation(fact)
            }
            _ => None,
        }
    }

    pub(crate) fn verify_builtin_rule_premises(
        &mut self,
        children: &[AtomicFact],
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut results = Vec::with_capacity(children.len());
        for child in children {
            let result = self.verify_builtin_rule_premise(child, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(results))
    }

    fn verify_atomic_fact_with_builtin_rules_inner(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match goal {
            AtomicFact::EqualFact(fact) => self.verify_equality_by_builtin_rules(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
                builtin_state,
            ),
            _ => {
                self.verify_non_equational_atomic_fact_with_builtin_rules_inner(goal, builtin_state)
            }
        }
    }

    fn verify_atomic_fact_with_one_builtin_rule(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        let child_state = builtin_state.after_applying_builtin_rule();
        self.verify_atomic_fact_with_builtin_rules_inner(goal, &child_state)
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    #[test]
    fn raw_builtin_dispatch_has_only_the_single_rule_entry_point() {
        let source = include_str!("verify_builtin_rule.rs");
        let full_verify_state_constructor = ["UseContextVerifyState", "::new("].concat();
        let raw_dispatch = ["verify_atomic_fact_with_builtin_rules_", "inner("].concat();
        let creates_full_verify_state =
            source
                .match_indices(&full_verify_state_constructor)
                .any(|(index, _)| {
                    source[..index]
                        .chars()
                        .next_back()
                        .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
                });
        assert!(!creates_full_verify_state);
        assert_eq!(
            source.matches(&raw_dispatch).count(),
            2,
            "the raw dispatcher must only be defined once and called by the one-rule entry point"
        );
    }

    #[test]
    fn automatic_builtin_rule_files_do_not_create_fresh_roots_or_bypass_the_limited_entry() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/verify/verify_builtin_rules");
        visit_rust_files(&dir, &mut |path, source| {
            assert!(
                !source.contains("BuiltinRuleVerifyState::new"),
                "{} creates a fresh recursive builtin root",
                path.display()
            );
            assert!(
                !source.contains("verify_atomic_fact_with_builtin_rules("),
                "{} bypasses the depth-limited builtin premise entry point",
                path.display()
            );
        });
    }

    fn visit_rust_files(dir: &Path, f: &mut impl FnMut(&Path, &str)) {
        for entry in fs::read_dir(dir).expect("read builtin rule source directory") {
            let path = entry.expect("read builtin rule directory entry").path();
            if path.is_dir() {
                visit_rust_files(&path, f);
            } else if path.extension().and_then(|value| value.to_str()) == Some("rs") {
                let source = fs::read_to_string(&path).expect("read builtin rule source file");
                f(&path, &source);
            }
        }
    }
}
