use crate::prelude::*;

impl Runtime {
    // A surjective image of a finite source is finite.
    // Example: finite A and `$surjective(A, B, f)` imply `$is_finite_set(B)`.
    pub(super) fn try_verify_finite_codomain_from_known_surjection(
        &mut self,
        target: &IsFiniteSetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for property in self.known_function_property_facts(&[SURJECTIVE, BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let codomain_match = self.verify_objs_are_equal_known_only(
                &codomain,
                &target.set,
                target.line_file.clone(),
            );
            if !codomain_match.is_true() {
                continue;
            }

            let domain_finite: AtomicFact =
                IsFiniteSetFact::new(domain, target.line_file.clone()).into();
            let domain_result = self.verify_non_equational_known_then_builtin_rules_only(
                &domain_finite,
                &verify_state.make_final_round_state(),
            )?;
            if !domain_result.is_true() {
                continue;
            }
            let property_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &property.clone().into(),
            )?;
            if !property_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    target.clone().into(),
                    "finite codomain of a surjection from a finite set".to_string(),
                    vec![codomain_match, domain_result, property_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // An injection from a finite source preserves cardinality onto its range.
    // Example: finite A and `$injective(A, B, f)` imply
    // `finite_set_size(fn_range(f)) = finite_set_size(A)`.
    pub(super) fn try_verify_finite_set_size_fn_range_from_known_injection(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((function, source)) = finite_fn_range_size_equality_shape(left, right)
            .or_else(|| finite_fn_range_size_equality_shape(right, left))
        else {
            return Ok(None);
        };

        for property in self.known_function_property_facts(&[INJECTIVE, BIJECTIVE]) {
            let Some((domain, _, candidate_function)) = function_property_parts(&property) else {
                continue;
            };
            let domain_match =
                self.verify_objs_are_equal_known_only(&domain, &source, line_file.clone());
            let function_match = self.verify_objs_are_equal_known_only(
                &candidate_function,
                &function,
                line_file.clone(),
            );
            if !domain_match.is_true() || !function_match.is_true() {
                continue;
            }

            let domain_finite: AtomicFact = IsFiniteSetFact::new(domain, line_file.clone()).into();
            let finite_result = self.verify_non_equational_known_then_builtin_rules_only(
                &domain_finite,
                verify_state,
            )?;
            if !finite_result.is_true() {
                continue;
            }
            let property_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &property.clone().into(),
            )?;
            if !property_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "finite injection has range cardinality equal to its source".to_string(),
                    vec![domain_match, function_match, finite_result, property_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // A bijection from a finite source preserves the source and codomain cardinalities.
    // Example: finite A and `$bijective(A, B, f)` imply
    // `finite_set_size(A) = finite_set_size(B)`.
    pub(super) fn try_verify_finite_set_size_from_known_bijection(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::FiniteSetSize(left_size), Obj::FiniteSetSize(right_size)) = (left, right) else {
            return Ok(None);
        };

        for property in self.known_function_property_facts(&[BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let direct_domain = self.verify_objs_are_equal_known_only(
                &domain,
                left_size.set.as_ref(),
                line_file.clone(),
            );
            let direct_codomain = self.verify_objs_are_equal_known_only(
                &codomain,
                right_size.set.as_ref(),
                line_file.clone(),
            );
            let reverse_domain = self.verify_objs_are_equal_known_only(
                &domain,
                right_size.set.as_ref(),
                line_file.clone(),
            );
            let reverse_codomain = self.verify_objs_are_equal_known_only(
                &codomain,
                left_size.set.as_ref(),
                line_file.clone(),
            );
            let (domain_match, codomain_match) =
                if direct_domain.is_true() && direct_codomain.is_true() {
                    (direct_domain, direct_codomain)
                } else if reverse_domain.is_true() && reverse_codomain.is_true() {
                    (reverse_domain, reverse_codomain)
                } else {
                    continue;
                };

            let domain_finite: AtomicFact = IsFiniteSetFact::new(domain, line_file.clone()).into();
            let finite_result = self.verify_non_equational_known_then_builtin_rules_only(
                &domain_finite,
                verify_state,
            )?;
            if !finite_result.is_true() {
                continue;
            }
            let property_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &property.clone().into(),
            )?;
            if !property_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "finite bijection preserves cardinality".to_string(),
                    vec![domain_match, codomain_match, finite_result, property_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // A surjection from a finite source cannot have a larger codomain.
    // Example: finite A and `$surjective(A, B, f)` imply
    // `finite_set_size(B) <= finite_set_size(A)`.
    pub(super) fn try_verify_finite_set_size_codomain_le_domain_from_known_surjection(
        &mut self,
        target: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((smaller, larger, line_file)) = ordered_finite_set_sizes(target) else {
            return Ok(None);
        };

        for property in self.known_function_property_facts(&[SURJECTIVE, BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let codomain_match =
                self.verify_objs_are_equal_known_only(&codomain, &smaller, line_file.clone());
            let domain_match =
                self.verify_objs_are_equal_known_only(&domain, &larger, line_file.clone());
            if !codomain_match.is_true() || !domain_match.is_true() {
                continue;
            }

            let domain_finite: AtomicFact = IsFiniteSetFact::new(domain, line_file.clone()).into();
            let finite_result = self.verify_non_equational_known_then_builtin_rules_only(
                &domain_finite,
                verify_state,
            )?;
            if !finite_result.is_true() {
                continue;
            }
            let property_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &property.clone().into(),
            )?;
            if !property_result.is_true() {
                continue;
            }

            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    target.clone().into(),
                    "finite surjection bounds codomain cardinality by source cardinality"
                        .to_string(),
                    vec![codomain_match, domain_match, finite_result, property_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // Consumers that need a bijection may match the builtin fact directly.
    // Example: `$bijective(I, X, g)` justifies reindexing a finite sum along `g`.
    pub(super) fn has_known_builtin_bijection(
        &self,
        domain: &Obj,
        codomain: &Obj,
        function: &Obj,
        line_file: LineFile,
    ) -> bool {
        for property in self.known_function_property_facts(&[BIJECTIVE]) {
            let Some((candidate_domain, candidate_codomain, candidate_function)) =
                function_property_parts(&property)
            else {
                continue;
            };
            let domain_match =
                self.verify_objs_are_equal_known_only(&candidate_domain, domain, line_file.clone());
            let codomain_match = self.verify_objs_are_equal_known_only(
                &candidate_codomain,
                codomain,
                line_file.clone(),
            );
            let function_match = self.verify_objs_are_equal_known_only(
                &candidate_function,
                function,
                line_file.clone(),
            );
            if domain_match.is_true() && codomain_match.is_true() && function_match.is_true() {
                return true;
            }
        }
        false
    }

    fn known_function_property_facts(&self, predicates: &[&str]) -> Vec<NormalAtomicFact> {
        let mut facts = Vec::new();
        for predicate in predicates {
            let key = ((*predicate).to_string(), true);
            for environment in self.iter_environments_from_top() {
                let Some(known) = environment
                    .known_atomic_facts_with_0_or_more_than_2_args
                    .get(&key)
                else {
                    continue;
                };
                for fact in known {
                    if let AtomicFact::NormalAtomicFact(fact) = fact {
                        facts.push(fact.clone());
                    }
                }
            }
        }
        facts.sort_by_key(|fact| fact.to_string());
        facts.dedup_by(|left, right| left.to_string() == right.to_string());
        facts
    }
}

fn function_property_parts(fact: &NormalAtomicFact) -> Option<(Obj, Obj, Obj)> {
    if fact.body.len() != 3 {
        return None;
    }
    Some((
        fact.body[0].clone(),
        fact.body[1].clone(),
        fact.body[2].clone(),
    ))
}

fn finite_fn_range_size_equality_shape(
    range_size_side: &Obj,
    source_size_side: &Obj,
) -> Option<(Obj, Obj)> {
    let Obj::FiniteSetSize(range_size) = range_size_side else {
        return None;
    };
    let Obj::FnRange(range) = range_size.set.as_ref() else {
        return None;
    };
    let Obj::FiniteSetSize(source_size) = source_size_side else {
        return None;
    };
    Some((
        range.function.as_ref().clone(),
        source_size.set.as_ref().clone(),
    ))
}

fn ordered_finite_set_sizes(target: &AtomicFact) -> Option<(Obj, Obj, LineFile)> {
    let (smaller, larger, line_file) = match target {
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, fact.line_file.clone()),
        AtomicFact::GreaterEqualFact(fact) => (&fact.right, &fact.left, fact.line_file.clone()),
        _ => return None,
    };
    let Obj::FiniteSetSize(smaller_size) = smaller else {
        return None;
    };
    let Obj::FiniteSetSize(larger_size) = larger else {
        return None;
    };
    Some((
        smaller_size.set.as_ref().clone(),
        larger_size.set.as_ref().clone(),
        line_file,
    ))
}
