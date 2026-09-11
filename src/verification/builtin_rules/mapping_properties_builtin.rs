use crate::prelude::*;

impl Runtime {
    // A surjective image of a finite source is finite.
    // Example: finite A and `$surjective(A, B, f)` imply `$is_finite_set(B)`.
    pub(super) fn try_verify_finite_codomain_from_known_surjection(
        &mut self,
        target: &IsFiniteSetFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        for property in self.known_function_property_facts(&[SURJECTIVE, BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let Some(codomain_match) = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&codomain, &target.set, target.line_file.clone()),
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };

            let domain_finite: AtomicFact = self
                .new_is_finite_set_fact(domain, target.line_file.clone())
                .into();
            let Some(domain_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&domain_finite, builtin_state)?
            else {
                continue;
            };
            let Some(property_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &property.clone().into(),
                builtin_state,
            )?
            else {
                continue;
            };

            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target.clone().into(),
                    "finite codomain of a surjection from a finite set".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyFiniteCodomainFromKnownSurjection,
                    ),
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
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some((function, source)) = finite_fn_range_size_equality_shape(equal_fact) else {
            return Ok(None);
        };
        let line_file = &equal_fact.line_file;

        for property in self.known_function_property_facts(&[INJECTIVE, BIJECTIVE]) {
            let Some((domain, _, candidate_function)) = function_property_parts(&property) else {
                continue;
            };
            let Some(domain_match) = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&domain, &source, line_file.clone()),
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };
            let Some(function_match) = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&candidate_function, &function, line_file.clone()),
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };

            let domain_finite: AtomicFact = self
                .new_is_finite_set_fact(domain, line_file.clone())
                .into();
            let Some(finite_result) = self.try_verify_known_or_structurally_finite_set_candidate(
                &domain_finite,
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };
            let Some(property_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &property.clone().into(),
                builtin_state,
            )?
            else {
                continue;
            };

            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "finite injection has range cardinality equal to its source".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyFiniteSetSizeFnRangeFromKnownInjection,
                    ),
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
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (Obj::FiniteSetSize(left_size), Obj::FiniteSetSize(right_size)) =
            (&equal_fact.left, &equal_fact.right)
        else {
            return Ok(None);
        };
        let line_file = &equal_fact.line_file;

        for property in self.known_function_property_facts(&[BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let direct_domain = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&domain, left_size.set.as_ref(), line_file.clone()),
                builtin_state.verify_state(),
            )?;
            let direct_codomain = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(
                    &codomain,
                    right_size.set.as_ref(),
                    line_file.clone(),
                ),
                builtin_state.verify_state(),
            )?;
            let reverse_domain = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&domain, right_size.set.as_ref(), line_file.clone()),
                builtin_state.verify_state(),
            )?;
            let reverse_codomain = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(
                    &codomain,
                    left_size.set.as_ref(),
                    line_file.clone(),
                ),
                builtin_state.verify_state(),
            )?;
            let (domain_match, codomain_match) = match (
                direct_domain,
                direct_codomain,
                reverse_domain,
                reverse_codomain,
            ) {
                (Some(domain), Some(codomain), _, _) => (domain, codomain),
                (_, _, Some(domain), Some(codomain)) => (domain, codomain),
                _ => continue,
            };

            let domain_finite: AtomicFact = self
                .new_is_finite_set_fact(domain, line_file.clone())
                .into();
            let Some(finite_result) = self.try_verify_known_or_structurally_finite_set_candidate(
                &domain_finite,
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };
            let Some(property_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &property.clone().into(),
                builtin_state,
            )?
            else {
                continue;
            };

            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "finite bijection preserves cardinality".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyFiniteSetSizeFromKnownBijection,
                    ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some((smaller, larger, line_file)) = ordered_finite_set_sizes(target) else {
            return Ok(None);
        };

        for property in self.known_function_property_facts(&[SURJECTIVE, BIJECTIVE]) {
            let Some((domain, codomain, _)) = function_property_parts(&property) else {
                continue;
            };
            let Some(codomain_match) = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&codomain, &smaller, line_file.clone()),
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };
            let Some(domain_match) = self.try_verify_known_equality_fact_candidate(
                &self.new_equal_fact_from_refs(&domain, &larger, line_file.clone()),
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };

            let domain_finite: AtomicFact = self
                .new_is_finite_set_fact(domain, line_file.clone())
                .into();
            let Some(finite_result) = self.try_verify_known_or_structurally_finite_set_candidate(
                &domain_finite,
                builtin_state.verify_state(),
            )?
            else {
                continue;
            };
            let Some(property_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &property.clone().into(),
                builtin_state,
            )?
            else {
                continue;
            };

            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target.clone().into(),
                    "finite surjection bounds codomain cardinality by source cardinality"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyFiniteSetSizeCodomainLeDomainFromKnownSurjection),
                    vec![codomain_match, domain_match, finite_result, property_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    /// Return the exact proof children used to match a stored bijection.
    /// Consumers retain these results instead of dropping the citation and the
    /// three transport equalities.
    pub(super) fn known_builtin_bijection_results(
        &mut self,
        domain: &Obj,
        codomain: &Obj,
        function: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        for property in self.known_function_property_facts(&[BIJECTIVE]) {
            let Some((candidate_domain, candidate_codomain, candidate_function)) =
                function_property_parts(&property)
            else {
                continue;
            };
            // A finite-sequence function retains a restricted function carrier,
            // while the public bijection fact names its extension as a closed
            // range. Use the ordinary checked equality dispatcher here, just as
            // the enumeration-shape recognizer does, so a builtin theorem's
            // witness can feed a builtin sum/product consumer directly.
            let domain_match = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&candidate_domain, domain, line_file.clone()),
                builtin_state,
            )?;
            let codomain_match = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&candidate_codomain, codomain, line_file.clone()),
                builtin_state,
            )?;
            let function_match = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&candidate_function, function, line_file.clone()),
                builtin_state,
            )?;
            if let (Some(domain_match), Some(codomain_match), Some(function_match)) =
                (domain_match, codomain_match, function_match)
            {
                if let Some(property_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &property.clone().into(),
                    builtin_state,
                )? {
                    return Ok(Some(vec![
                        property_result,
                        domain_match,
                        codomain_match,
                        function_match,
                    ]));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_known_or_structurally_finite_set_candidate(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        let known = self.verify_non_equational_atomic_fact_with_known_atomic_facts(fact)?;
        if known.is_success() {
            return self.complete_proven_fact_candidate(fact.clone().into(), known, verify_state);
        }
        let AtomicFact::IsFiniteSetFact(finite) = fact else {
            return Ok(None);
        };
        if !set_is_structurally_finite(&finite.set) {
            return Ok(None);
        }
        let proof =
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                fact.clone().into(),
                "literal/range finite-set structure".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyKnownOrStructurallyFiniteSet,
                ),
                Vec::new(),
            )
            .into();
        self.complete_proven_fact_candidate(fact.clone().into(), proof, verify_state)
    }

    fn known_function_property_facts(&self, predicates: &[&str]) -> Vec<NormalAtomicFact> {
        let mut facts = Vec::new();
        for predicate in predicates {
            let key = ((*predicate).to_string(), true);
            for environment in self.iter_environments_from_top() {
                let Some(known) = environment.facts.atomic.by_other_arg_count.get(&key) else {
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

fn set_is_structurally_finite(set: &Obj) -> bool {
    match set {
        Obj::ListSet(_) | Obj::Range(_) | Obj::ClosedRange(_) => true,
        Obj::Union(union) => {
            set_is_structurally_finite(union.left.as_ref())
                && set_is_structurally_finite(union.right.as_ref())
        }
        _ => false,
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

fn finite_fn_range_size_equality_shape(equal_fact: &EqualFact) -> Option<(Obj, Obj)> {
    for (range_size_side, source_size_side) in [
        (&equal_fact.left, &equal_fact.right),
        (&equal_fact.right, &equal_fact.left),
    ] {
        let Obj::FiniteSetSize(range_size) = range_size_side else {
            continue;
        };
        let Obj::FnRange(range) = range_size.set.as_ref() else {
            continue;
        };
        let Obj::FiniteSetSize(source_size) = source_size_side else {
            continue;
        };
        return Some((
            range.function.as_ref().clone(),
            source_size.set.as_ref().clone(),
        ));
    }
    None
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
