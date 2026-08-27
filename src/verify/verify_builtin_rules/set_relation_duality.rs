use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(result) =
            self.try_verify_indexed_set_family_algebra_subset(subset_fact, builtin_state)?
        {
            return Ok(result);
        }

        // Fundamental set containments follow directly from membership definitions.
        // Examples: `intersect(A, B) $subset A`, `A $subset union(A, B)`.
        let elementary_set_subset_reason = match (&subset_fact.left, &subset_fact.right) {
            (Obj::Intersect(intersect), right)
                if objs_equal_with_nested_binder_alpha_equivalence(&intersect.left, right)
                    || objs_equal_with_nested_binder_alpha_equivalence(&intersect.right, right) =>
            {
                Some("intersection_subset_operand")
            }
            (left, Obj::Union(union))
                if objs_equal_with_nested_binder_alpha_equivalence(&union.left, left)
                    || objs_equal_with_nested_binder_alpha_equivalence(&union.right, left) =>
            {
                Some("operand_subset_union")
            }
            (Obj::SetMinus(set_minus), right)
                if objs_equal_with_nested_binder_alpha_equivalence(&set_minus.left, right) =>
            {
                Some("set_minus_subset_left_operand")
            }
            _ => None,
        };
        if let Some(reason) = elementary_set_subset_reason {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    reason.to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Binary union is monotone componentwise. This direct leaf is also
        // what lets a checked anonymous family certify
        // `union(C, A(i)) subset union(C, X)` from `A(i) subset X` without
        // adding another builtin hop or weakening its defined return set.
        if let (Obj::Union(left_union), Obj::Union(right_union)) =
            (&subset_fact.left, &subset_fact.right)
        {
            for ((left_first, right_first), (left_second, right_second)) in [
                (
                    (left_union.left.as_ref(), right_union.left.as_ref()),
                    (left_union.right.as_ref(), right_union.right.as_ref()),
                ),
                (
                    (left_union.left.as_ref(), right_union.right.as_ref()),
                    (left_union.right.as_ref(), right_union.left.as_ref()),
                ),
            ] {
                let premises = [(left_first, right_first), (left_second, right_second)]
                    .into_iter()
                    .filter(|(left, right)| {
                        !objs_equal_with_nested_binder_alpha_equivalence(left, right)
                    })
                    .map(|(left, right)| {
                        SubsetFact::new(left.clone(), right.clone(), subset_fact.line_file.clone())
                            .into()
                    })
                    .collect::<Vec<AtomicFact>>();
                if let Some(steps) = self.verify_builtin_rule_premises(&premises, builtin_state)? {
                    return Ok(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "binary union subset from componentwise subsets".to_string(),
                            steps,
                        )
                        .into(),
                    );
                }
            }
        }

        // An intersection is contained in every known upper bound of either
        // operand. This is the one-premise form of the elementary
        // `intersect(A, B) subset A` rule.
        if let Obj::Intersect(intersection) = &subset_fact.left {
            for operand in [intersection.left.as_ref(), intersection.right.as_ref()] {
                let premise: AtomicFact = SubsetFact::new(
                    operand.clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
                if result.is_success() {
                    return Ok(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "intersection subset from an operand upper bound".to_string(),
                            vec![result],
                        )
                        .into(),
                    );
                }
            }
        }

        if let Obj::SetMinus(set_minus) = &subset_fact.left {
            let premise: AtomicFact = SubsetFact::new(
                set_minus.left.as_ref().clone(),
                subset_fact.right.clone(),
                subset_fact.line_file.clone(),
            )
            .into();
            let result =
                self.verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
            if result.is_success() {
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "set difference subset from left-operand upper bound".to_string(),
                        vec![result],
                    )
                    .into(),
                );
            }
        }

        // Power set is monotone: `A subset B` implies
        // `power_set(A) subset power_set(B)`.
        if let (Obj::PowerSet(left_power), Obj::PowerSet(right_power)) =
            (&subset_fact.left, &subset_fact.right)
        {
            let premise: AtomicFact = SubsetFact::new(
                left_power.set.as_ref().clone(),
                right_power.set.as_ref().clone(),
                subset_fact.line_file.clone(),
            )
            .into();
            let result =
                self.verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
            if result.is_success() {
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "power set subset from base-set subset".to_string(),
                        vec![result],
                    )
                    .into(),
                );
            }
        }

        // Removing the same set preserves inclusion on the left operand.
        if let (Obj::SetMinus(left_minus), Obj::SetMinus(right_minus)) =
            (&subset_fact.left, &subset_fact.right)
        {
            if objs_equal_with_nested_binder_alpha_equivalence(
                left_minus.right.as_ref(),
                right_minus.right.as_ref(),
            ) {
                let premise: AtomicFact = SubsetFact::new(
                    left_minus.left.as_ref().clone(),
                    right_minus.left.as_ref().clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
                if result.is_success() {
                    return Ok(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "set difference subset from common-right left subset".to_string(),
                            vec![result],
                        )
                        .into(),
                    );
                }
            }
        }

        // A union is contained in a set when both operands are already known
        // to be contained in it.
        if let Obj::Union(union) = &subset_fact.left {
            let premises: [AtomicFact; 2] = [
                SubsetFact::new(
                    union.left.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into(),
                SubsetFact::new(
                    union.right.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into(),
            ];
            if let Some(steps) = self.verify_builtin_rule_premises(&premises, builtin_state)? {
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "union subset from both operand subsets".to_string(),
                        steps,
                    )
                    .into(),
                );
            }
        }

        // A predicate-defined set retains the exact carrier of its declared
        // base, so it is always contained in that base without inspecting the
        // predicate.
        if let Obj::SetBuilder(builder) = &subset_fact.left {
            if objs_equal_with_nested_binder_alpha_equivalence(
                builder.param_set.as_ref(),
                &subset_fact.right,
            ) {
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        subset_fact.clone().into(),
                        "set-builder subset of its base carrier".to_string(),
                        BuiltinRuleEvidence::SetBuilderSubsetBase,
                        Vec::new(),
                    )
                    .into(),
                );
            }
        }

        // A literal finite set is contained in a set when every listed member
        // is already known to belong to the target.
        if let Obj::ListSet(list_set) = &subset_fact.left {
            let premises = list_set
                .list
                .iter()
                .map(|element| {
                    InFact::new(
                        element.as_ref().clone(),
                        subset_fact.right.clone(),
                        subset_fact.line_file.clone(),
                    )
                    .into()
                })
                .collect::<Vec<AtomicFact>>();
            if let Some(steps) = self.verify_builtin_rule_premises(&premises, builtin_state)? {
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        subset_fact.clone().into(),
                        "literal finite-set subset from member facts".to_string(),
                        BuiltinRuleEvidence::LiteralSetSubset,
                        steps,
                    )
                    .into(),
                );
            }
        }

        // Literal Cartesian products are monotone componentwise. The factor
        // subset premises must already be known (or be direct non-builtin
        // facts), which keeps this constructor rule within one builtin hop.
        if let (Obj::Cart(left_cart), Obj::Cart(right_cart)) =
            (&subset_fact.left, &subset_fact.right)
        {
            if left_cart.args.len() == right_cart.args.len() {
                let premises = left_cart
                    .args
                    .iter()
                    .zip(right_cart.args.iter())
                    .filter(|(left_factor, right_factor)| {
                        !objs_equal_with_nested_binder_alpha_equivalence(
                            left_factor.as_ref(),
                            right_factor.as_ref(),
                        )
                    })
                    .map(|(left_factor, right_factor)| {
                        SubsetFact::new(
                            left_factor.as_ref().clone(),
                            right_factor.as_ref().clone(),
                            subset_fact.line_file.clone(),
                        )
                        .into()
                    })
                    .collect::<Vec<AtomicFact>>();
                if let Some(steps) = self.verify_builtin_rule_premises(&premises, builtin_state)? {
                    return Ok(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "Cartesian-product subset from componentwise subsets".to_string(),
                            steps,
                        )
                        .into(),
                    );
                }
            }
        }

        // Standard number sets form a fixed inclusion chain. Example: `N $subset R`.
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) =
            (&subset_fact.left, &subset_fact.right)
        {
            if left.is_subset_eq(right) {
                return Ok(
                    (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        subset_fact.clone().into(),
                        "standard_set_subset".to_string(),
                        BuiltinRuleEvidence::StandardSetSubset,
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        // Integer ranges inherit their numeric carrier from their integer
        // elements.  For N/N+, a verified lower endpoint is sufficient because
        // every range element is an integer at least that endpoint.
        // Examples: `closed_range(0, n) $subset N` and
        // `range(1, n) $subset N+`.
        let integer_range_start = match &subset_fact.left {
            Obj::Range(range) => Some(range.start.as_ref()),
            Obj::ClosedRange(range) => Some(range.start.as_ref()),
            _ => None,
        };
        if let (Some(start), Obj::StandardSet(target)) = (integer_range_start, &subset_fact.right) {
            let range_carrier_requirement = match target {
                StandardSet::N => Some(Some(StandardSet::N)),
                StandardSet::NPos => Some(Some(StandardSet::NPos)),
                _ if StandardSet::Z.is_subset_eq(target) => Some(None),
                _ => None,
            };
            if let Some(required_start_set) = range_carrier_requirement {
                let mut dependencies = Vec::new();
                if let Some(required_start_set) = required_start_set {
                    let start_membership: AtomicFact = InFact::new(
                        start.clone(),
                        required_start_set.into(),
                        subset_fact.line_file.clone(),
                    )
                    .into();
                    let result = self.verify_atomic_fact_as_builtin_rule_premise(
                        &start_membership,
                        builtin_state,
                    )?;
                    if !result.is_success() {
                        return Ok((UnknownGenericStmtResult::new()).into());
                    }
                    dependencies.push(result);
                }
                return Ok(
                    (SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "integer range is contained in its standard numeric carrier".to_string(),
                        dependencies,
                    ))
                    .into(),
                );
            }
        }

        // Every set is a subset of itself, including alpha-equivalent function
        // sets such as `fn(x X) X $subset fn(y X) X`.
        if objs_equal_with_nested_binder_alpha_equivalence(&subset_fact.left, &subset_fact.right) {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::Set(SetBuiltinRule::SubsetReflexivity),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Compose exactly two stored subset facts through one shared middle
        // set. This is deliberately a bounded leaf over known facts rather
        // than recursive reachability over the whole subset graph.
        // Example: `A subset B`, `B subset C` gives `A subset C`.
        let mut known_subsets = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.facts.atomic.by_two_args.values() {
                for known_fact in known_facts_map.values() {
                    if matches!(known_fact, AtomicFact::SubsetFact(_)) {
                        known_subsets.push(known_fact.clone());
                    }
                }
            }
        }
        known_subsets.sort_by_key(ToString::to_string);
        known_subsets.dedup_by(|left, right| left.to_string() == right.to_string());

        for first in &known_subsets {
            let AtomicFact::SubsetFact(first_subset) = first else {
                continue;
            };
            if !objs_equal_with_nested_binder_alpha_equivalence(
                &first_subset.left,
                &subset_fact.left,
            ) {
                continue;
            }
            for second in &known_subsets {
                let AtomicFact::SubsetFact(second_subset) = second else {
                    continue;
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(
                    &first_subset.right,
                    &second_subset.left,
                ) || !objs_equal_with_nested_binder_alpha_equivalence(
                    &second_subset.right,
                    &subset_fact.right,
                ) {
                    continue;
                }
                let first_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(first)?;
                let second_result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(second)?;
                if !first_result.is_success() || !second_result.is_success() {
                    continue;
                }
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        subset_fact.clone().into(),
                        "subset transitivity through one stored middle set".to_string(),
                        BuiltinRuleEvidence::Set(SetBuiltinRule::SubsetTransitivity),
                        vec![first_result, second_result],
                    )
                    .into(),
                );
            }
        }

        // Every finite real interval is a subset of R once its endpoints are
        // well-defined reals. Example: `'[a, b] $subset R`.
        if matches!(subset_fact.left, Obj::IntervalObj(_))
            && matches!(subset_fact.right, Obj::StandardSet(StandardSet::R))
        {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "real_interval_subset_R".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // The range of `f : ... -> T` is a subset of `T`, and of any known superset of `T`.
        // Example: `have f fn(x S) T` proves `fn_range(f) $subset T`.
        if let Obj::FnRange(fn_range) = &subset_fact.left {
            if let Some(body) = self.get_fn_range_function_body(&fn_range.function) {
                let ret_subset: AtomicFact = SubsetFact::new(
                    body.ret_set.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let ret_subset_result = if objs_equal_with_nested_binder_alpha_equivalence(
                    body.ret_set.as_ref(),
                    &subset_fact.right,
                ) {
                    SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        ret_subset.clone().into(),
                        "structural subset".to_string(),
                        Vec::new(),
                    )
                    .into()
                } else {
                    self.verify_atomic_fact_as_builtin_rule_premise(&ret_subset, builtin_state)?
                };
                if ret_subset_result.is_success() {
                    return Ok(
                        (SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "fn_range_subset_codomain".to_string(),
                            vec![ret_subset_result],
                        ))
                        .into(),
                    );
                }
            }
        }

        let converted_superset_fact = SupersetFact::new(
            subset_fact.right.clone(),
            subset_fact.left.clone(),
            subset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&converted_superset_fact)?;
        if verify_result.is_success() {
            Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::SetRelationDuality(
                        SetRelationDualityBuiltinRule::SubsetFromSuperset,
                    ),
                    vec![verify_result],
                ))
                .into(),
            )
        } else {
            Ok((UnknownGenericStmtResult::new()).into())
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        // Standard number sets form a fixed inclusion chain. Example: `R $supset N`.
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) =
            (&superset_fact.left, &superset_fact.right)
        {
            if right.is_subset_eq(left) {
                return Ok(
                    (SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                        superset_fact.clone().into(),
                        "standard_set_superset".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        // Every set is a superset of itself, including alpha-equivalent
        // function sets such as `fn(x X) X $supset fn(y X) X`.
        if objs_equal_with_nested_binder_alpha_equivalence(
            &superset_fact.left,
            &superset_fact.right,
        ) {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::Set(SetBuiltinRule::SupersetReflexivity),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let converted_subset_fact = SubsetFact::new(
            superset_fact.right.clone(),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        )
        .into();
        let verify_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&converted_subset_fact)?;
        if verify_result.is_success() {
            Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::SetRelationDuality(
                        SetRelationDualityBuiltinRule::SupersetFromSubset,
                    ),
                    vec![verify_result],
                ))
                .into(),
            )
        } else {
            Ok((UnknownGenericStmtResult::new()).into())
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        let converted_not_superset_fact = NotSupersetFact::new(
            not_subset_fact.right.clone(),
            not_subset_fact.left.clone(),
            not_subset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &converted_not_superset_fact,
        )?;
        if verify_result.is_success() {
            Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    not_subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::SetRelationDuality(
                        SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset,
                    ),
                    vec![verify_result],
                ))
                .into(),
            )
        } else {
            Ok((UnknownGenericStmtResult::new()).into())
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        let converted_not_subset_fact = NotSubsetFact::new(
            not_superset_fact.right.clone(),
            not_superset_fact.left.clone(),
            not_superset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &converted_not_subset_fact,
        )?;
        if verify_result.is_success() {
            Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    not_superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    BuiltinRuleEvidence::SetRelationDuality(
                        SetRelationDualityBuiltinRule::NotSupersetFromNotSubset,
                    ),
                    vec![verify_result],
                ))
                .into(),
            )
        } else {
            Ok((UnknownGenericStmtResult::new()).into())
        }
    }
}
