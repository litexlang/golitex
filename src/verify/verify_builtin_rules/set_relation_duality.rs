use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    reason.to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // A union is contained in a set when both operands are already known
        // to be contained in it.
        if let Obj::Union(union) = &subset_fact.left {
            let mut steps = Vec::with_capacity(2);
            let mut both_operands_are_subsets = true;
            for operand in [&union.left, &union.right] {
                let operand_subset: AtomicFact = SubsetFact::new(
                    operand.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let result = self
                    .verify_atomic_fact_as_builtin_rule_premise(&operand_subset, builtin_state)?;
                if !result.is_true() {
                    both_operands_are_subsets = false;
                    break;
                }
                steps.push(result);
            }
            if both_operands_are_subsets {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "union subset from both operand subsets".to_string(),
                        steps,
                    )
                    .into(),
                );
            }
        }

        // A literal finite set is contained in a set when every listed member
        // is already known to belong to the target.
        if let Obj::ListSet(list_set) = &subset_fact.left {
            let mut steps = Vec::with_capacity(list_set.list.len());
            let mut all_elements_are_members = true;
            for element in &list_set.list {
                let membership: AtomicFact = InFact::new(
                    element.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&membership, builtin_state)?;
                if !result.is_true() {
                    all_elements_are_members = false;
                    break;
                }
                steps.push(result);
            }
            if all_elements_are_members {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "literal finite-set subset from member facts".to_string(),
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
                let mut steps = Vec::with_capacity(left_cart.args.len());
                let mut all_factors_are_subsets = true;
                for (left_factor, right_factor) in left_cart.args.iter().zip(right_cart.args.iter())
                {
                    let factor_subset: AtomicFact = SubsetFact::new(
                        left_factor.as_ref().clone(),
                        right_factor.as_ref().clone(),
                        subset_fact.line_file.clone(),
                    )
                    .into();
                    let result = self.verify_atomic_fact_as_builtin_rule_premise(
                        &factor_subset,
                        builtin_state,
                    )?;
                    if !result.is_true() {
                        all_factors_are_subsets = false;
                        break;
                    }
                    steps.push(result);
                }
                if all_factors_are_subsets {
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
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
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "standard_set_subset".to_string(),
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
                    if !result.is_true() {
                        return Ok((StmtUnknown::new()).into());
                    }
                    dependencies.push(result);
                }
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
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
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Every finite real interval is a subset of R once its endpoints are
        // well-defined reals. Example: `'[a, b] $subset R`.
        if matches!(subset_fact.left, Obj::IntervalObj(_))
            && matches!(subset_fact.right, Obj::StandardSet(StandardSet::R))
        {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
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
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        ret_subset.clone().into(),
                        "structural subset".to_string(),
                        Vec::new(),
                    )
                    .into()
                } else {
                    self.verify_atomic_fact_as_builtin_rule_premise(&ret_subset, builtin_state)?
                };
                if ret_subset_result.is_true() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
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
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
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
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Standard number sets form a fixed inclusion chain. Example: `R $supset N`.
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) =
            (&superset_fact.left, &superset_fact.right)
        {
            if right.is_subset_eq(left) {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
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
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
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
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
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
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _builtin_state: &UseBuiltinRuleVerifyState,
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
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
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
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _builtin_state: &UseBuiltinRuleVerifyState,
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
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
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
            Ok((StmtUnknown::new()).into())
        }
    }
}
