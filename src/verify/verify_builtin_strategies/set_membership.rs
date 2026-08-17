use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_set_membership_with_builtin_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let literal_struct =
            self.verify_literal_tuple_struct_membership_with_builtin_strategy(fact)?;
        if literal_struct.is_true() {
            return Ok(literal_struct);
        }

        let defined_set =
            self.verify_one_layer_set_builder_membership_with_builtin_strategy(fact)?;
        if defined_set.is_true() {
            return Ok(defined_set);
        }

        let lf = fact.line_file.clone();
        let alternatives: Vec<Vec<AtomicFact>> = match &fact.set {
            Obj::Cart(cart) => {
                let Obj::Tuple(tuple) = &fact.element else {
                    return Ok(StmtUnknown::new().into());
                };
                if tuple.args.len() < 2 || tuple.args.len() != cart.args.len() {
                    return Ok(StmtUnknown::new().into());
                }
                vec![tuple
                    .args
                    .iter()
                    .zip(cart.args.iter())
                    .map(|(element, set)| {
                        InFact::new(element.as_ref().clone(), set.as_ref().clone(), lf.clone())
                            .into()
                    })
                    .collect()]
            }
            Obj::Union(set) => vec![
                vec![
                    InFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone()).into(),
                ],
                vec![
                    InFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone())
                        .into(),
                ],
            ],
            Obj::Intersect(set) => vec![vec![
                InFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone()).into(),
                InFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone()).into(),
            ]],
            Obj::SetMinus(set) => vec![vec![
                InFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone()).into(),
                NotInFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone()).into(),
            ]],
            Obj::PowerSet(set) => vec![vec![SubsetFact::new(
                fact.element.clone(),
                set.set.as_ref().clone(),
                lf.clone(),
            )
            .into()]],
            Obj::Range(range) => vec![vec![
                InFact::new(fact.element.clone(), StandardSet::Z.into(), lf.clone()).into(),
                LessEqualFact::new(
                    range.start.as_ref().clone(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
                LessFact::new(fact.element.clone(), range.end.as_ref().clone(), lf.clone()).into(),
            ]],
            Obj::ClosedRange(range) => vec![vec![
                InFact::new(fact.element.clone(), StandardSet::Z.into(), lf.clone()).into(),
                LessEqualFact::new(
                    range.start.as_ref().clone(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
                LessEqualFact::new(fact.element.clone(), range.end.as_ref().clone(), lf.clone())
                    .into(),
            ]],
            // Real interval membership structurally decomposes into the real
            // carrier and its two endpoint bounds. Each smaller child may use
            // one direct rule or another constructor-decreasing strategy.
            // Example: `r R+` implies `c in (c-r, c+r)`.
            Obj::IntervalObj(interval) => vec![vec![
                InFact::new(fact.element.clone(), StandardSet::R.into(), lf.clone()).into(),
                if interval.left_closed() {
                    LessEqualFact::new(interval.start().clone(), fact.element.clone(), lf.clone())
                        .into()
                } else {
                    LessFact::new(interval.start().clone(), fact.element.clone(), lf.clone()).into()
                },
                if interval.right_closed() {
                    LessEqualFact::new(fact.element.clone(), interval.end().clone(), lf.clone())
                        .into()
                } else {
                    LessFact::new(fact.element.clone(), interval.end().clone(), lf.clone()).into()
                },
            ]],
            _ => return Ok(StmtUnknown::new().into()),
        };

        let Some(children) = self.verify_set_strategy_alternatives(alternatives)? else {
            return Ok(StmtUnknown::new().into());
        };
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                "set-membership strategy: constructor membership decomposition".to_string(),
                children,
            )
            .into(),
        )
    }

    // A literal tuple is a direct dependent-structure constructor. This is a
    // strategy, rather than a raw builtin rule, because checking the declared
    // structure laws may require several independent child verifications.
    fn verify_literal_tuple_struct_membership_with_builtin_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let (Obj::Tuple(_), Obj::StructObj(struct_obj)) = (&fact.element, &fact.set) else {
            return Ok(StmtUnknown::new().into());
        };
        let final_state = UseContextVerifyState::new_with_final_round(false);
        self.verify_in_fact_by_struct_obj(fact, struct_obj, &final_state)
    }

    // Fold one literal or one-layer defined set builder. Every quantifier-free
    // predicate shape is kept intact, including disjunction: a known complete
    // `P(x) or Q(x)` may establish membership without selecting either branch.
    // Quantified predicates remain outside this bounded constructor strategy.
    fn verify_one_layer_set_builder_membership_with_builtin_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let goal_key = fact.to_string();
        if !self.active_set_builder_membership_unfolds.is_empty() {
            return Ok(StmtUnknown::new().into());
        }
        self.active_set_builder_membership_unfolds
            .insert(goal_key.clone());
        let result = self.verify_one_layer_set_builder_membership_with_builtin_strategy_once(fact);
        self.active_set_builder_membership_unfolds.remove(&goal_key);
        result
    }

    fn verify_one_layer_set_builder_membership_with_builtin_strategy_once(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(result) = self.try_verify_set_builder_membership_definition_transport(fact)? {
            return Ok(result);
        }
        // Most membership goals target a carrier parameter or a native set
        // constructor and cannot possibly unfold to a set builder. Avoid a
        // definition lookup for those overwhelmingly common cases.
        let indexed_set_builder = self.get_obj_equal_to_set_builder(&fact.set);
        if !matches!(
            &fact.set,
            Obj::SetBuilder(_) | Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_)
        ) && indexed_set_builder.is_none()
        {
            return Ok(StmtUnknown::new().into());
        }
        let final_state = UseContextVerifyState::new_with_final_round(false);
        if let Obj::InstantiatedTemplateObj(template_obj) = &fact.set {
            self.materialize_instantiated_template_obj(template_obj, &final_state)?;
        }
        let set_builder = match &fact.set {
            Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
            _ => self
                .unfold_known_fn_application_to_set_builder(&fact.set, &final_state)?
                .or(indexed_set_builder),
        };
        let Some(set_builder) = set_builder else {
            return Ok(StmtUnknown::new().into());
        };

        let mut children = Vec::with_capacity(set_builder.facts.len() + 1);
        let mut expected_premises = Vec::with_capacity(set_builder.facts.len() + 1);
        let base: AtomicFact = InFact::new(
            fact.element.clone(),
            set_builder.param_set.as_ref().clone(),
            fact.line_file.clone(),
        )
        .into();
        let base_result = self.verify_builtin_strategy_child(&base)?;
        if !base_result.is_true() {
            return Ok(StmtUnknown::new().into());
        }
        expected_premises.push(base.clone().into());
        children.push(base_result);

        let mut param_to_arg_map = std::collections::HashMap::new();
        insert_symbol_substitution(
            &mut param_to_arg_map,
            &set_builder.param_binding,
            fact.element.clone(),
        );
        for defining_fact in &set_builder.facts {
            let instantiated = self.inst_quantifier_free_fact(
                defining_fact,
                &param_to_arg_map,
                ParamObjType::SetBuilder,
                Some(&fact.line_file),
            )?;
            // A set-builder predicate may itself be a checked proposition whose
            // body is already known (for example an existential witness). Try
            // the restricted final round first, then fold exactly one named
            // proposition definition without reopening general proof search.
            let mut result =
                self.verify_fact_full(&instantiated.clone().to_fact(), &final_state)?;
            if !result.is_true() {
                if let QuantifierFreeFact::AtomicFact(atomic_fact) = &instantiated {
                    if matches!(atomic_fact, AtomicFact::NormalAtomicFact(_)) {
                        if let Some(definition_result) = self
                            .verify_atomic_fact_using_builtin_or_prop_definition(
                                atomic_fact,
                                &final_state,
                            )?
                        {
                            result = definition_result;
                        }
                    }
                }
            }
            if !result.is_true() {
                return Ok(StmtUnknown::new().into());
            }
            expected_premises.push(instantiated.clone().to_fact());
            children.push(result);
        }

        let target: Fact = fact.clone().into();
        if matches!(fact.set, Obj::SetBuilder(_)) {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                    target.clone(),
                    "set-builder membership strategy: unfold one set definition and verify its atomic obligations"
                        .to_string(),
                    BuiltinRuleEvidence::SetBuilderMembership(
                        SetBuilderMembershipBuiltinRuleEvidence::new(
                            target,
                            expected_premises,
                        ),
                    ),
                    children,
                )
                .into(),
            );
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                target,
                "set-builder membership strategy: unfold one set definition and verify its atomic obligations"
                    .to_string(),
                children,
            )
            .into(),
        )
    }

    pub(crate) fn verify_subset_with_builtin_strategy(
        &mut self,
        fact: &SubsetFact,
    ) -> Result<StmtResult, RuntimeError> {
        let lf = fact.line_file.clone();
        let mut alternatives: Vec<Vec<AtomicFact>> = Vec::new();
        match &fact.left {
            Obj::ListSet(set) => alternatives.push(
                set.list
                    .iter()
                    .map(|element| {
                        InFact::new(element.as_ref().clone(), fact.right.clone(), lf.clone()).into()
                    })
                    .collect(),
            ),
            Obj::Union(set) => alternatives.push(vec![
                SubsetFact::new(set.left.as_ref().clone(), fact.right.clone(), lf.clone()).into(),
                SubsetFact::new(set.right.as_ref().clone(), fact.right.clone(), lf.clone()).into(),
            ]),
            Obj::Intersect(set) => {
                alternatives.push(vec![SubsetFact::new(
                    set.left.as_ref().clone(),
                    fact.right.clone(),
                    lf.clone(),
                )
                .into()]);
                alternatives.push(vec![SubsetFact::new(
                    set.right.as_ref().clone(),
                    fact.right.clone(),
                    lf.clone(),
                )
                .into()]);
            }
            Obj::SetMinus(set) => alternatives.push(vec![SubsetFact::new(
                set.left.as_ref().clone(),
                fact.right.clone(),
                lf.clone(),
            )
            .into()]),
            _ => {}
        }
        if let Obj::Intersect(set) = &fact.right {
            alternatives.push(vec![
                SubsetFact::new(fact.left.clone(), set.left.as_ref().clone(), lf.clone()).into(),
                SubsetFact::new(fact.left.clone(), set.right.as_ref().clone(), lf.clone()).into(),
            ]);
        }
        let Some(children) = self.verify_set_strategy_alternatives(alternatives)? else {
            return Ok(StmtUnknown::new().into());
        };
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                "set-containment strategy: constructor containment decomposition".to_string(),
                children,
            )
            .into(),
        )
    }

    fn verify_set_strategy_alternatives(
        &mut self,
        alternatives: Vec<Vec<AtomicFact>>,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        for required in alternatives {
            let mut results = Vec::with_capacity(required.len());
            let mut complete = true;
            for child in required {
                let result = self.verify_builtin_strategy_child(&child)?;
                if !result.is_true() {
                    complete = false;
                    break;
                }
                results.push(result);
            }
            if complete {
                return Ok(Some(results));
            }
        }
        Ok(None)
    }
}
