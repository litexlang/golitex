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
            Obj::SetDiff(set) => vec![
                vec![
                    InFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone()).into(),
                    NotInFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone())
                        .into(),
                ],
                vec![
                    InFact::new(fact.element.clone(), set.right.as_ref().clone(), lf.clone())
                        .into(),
                    NotInFact::new(fact.element.clone(), set.left.as_ref().clone(), lf.clone())
                        .into(),
                ],
            ],
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

    // Fold one literal or one-layer defined set builder. The strategy is
    // intentionally restricted to atomic defining facts, and each obligation
    // is verified as an independent strategy child. This prevents a defined
    // membership goal from recursively re-entering the same raw builtin rule.
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
        // Most membership goals target a carrier parameter or a native set
        // constructor and cannot possibly unfold to a set builder. Avoid a
        // definition lookup for those overwhelmingly common cases.
        let indexed_set_builder = self.get_obj_equal_to_set_builder(&fact.set.to_string());
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
            _ => match self.unfold_known_fn_application_once(&fact.set, &final_state)? {
                Some(Obj::SetBuilder(set_builder)) => Some(set_builder),
                _ => indexed_set_builder,
            },
        };
        let Some(set_builder) = set_builder else {
            return Ok(StmtUnknown::new().into());
        };

        let mut children = Vec::with_capacity(set_builder.facts.len() + 1);
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
        children.push(base_result);

        let mut param_to_arg_map = std::collections::HashMap::new();
        insert_symbol_substitution(
            &mut param_to_arg_map,
            &set_builder.param_binding,
            fact.element.clone(),
        );
        for defining_fact in &set_builder.facts {
            let instantiated = self.inst_exist_body_fact(
                defining_fact,
                &param_to_arg_map,
                ParamObjType::SetBuilder,
                Some(&fact.line_file),
            )?;
            let ExistBodyFact::AtomicFact(atomic) = instantiated else {
                return Ok(StmtUnknown::new().into());
            };
            // A set-builder predicate may itself be a checked proposition whose
            // body is already known (for example an existential witness). Use
            // the final context round so that one proposition fold is allowed
            // without reopening known-forall or unbounded strategy search.
            let result = self.verify_atomic_fact(&atomic, &final_state)?;
            if !result.is_true() {
                return Ok(StmtUnknown::new().into());
            }
            children.push(result);
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
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
            Obj::SetDiff(set) => alternatives.push(vec![
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
