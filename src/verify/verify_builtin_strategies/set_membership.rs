use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_set_membership_with_builtin_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
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
                let direct = self
                    .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                        &child,
                    )?;
                let result = if direct.is_true() {
                    direct
                } else {
                    match &child {
                        AtomicFact::InFact(fact) => {
                            self.verify_set_membership_with_builtin_strategy(fact)?
                        }
                        AtomicFact::SubsetFact(fact) => {
                            self.verify_subset_with_builtin_strategy(fact)?
                        }
                        _ => StmtUnknown::new().into(),
                    }
                };
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
