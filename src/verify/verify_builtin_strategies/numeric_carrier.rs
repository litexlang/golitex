use crate::prelude::*;

impl Runtime {
    // Descends through arithmetic syntax while keeping the requested numeric carrier explicit.
    // A strategy layer may use one direct builtin rule for each immediate child, then repeats
    // only this structural carrier decomposition when that direct attempt is unknown.
    pub(crate) fn verify_numeric_carrier_with_builtin_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let Obj::StandardSet(target) = &fact.set else {
            return Ok(StmtUnknown::new().into());
        };
        let lf = fact.line_file.clone();
        let extremum_set = match &fact.element {
            Obj::FiniteSetMax(x) => Some(x.set.as_ref()),
            Obj::FiniteSetMin(x) => Some(x.set.as_ref()),
            _ => None,
        };
        if matches!(
            target,
            StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
        ) {
            if let Obj::FiniteSetSize(size) = &fact.element {
                let required = [AtomicFact::from(IsFiniteSetFact::new(
                    size.set.as_ref().clone(),
                    lf.clone(),
                ))];
                let Some(children) = self.verify_numeric_carrier_strategy_children(&required)?
                else {
                    return Ok(StmtUnknown::new().into());
                };
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: cardinality of a structurally finite set"
                            .to_string(),
                        children,
                    )
                    .into(),
                );
            }
            if let Some(set) = extremum_set {
                let Some(children) =
                    self.verify_set_elements_in_numeric_carrier_strategy(set, target, &lf)?
                else {
                    return Ok(StmtUnknown::new().into());
                };
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: finite extremum source is real-valued"
                            .to_string(),
                        children,
                    )
                    .into(),
                );
            }
        }
        if let Some(required) = self.refined_numeric_carrier_children(fact, target, &lf) {
            let Some(children) = self.verify_numeric_carrier_strategy_children(&required)? else {
                return Ok(StmtUnknown::new().into());
            };
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                    fact.clone().into(),
                    format!(
                        "numeric-carrier strategy: base carrier and sign conditions for {target}"
                    ),
                    children,
                )
                .into(),
            );
        }
        let required = match target {
            StandardSet::R => self.real_carrier_children(&fact.element, &lf),
            StandardSet::Q => self.rational_carrier_children(&fact.element, &lf),
            StandardSet::Z => self.integer_carrier_children(&fact.element, &lf),
            StandardSet::N => self.natural_carrier_children(&fact.element, &lf),
            StandardSet::NPos => {
                return self.verify_positive_natural_carrier_strategy(fact);
            }
            _ => None,
        };
        let Some(required) = required else {
            return Ok(StmtUnknown::new().into());
        };
        let Some(children) = self.verify_numeric_carrier_strategy_children(&required)? else {
            return Ok(StmtUnknown::new().into());
        };
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                format!("numeric-carrier strategy: structural closure in {target}"),
                children,
            )
            .into(),
        )
    }

    fn refined_numeric_carrier_children(
        &self,
        fact: &InFact,
        target: &StandardSet,
        lf: &LineFile,
    ) -> Option<Vec<AtomicFact>> {
        let zero: Obj = Number::new("0".to_string()).into();
        let element = fact.element.clone();
        let (base, condition): (StandardSet, AtomicFact) = match target {
            StandardSet::QPos => (
                StandardSet::Q,
                LessFact::new(zero, element.clone(), lf.clone()).into(),
            ),
            StandardSet::RPos => (
                StandardSet::R,
                LessFact::new(zero, element.clone(), lf.clone()).into(),
            ),
            StandardSet::QNeg => (
                StandardSet::Q,
                LessFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::ZNeg => (
                StandardSet::Z,
                LessFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::RNeg => (
                StandardSet::R,
                LessFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::QNz => (
                StandardSet::Q,
                NotEqualFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::ZNz => (
                StandardSet::Z,
                NotEqualFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::RNz => (
                StandardSet::R,
                NotEqualFact::new(element.clone(), zero, lf.clone()).into(),
            ),
            _ => return None,
        };
        Some(vec![
            InFact::new(element, base.into(), lf.clone()).into(),
            condition,
        ])
    }

    fn real_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let real: Obj = StandardSet::R.into();
        match obj {
            Obj::Add(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), real.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), real, lf.clone()).into(),
            ]),
            Obj::Mul(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), real.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), real, lf.clone()).into(),
            ]),
            Obj::Sub(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), real.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), real, lf.clone()).into(),
            ]),
            Obj::Div(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), real.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), real, lf.clone()).into(),
            ]),
            Obj::Pow(x) => Some(vec![
                InFact::new(x.base.as_ref().clone(), real, lf.clone()).into()
            ]),
            _ => None,
        }
    }

    fn rational_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let rational: Obj = StandardSet::Q.into();
        match obj {
            Obj::Add(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), rational.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), rational, lf.clone()).into(),
            ]),
            Obj::Mul(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), rational.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), rational, lf.clone()).into(),
            ]),
            Obj::Sub(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), rational.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), rational, lf.clone()).into(),
            ]),
            Obj::Div(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), rational.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), rational, lf.clone()).into(),
            ]),
            Obj::Pow(x) => Some(vec![
                InFact::new(x.base.as_ref().clone(), rational, lf.clone()).into(),
                InFact::new(
                    x.exponent.as_ref().clone(),
                    StandardSet::Z.into(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Abs(x) => Some(vec![InFact::new(
                x.arg.as_ref().clone(),
                rational,
                lf.clone(),
            )
            .into()]),
            _ => None,
        }
    }

    fn integer_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let integer: Obj = StandardSet::Z.into();
        match obj {
            Obj::Add(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), integer.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), integer, lf.clone()).into(),
            ]),
            Obj::Mul(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), integer.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), integer, lf.clone()).into(),
            ]),
            Obj::Mod(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), integer.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), integer, lf.clone()).into(),
            ]),
            Obj::Sub(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), integer.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), integer, lf.clone()).into(),
            ]),
            Obj::Pow(x) => Some(vec![
                InFact::new(x.base.as_ref().clone(), integer, lf.clone()).into(),
                InFact::new(
                    x.exponent.as_ref().clone(),
                    StandardSet::N.into(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Abs(x) => Some(vec![InFact::new(
                x.arg.as_ref().clone(),
                integer,
                lf.clone(),
            )
            .into()]),
            _ => None,
        }
    }

    fn natural_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let natural: Obj = StandardSet::N.into();
        match obj {
            Obj::Add(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), natural.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), natural, lf.clone()).into(),
            ]),
            Obj::Mul(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), natural.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), natural, lf.clone()).into(),
            ]),
            Obj::Sub(x) => Some(vec![
                InFact::new(x.left.as_ref().clone(), StandardSet::Z.into(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), StandardSet::Z.into(), lf.clone()).into(),
                LessEqualFact::new(
                    x.right.as_ref().clone(),
                    x.left.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Pow(x) => Some(vec![
                InFact::new(x.base.as_ref().clone(), natural.clone(), lf.clone()).into(),
                InFact::new(x.exponent.as_ref().clone(), natural, lf.clone()).into(),
            ]),
            Obj::Abs(x) => Some(vec![InFact::new(
                x.arg.as_ref().clone(),
                StandardSet::Z.into(),
                lf.clone(),
            )
            .into()]),
            _ => None,
        }
    }

    fn verify_positive_natural_carrier_strategy(
        &mut self,
        fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let lf = fact.line_file.clone();
        let n: Obj = StandardSet::N.into();
        let n_pos: Obj = StandardSet::NPos.into();
        let alternatives: Vec<Vec<AtomicFact>> = match &fact.element {
            Obj::Add(x) => vec![
                vec![
                    InFact::new(x.left.as_ref().clone(), n_pos.clone(), lf.clone()).into(),
                    InFact::new(x.right.as_ref().clone(), n.clone(), lf.clone()).into(),
                ],
                vec![
                    InFact::new(x.left.as_ref().clone(), n, lf.clone()).into(),
                    InFact::new(x.right.as_ref().clone(), n_pos.clone(), lf.clone()).into(),
                ],
            ],
            Obj::Mul(x) => vec![vec![
                InFact::new(x.left.as_ref().clone(), n_pos.clone(), lf.clone()).into(),
                InFact::new(x.right.as_ref().clone(), n_pos.clone(), lf.clone()).into(),
            ]],
            Obj::Pow(x) => vec![vec![
                InFact::new(x.base.as_ref().clone(), n_pos, lf.clone()).into(),
                InFact::new(
                    x.exponent.as_ref().clone(),
                    StandardSet::N.into(),
                    lf.clone(),
                )
                .into(),
            ]],
            Obj::Abs(x) => vec![vec![
                InFact::new(x.arg.as_ref().clone(), StandardSet::Z.into(), lf.clone()).into(),
                LessFact::new(
                    Number::new("0".to_string()).into(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
            ]],
            Obj::FiniteSetSize(_) => vec![vec![
                InFact::new(fact.element.clone(), StandardSet::N.into(), lf.clone()).into(),
                LessEqualFact::new(
                    Number::new("1".to_string()).into(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
            ]],
            _ => return Ok(StmtUnknown::new().into()),
        };

        for required in alternatives {
            if let Some(children) = self.verify_numeric_carrier_strategy_children(&required)? {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: structural closure in N+".to_string(),
                        children,
                    )
                    .into(),
                );
            }
        }
        Ok(StmtUnknown::new().into())
    }

    fn verify_numeric_carrier_strategy_children(
        &mut self,
        required: &[AtomicFact],
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut results = Vec::with_capacity(required.len());
        for child in required {
            let result = self.verify_builtin_strategy_child(child)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(results))
    }

    fn verify_set_elements_in_numeric_carrier_strategy(
        &mut self,
        set: &Obj,
        target: &StandardSet,
        lf: &LineFile,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let target_obj: Obj = target.clone().into();
        let subset: AtomicFact =
            SubsetFact::new(set.clone(), target_obj.clone(), lf.clone()).into();
        let direct =
            self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(&subset)?;
        if direct.is_true() {
            return Ok(Some(vec![direct]));
        }

        let mut results = Vec::new();
        match set {
            Obj::ListSet(list) => {
                for element in &list.list {
                    let child: AtomicFact =
                        InFact::new(element.as_ref().clone(), target_obj.clone(), lf.clone())
                            .into();
                    let direct = self
                        .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                            &child,
                        )?;
                    let result = if direct.is_true() {
                        direct
                    } else {
                        let AtomicFact::InFact(child_fact) = child else {
                            unreachable!("constructed a membership fact")
                        };
                        self.verify_numeric_carrier_with_builtin_strategy(&child_fact)?
                    };
                    if !result.is_true() {
                        return Ok(None);
                    }
                    results.push(result);
                }
            }
            Obj::Union(x) => {
                for child in [x.left.as_ref(), x.right.as_ref()] {
                    let Some(mut child_results) =
                        self.verify_set_elements_in_numeric_carrier_strategy(child, target, lf)?
                    else {
                        return Ok(None);
                    };
                    results.append(&mut child_results);
                }
            }
            Obj::SetDiff(x) => {
                for child in [x.left.as_ref(), x.right.as_ref()] {
                    let Some(mut child_results) =
                        self.verify_set_elements_in_numeric_carrier_strategy(child, target, lf)?
                    else {
                        return Ok(None);
                    };
                    results.append(&mut child_results);
                }
            }
            Obj::Intersect(x) => {
                let Some(mut child_results) = self
                    .verify_set_elements_in_numeric_carrier_strategy(x.left.as_ref(), target, lf)?
                else {
                    return Ok(None);
                };
                results.append(&mut child_results);
            }
            Obj::SetMinus(x) => {
                let Some(mut child_results) = self
                    .verify_set_elements_in_numeric_carrier_strategy(x.left.as_ref(), target, lf)?
                else {
                    return Ok(None);
                };
                results.append(&mut child_results);
            }
            Obj::SetBuilder(x) => {
                let Some(mut child_results) = self
                    .verify_set_elements_in_numeric_carrier_strategy(
                        x.param_set.as_ref(),
                        target,
                        lf,
                    )?
                else {
                    return Ok(None);
                };
                results.append(&mut child_results);
            }
            _ => return Ok(None),
        }
        Ok(Some(results))
    }
}
