use crate::prelude::*;

impl Runtime {
    // Descends through arithmetic syntax while keeping the requested numeric carrier explicit.
    // A strategy layer may use one direct builtin rule for each immediate child, then repeats
    // only this structural carrier decomposition when that direct attempt is unknown.
    pub fn verify_numeric_carrier_with_builtin_strategy(
        &mut self,
        fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Obj::StandardSet(target) = &fact.set else {
            return Ok(UnknownGenericStmtResult::new().into());
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
                let required = [AtomicFact::from(
                    self.new_is_finite_set_fact(size.set.as_ref().clone(), lf.clone()),
                )];
                let Some(children) =
                    self.verify_numeric_carrier_strategy_children(&required, verify_state)?
                else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: cardinality of a structurally finite set"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyNumericCarrierWithBuiltinStrategy01),
                        children,
                    )
                    .into(),
                );
            }
            if let Some(set) = extremum_set {
                let Some(children) = self.verify_set_elements_in_numeric_carrier_strategy(
                    set,
                    target,
                    &lf,
                    verify_state,
                )?
                else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: finite extremum source is real-valued"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyNumericCarrierWithBuiltinStrategy02),
                        children,
                    )
                    .into(),
                );
            }
        }
        if let Some(required) = self.refined_numeric_carrier_children(fact, target, &lf) {
            let Some(children) =
                self.verify_numeric_carrier_strategy_children(&required, verify_state)?
            else {
                return Ok(UnknownGenericStmtResult::new().into());
            };
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                    fact.clone().into(),
                    format!(
                        "numeric-carrier strategy: base carrier and sign conditions for {target}"
                    ),
                    BuiltinRuleEvidence::RefinedNumericMembership(
                        RefinedNumericMembershipBuiltinRuleEvidence::new(
                            fact.clone().into(),
                            required.iter().cloned().map(Fact::from).collect(),
                        ),
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
                return self.verify_positive_natural_carrier_strategy(fact, verify_state);
            }
            _ => None,
        };
        let Some(required) = required else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let Some(children) =
            self.verify_numeric_carrier_strategy_children(&required, verify_state)?
        else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let real_rule = if matches!(target, StandardSet::R) {
            match &fact.element {
                Obj::Add(_) => Some(RealArithmeticMembershipClosureBuiltinRule::Add),
                Obj::Sub(_) => Some(RealArithmeticMembershipClosureBuiltinRule::Sub),
                Obj::Mul(_) => Some(RealArithmeticMembershipClosureBuiltinRule::Mul),
                Obj::Div(_) => Some(RealArithmeticMembershipClosureBuiltinRule::Div),
                Obj::Pow(_) => Some(RealArithmeticMembershipClosureBuiltinRule::Pow),
                _ => None,
            }
        } else {
            None
        };
        if let Some(rule) = real_rule {
            let conjunction: Fact = self.new_and_fact(required, lf).into();
            let conjunction_result = SuccessProveFactResult::new(
                conjunction.clone(),
                SuccessInferResult::new(),
                SuccessFactProofResult::combined_steps(children),
            );
            let conjunction_result = self.complete_fact_proof_result(
                &conjunction,
                conjunction_result.into(),
                verify_state,
            )?;
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                    fact.clone().into(),
                    "numeric-carrier strategy: typed structural closure in R".to_string(),
                    BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule),
                    vec![conjunction_result.into()],
                )
                .into(),
            );
        }
        let integer_rule = if matches!(target, StandardSet::Z) {
            match &fact.element {
                Obj::Add(_) => Some(IntegerMembershipClosureBuiltinRule::Add),
                Obj::Sub(_) => Some(IntegerMembershipClosureBuiltinRule::Sub),
                Obj::Mul(_) => Some(IntegerMembershipClosureBuiltinRule::Mul),
                Obj::Mod(_) => Some(IntegerMembershipClosureBuiltinRule::Mod),
                Obj::Pow(_) => Some(IntegerMembershipClosureBuiltinRule::PowNat),
                _ => None,
            }
        } else {
            None
        };
        if let Some(rule) = integer_rule {
            let conjunction: Fact = self.new_and_fact(required, lf).into();
            let conjunction_result = SuccessProveFactResult::new(
                conjunction.clone(),
                SuccessInferResult::new(),
                SuccessFactProofResult::combined_steps(children),
            );
            let conjunction_result = self.complete_fact_proof_result(
                &conjunction,
                conjunction_result.into(),
                verify_state,
            )?;
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                    fact.clone().into(),
                    "numeric-carrier strategy: typed structural closure in Z".to_string(),
                    BuiltinRuleEvidence::IntegerMembershipClosure(rule),
                    vec![conjunction_result],
                )
                .into(),
            );
        }
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                format!("numeric-carrier strategy: structural closure in {target}"),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyNumericCarrierWithBuiltinStrategy03,
                ),
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
                self.new_less_fact(zero, element.clone(), lf.clone()).into(),
            ),
            StandardSet::RPos => (
                StandardSet::R,
                self.new_less_fact(zero, element.clone(), lf.clone()).into(),
            ),
            StandardSet::QNeg => (
                StandardSet::Q,
                self.new_less_fact(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::ZNeg => (
                StandardSet::Z,
                self.new_less_fact(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::RNeg => (
                StandardSet::R,
                self.new_less_fact(element.clone(), zero, lf.clone()).into(),
            ),
            StandardSet::QStar => (
                StandardSet::Q,
                self.new_not_equal_fact(element.clone(), zero, lf.clone())
                    .into(),
            ),
            StandardSet::ZStar => (
                StandardSet::Z,
                self.new_not_equal_fact(element.clone(), zero, lf.clone())
                    .into(),
            ),
            StandardSet::RStar => (
                StandardSet::R,
                self.new_not_equal_fact(element.clone(), zero, lf.clone())
                    .into(),
            ),
            StandardSet::CStar => (
                StandardSet::C,
                self.new_not_equal_fact(element.clone(), zero, lf.clone())
                    .into(),
            ),
            _ => return None,
        };
        Some(vec![
            self.new_in_fact(element, base.into(), lf.clone()).into(),
            condition,
        ])
    }

    fn real_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let real: Obj = StandardSet::R.into();
        match obj {
            Obj::Add(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), real.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), real, lf.clone())
                    .into(),
            ]),
            Obj::Mul(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), real.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), real, lf.clone())
                    .into(),
            ]),
            Obj::Sub(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), real.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), real, lf.clone())
                    .into(),
            ]),
            Obj::Div(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), real.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), real, lf.clone())
                    .into(),
            ]),
            Obj::Pow(x) => Some(vec![self
                .new_in_fact(x.base.as_ref().clone(), real, lf.clone())
                .into()]),
            _ => None,
        }
    }

    fn rational_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let rational: Obj = StandardSet::Q.into();
        match obj {
            Obj::Add(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), rational.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), rational, lf.clone())
                    .into(),
            ]),
            Obj::Mul(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), rational.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), rational, lf.clone())
                    .into(),
            ]),
            Obj::Sub(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), rational.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), rational, lf.clone())
                    .into(),
            ]),
            Obj::Div(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), rational.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), rational, lf.clone())
                    .into(),
            ]),
            Obj::Pow(x) => Some(vec![
                self.new_in_fact(x.base.as_ref().clone(), rational, lf.clone())
                    .into(),
                self.new_in_fact(
                    x.exponent.as_ref().clone(),
                    StandardSet::Z.into(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Abs(x) => Some(vec![self
                .new_in_fact(x.arg.as_ref().clone(), rational, lf.clone())
                .into()]),
            _ => None,
        }
    }

    fn integer_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let integer: Obj = StandardSet::Z.into();
        match obj {
            Obj::Add(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), integer.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), integer, lf.clone())
                    .into(),
            ]),
            Obj::Mul(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), integer.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), integer, lf.clone())
                    .into(),
            ]),
            Obj::Mod(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), integer.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), integer, lf.clone())
                    .into(),
            ]),
            Obj::Sub(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), integer.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), integer, lf.clone())
                    .into(),
            ]),
            Obj::Pow(x) => Some(vec![
                self.new_in_fact(x.base.as_ref().clone(), integer, lf.clone())
                    .into(),
                self.new_in_fact(
                    x.exponent.as_ref().clone(),
                    StandardSet::N.into(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Abs(x) => Some(vec![self
                .new_in_fact(x.arg.as_ref().clone(), integer, lf.clone())
                .into()]),
            _ => None,
        }
    }

    fn natural_carrier_children(&self, obj: &Obj, lf: &LineFile) -> Option<Vec<AtomicFact>> {
        let natural: Obj = StandardSet::N.into();
        match obj {
            Obj::Add(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), natural.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), natural, lf.clone())
                    .into(),
            ]),
            Obj::Mul(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), natural.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), natural, lf.clone())
                    .into(),
            ]),
            Obj::Sub(x) => Some(vec![
                self.new_in_fact(x.left.as_ref().clone(), StandardSet::Z.into(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), StandardSet::Z.into(), lf.clone())
                    .into(),
                self.new_less_equal_fact(
                    x.right.as_ref().clone(),
                    x.left.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
            ]),
            Obj::Pow(x) => Some(vec![
                self.new_in_fact(x.base.as_ref().clone(), natural.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.exponent.as_ref().clone(), natural, lf.clone())
                    .into(),
            ]),
            Obj::Abs(x) => Some(vec![self
                .new_in_fact(x.arg.as_ref().clone(), StandardSet::Z.into(), lf.clone())
                .into()]),
            _ => None,
        }
    }

    fn verify_positive_natural_carrier_strategy(
        &mut self,
        fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let lf = fact.line_file.clone();
        let n: Obj = StandardSet::N.into();
        let n_pos: Obj = StandardSet::NPos.into();
        let alternatives: Vec<Vec<AtomicFact>> = match &fact.element {
            Obj::Add(x) => vec![
                vec![
                    self.new_in_fact(x.left.as_ref().clone(), n_pos.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(x.right.as_ref().clone(), n.clone(), lf.clone())
                        .into(),
                ],
                vec![
                    self.new_in_fact(x.left.as_ref().clone(), n, lf.clone())
                        .into(),
                    self.new_in_fact(x.right.as_ref().clone(), n_pos.clone(), lf.clone())
                        .into(),
                ],
            ],
            Obj::Mul(x) => vec![vec![
                self.new_in_fact(x.left.as_ref().clone(), n_pos.clone(), lf.clone())
                    .into(),
                self.new_in_fact(x.right.as_ref().clone(), n_pos.clone(), lf.clone())
                    .into(),
            ]],
            Obj::Pow(x) => vec![vec![
                self.new_in_fact(x.base.as_ref().clone(), n_pos, lf.clone())
                    .into(),
                self.new_in_fact(
                    x.exponent.as_ref().clone(),
                    StandardSet::N.into(),
                    lf.clone(),
                )
                .into(),
            ]],
            Obj::Abs(x) => vec![vec![
                self.new_in_fact(x.arg.as_ref().clone(), StandardSet::Z.into(), lf.clone())
                    .into(),
                self.new_less_fact(
                    Number::new("0".to_string()).into(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
            ]],
            Obj::FiniteSetSize(_) => vec![vec![
                self.new_in_fact(fact.element.clone(), StandardSet::N.into(), lf.clone())
                    .into(),
                self.new_less_equal_fact(
                    Number::new("1".to_string()).into(),
                    fact.element.clone(),
                    lf.clone(),
                )
                .into(),
            ]],
            _ => return Ok(UnknownGenericStmtResult::new().into()),
        };

        for required in alternatives {
            if let Some(children) =
                self.verify_numeric_carrier_strategy_children(&required, verify_state)?
            {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "numeric-carrier strategy: structural closure in N+".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyPositiveNaturalCarrierStrategy),
                        children,
                    )
                    .into(),
                );
            }
        }
        Ok(UnknownGenericStmtResult::new().into())
    }

    fn verify_numeric_carrier_strategy_children(
        &mut self,
        required: &[AtomicFact],
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let mut results = Vec::with_capacity(required.len());
        for child in required {
            let result = self.verify_builtin_strategy_child(child, verify_state)?;
            if !result.is_success() {
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
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let target_obj: Obj = target.clone().into();
        let subset: AtomicFact = self
            .new_subset_fact(set.clone(), target_obj.clone(), lf.clone())
            .into();
        let direct_proof = self
            .verify_non_equational_atomic_fact_with_bounded_builtin_routes(&subset, verify_state)?;
        let direct = self.complete_atomic_fact_proof_result(&subset, direct_proof, verify_state)?;
        if direct.is_success() {
            return Ok(Some(vec![direct]));
        }

        let mut results = Vec::new();
        match set {
            Obj::ListSet(list) => {
                for element in &list.list {
                    let child: AtomicFact = self
                        .new_in_fact(element.as_ref().clone(), target_obj.clone(), lf.clone())
                        .into();
                    let direct_proof = self
                        .verify_non_equational_atomic_fact_with_bounded_builtin_routes(
                            &child,
                            verify_state,
                        )?;
                    let direct =
                        self.complete_atomic_fact_proof_result(&child, direct_proof, verify_state)?;
                    let result = if direct.is_success() {
                        direct
                    } else {
                        let AtomicFact::InFact(child_fact) = &child else {
                            unreachable!("constructed a membership fact")
                        };
                        let proof = self.verify_numeric_carrier_with_builtin_strategy(
                            child_fact,
                            verify_state,
                        )?;
                        self.complete_atomic_fact_proof_result(&child, proof, verify_state)?
                    };
                    if !result.is_success() {
                        return Ok(None);
                    }
                    results.push(result);
                }
            }
            Obj::Union(x) => {
                for child in [x.left.as_ref(), x.right.as_ref()] {
                    let Some(mut child_results) = self
                        .verify_set_elements_in_numeric_carrier_strategy(
                            child,
                            target,
                            lf,
                            verify_state,
                        )?
                    else {
                        return Ok(None);
                    };
                    results.append(&mut child_results);
                }
            }
            Obj::Intersect(x) => {
                let Some(mut child_results) = self
                    .verify_set_elements_in_numeric_carrier_strategy(
                        x.left.as_ref(),
                        target,
                        lf,
                        verify_state,
                    )?
                else {
                    return Ok(None);
                };
                results.append(&mut child_results);
            }
            Obj::SetMinus(x) => {
                let Some(mut child_results) = self
                    .verify_set_elements_in_numeric_carrier_strategy(
                        x.left.as_ref(),
                        target,
                        lf,
                        verify_state,
                    )?
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
                        verify_state,
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
