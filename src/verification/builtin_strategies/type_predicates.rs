use crate::prelude::*;

impl Runtime {
    // Repeatedly applies finite-set constructor rules to strictly smaller set expressions.
    // Example: `$is_finite_set(power_set(power_set({1})))`.
    pub fn verify_is_finite_set_with_builtin_strategy(
        &mut self,
        fact: &IsFiniteSetFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let mut child_results = Vec::new();
        let reason = match &fact.set {
            Obj::FnRange(fn_range) => {
                let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                if body.set_bound_parameters.number_of_params() != 1 {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                let Some(domain) = body.set_bound_parameters.first() else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                let child =
                    self.new_is_finite_set_fact(domain.set_obj().clone(), fact.line_file.clone());
                let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                child_results.push(result);
                "finite-set strategy: range of a function with finite domain"
            }
            Obj::PowerSet(power_set) => {
                let child = self
                    .new_is_finite_set_fact(power_set.set.as_ref().clone(), fact.line_file.clone());
                let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                child_results.push(result);
                "finite-set strategy: power set of a finite set"
            }
            Obj::SetBuilder(set_builder) => {
                let child = self.new_is_finite_set_fact(
                    set_builder.param_set.as_ref().clone(),
                    fact.line_file.clone(),
                );
                let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                child_results.push(result);
                "finite-set strategy: set-builder over a finite base"
            }
            Obj::Union(union) => {
                for set in [union.left.as_ref(), union.right.as_ref()] {
                    let child = self.new_is_finite_set_fact(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                    if !result.is_success() {
                        return Ok(UnknownGenericStmtResult::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: union of finite sets"
            }
            Obj::Intersect(intersect) => {
                for set in [intersect.left.as_ref(), intersect.right.as_ref()] {
                    let child = self.new_is_finite_set_fact(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                    if !result.is_success() {
                        return Ok(UnknownGenericStmtResult::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: intersection of finite sets"
            }
            Obj::SetMinus(set_minus) => {
                let child = self.new_is_finite_set_fact(
                    set_minus.left.as_ref().clone(),
                    fact.line_file.clone(),
                );
                let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                child_results.push(result);
                "finite-set strategy: subset of a finite left operand"
            }
            Obj::Cart(cart) => {
                for set in &cart.args {
                    let child =
                        self.new_is_finite_set_fact(set.as_ref().clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child, verify_state)?;
                    if !result.is_success() {
                        return Ok(UnknownGenericStmtResult::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: finite Cartesian factors"
            }
            _ => return Ok(UnknownGenericStmtResult::new().into()),
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyIsFiniteSetWithBuiltinStrategy,
                ),
                child_results,
            )
            .into(),
        )
    }

    fn verify_is_finite_set_strategy_child(
        &mut self,
        fact: &IsFiniteSetFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let atomic_fact: AtomicFact = fact.clone().into();
        let direct = self.verify_non_equational_atomic_fact_with_bounded_builtin_routes(
            &atomic_fact,
            verify_state,
        )?;
        if direct.is_success() {
            return self.complete_atomic_fact_proof_result(&atomic_fact, direct, verify_state);
        }
        let proof = self.verify_is_finite_set_with_builtin_strategy(fact, verify_state)?;
        self.complete_atomic_fact_proof_result(&atomic_fact, proof, verify_state)
    }

    // Nonemptiness is structural only for constructors whose witnesses come from their
    // immediate parts. Intersections and filtered sets deliberately do not participate.
    pub fn verify_is_nonempty_set_with_builtin_strategy(
        &mut self,
        fact: &IsNonemptySetFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match &fact.set {
            // An integer closed range is nonempty exactly when its endpoints are ordered.
            // Example: `2 <= n` proves `$is_nonempty_set(closed_range(1, n))`.
            Obj::ClosedRange(closed_range) => {
                let endpoint_order: AtomicFact = self
                    .new_less_equal_fact(
                        closed_range.start.as_ref().clone(),
                        closed_range.end.as_ref().clone(),
                        fact.line_file.clone(),
                    )
                    .into();
                let result = self.verify_builtin_strategy_child(&endpoint_order, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: closed integer range has ordered endpoints"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyIsNonemptySetWithBuiltinStrategy01),
                        vec![result],
                    )
                    .into(),
                )
            }
            // An integer half-open range is nonempty exactly when its start is below its end.
            // Example: `2 <= n` proves `$is_nonempty_set(range(1, n))`.
            Obj::Range(range) => {
                let endpoint_order: AtomicFact = self
                    .new_less_fact(
                        range.start.as_ref().clone(),
                        range.end.as_ref().clone(),
                        fact.line_file.clone(),
                    )
                    .into();
                let result = self.verify_builtin_strategy_child(&endpoint_order, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: half-open integer range has strictly ordered endpoints"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyIsNonemptySetWithBuiltinStrategy02),
                        vec![result],
                    )
                    .into(),
                )
            }
            // A finite real interval needs weak endpoint order only when both ends are closed;
            // any open endpoint requires strict order. Examples: `'[a, b]` uses `a <= b`,
            // while `'(a, b]` uses `a < b`.
            Obj::IntervalObj(interval) => {
                let both_closed = interval.left_closed() && interval.right_closed();
                let endpoint_order: AtomicFact = if both_closed {
                    self.new_less_equal_fact(
                        interval.start().clone(),
                        interval.end().clone(),
                        fact.line_file.clone(),
                    )
                    .into()
                } else {
                    self.new_less_fact(
                        interval.start().clone(),
                        interval.end().clone(),
                        fact.line_file.clone(),
                    )
                    .into()
                };
                let result = self.verify_builtin_strategy_child(&endpoint_order, verify_state)?;
                if !result.is_success() {
                    return Ok(UnknownGenericStmtResult::new().into());
                }
                let reason = if both_closed {
                    "nonempty-set strategy: closed real interval has weakly ordered endpoints"
                } else {
                    "nonempty-set strategy: real interval with an open endpoint has strictly ordered endpoints"
                };
                Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        reason.to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyIsNonemptySetWithBuiltinStrategy03),
                        vec![result],
                    )
                    .into(),
                )
            }
            Obj::Union(union) => {
                for set in [union.left.as_ref(), union.right.as_ref()] {
                    let child = self.new_is_nonempty_set_fact(set.clone(), fact.line_file.clone());
                    let result =
                        self.verify_is_nonempty_set_strategy_child(&child, verify_state)?;
                    if result.is_success() {
                        return Ok(
                            SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                                fact.clone().into(),
                                "nonempty-set strategy: a union has a nonempty side".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyIsNonemptySetWithBuiltinStrategy04),
                                vec![result],
                            )
                            .into(),
                        );
                    }
                }
                Ok(UnknownGenericStmtResult::new().into())
            }
            Obj::Cart(cart) => {
                let mut results = Vec::with_capacity(cart.args.len());
                for set in &cart.args {
                    let child =
                        self.new_is_nonempty_set_fact(set.as_ref().clone(), fact.line_file.clone());
                    let result =
                        self.verify_is_nonempty_set_strategy_child(&child, verify_state)?;
                    if !result.is_success() {
                        return Ok(UnknownGenericStmtResult::new().into());
                    }
                    results.push(result);
                }
                Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: all Cartesian factors are nonempty".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyIsNonemptySetWithBuiltinStrategy05),
                        results,
                    )
                    .into(),
                )
            }
            Obj::FnSet(fn_set) => self.verify_nonempty_constructor_strategy(
                fact,
                fn_set.body.ret_set.as_ref(),
                "nonempty-set strategy: function codomain is nonempty",
                verify_state,
            ),
            Obj::AnonymousFn(function) => self.verify_nonempty_constructor_strategy(
                fact,
                function.body.ret_set.as_ref(),
                "nonempty-set strategy: anonymous-function codomain is nonempty",
                verify_state,
            ),
            Obj::FiniteSeqSet(sequence) => self.verify_nonempty_constructor_strategy(
                fact,
                sequence.set.as_ref(),
                "nonempty-set strategy: finite-sequence codomain is nonempty",
                verify_state,
            ),
            Obj::SeqSet(sequence) => self.verify_nonempty_constructor_strategy(
                fact,
                sequence.set.as_ref(),
                "nonempty-set strategy: sequence codomain is nonempty",
                verify_state,
            ),
            Obj::MatrixSet(matrix) => self.verify_nonempty_constructor_strategy(
                fact,
                matrix.set.as_ref(),
                "nonempty-set strategy: matrix entry set is nonempty",
                verify_state,
            ),
            _ => Ok(UnknownGenericStmtResult::new().into()),
        }
    }

    fn verify_nonempty_constructor_strategy(
        &mut self,
        fact: &IsNonemptySetFact,
        child_set: &Obj,
        reason: &str,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let child = self.new_is_nonempty_set_fact(child_set.clone(), fact.line_file.clone());
        let result = self.verify_is_nonempty_set_strategy_child(&child, verify_state)?;
        if !result.is_success() {
            return Ok(UnknownGenericStmtResult::new().into());
        }
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_strategy_evidence_recording_stmt(
                fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyNonemptyConstructorStrategy,
                ),
                vec![result],
            )
            .into(),
        )
    }

    fn verify_is_nonempty_set_strategy_child(
        &mut self,
        fact: &IsNonemptySetFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let atomic_fact: AtomicFact = fact.clone().into();
        let direct = self.verify_non_equational_atomic_fact_with_bounded_builtin_routes(
            &atomic_fact,
            verify_state,
        )?;
        if direct.is_success() {
            return self.complete_atomic_fact_proof_result(&atomic_fact, direct, verify_state);
        }
        let proof = self.verify_is_nonempty_set_with_builtin_strategy(fact, verify_state)?;
        self.complete_atomic_fact_proof_result(&atomic_fact, proof, verify_state)
    }
}
