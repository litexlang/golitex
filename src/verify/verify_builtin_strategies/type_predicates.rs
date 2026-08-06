use crate::prelude::*;

impl Runtime {
    // Repeatedly applies finite-set constructor rules to strictly smaller set expressions.
    // Example: `$is_finite_set(power_set(power_set({1})))`.
    pub(crate) fn verify_is_finite_set_with_builtin_strategy(
        &mut self,
        fact: &IsFiniteSetFact,
    ) -> Result<StmtResult, RuntimeError> {
        let mut child_results = Vec::new();
        let reason = match &fact.set {
            Obj::FnRange(fn_range) => {
                let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
                    return Ok(StmtUnknown::new().into());
                };
                if body.params_def_with_set.number_of_params() != 1 {
                    return Ok(StmtUnknown::new().into());
                }
                let Some(domain) = body.params_def_with_set.first() else {
                    return Ok(StmtUnknown::new().into());
                };
                let child = IsFiniteSetFact::new(domain.set_obj().clone(), fact.line_file.clone());
                let result = self.verify_is_finite_set_strategy_child(&child)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                child_results.push(result);
                "finite-set strategy: range of a function with finite domain"
            }
            Obj::PowerSet(power_set) => {
                let child =
                    IsFiniteSetFact::new(power_set.set.as_ref().clone(), fact.line_file.clone());
                let result = self.verify_is_finite_set_strategy_child(&child)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                child_results.push(result);
                "finite-set strategy: power set of a finite set"
            }
            Obj::SetBuilder(set_builder) => {
                let child = IsFiniteSetFact::new(
                    set_builder.param_set.as_ref().clone(),
                    fact.line_file.clone(),
                );
                let result = self.verify_is_finite_set_strategy_child(&child)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                child_results.push(result);
                "finite-set strategy: set-builder over a finite base"
            }
            Obj::Union(union) => {
                for set in [union.left.as_ref(), union.right.as_ref()] {
                    let child = IsFiniteSetFact::new(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child)?;
                    if !result.is_true() {
                        return Ok(StmtUnknown::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: union of finite sets"
            }
            Obj::Intersect(intersect) => {
                for set in [intersect.left.as_ref(), intersect.right.as_ref()] {
                    let child = IsFiniteSetFact::new(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child)?;
                    if !result.is_true() {
                        return Ok(StmtUnknown::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: intersection of finite sets"
            }
            Obj::SetMinus(set_minus) => {
                let child =
                    IsFiniteSetFact::new(set_minus.left.as_ref().clone(), fact.line_file.clone());
                let result = self.verify_is_finite_set_strategy_child(&child)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                child_results.push(result);
                "finite-set strategy: subset of a finite left operand"
            }
            Obj::SetDiff(set_diff) => {
                for set in [set_diff.left.as_ref(), set_diff.right.as_ref()] {
                    let child = IsFiniteSetFact::new(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child)?;
                    if !result.is_true() {
                        return Ok(StmtUnknown::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: symmetric difference of finite sets"
            }
            Obj::Cart(cart) => {
                for set in &cart.args {
                    let child = IsFiniteSetFact::new(set.as_ref().clone(), fact.line_file.clone());
                    let result = self.verify_is_finite_set_strategy_child(&child)?;
                    if !result.is_true() {
                        return Ok(StmtUnknown::new().into());
                    }
                    child_results.push(result);
                }
                "finite-set strategy: finite Cartesian factors"
            }
            _ => return Ok(StmtUnknown::new().into()),
        };

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                reason.to_string(),
                child_results,
            )
            .into(),
        )
    }

    fn verify_is_finite_set_strategy_child(
        &mut self,
        fact: &IsFiniteSetFact,
    ) -> Result<StmtResult, RuntimeError> {
        let atomic_fact: AtomicFact = fact.clone().into();
        let direct = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(&atomic_fact)?;
        if direct.is_true() {
            return Ok(direct);
        }
        self.verify_is_finite_set_with_builtin_strategy(fact)
    }

    // Nonemptiness is structural only for constructors whose witnesses come from their
    // immediate parts. Intersections and filtered sets deliberately do not participate.
    pub(crate) fn verify_is_nonempty_set_with_builtin_strategy(
        &mut self,
        fact: &IsNonemptySetFact,
    ) -> Result<StmtResult, RuntimeError> {
        match &fact.set {
            // An integer closed range is nonempty exactly when its endpoints are ordered.
            // Example: `2 <= n` proves `$is_nonempty_set(closed_range(1, n))`.
            Obj::ClosedRange(closed_range) => {
                let endpoint_order: AtomicFact = LessEqualFact::new(
                    closed_range.start.as_ref().clone(),
                    closed_range.end.as_ref().clone(),
                    fact.line_file.clone(),
                )
                .into();
                let result = self.verify_builtin_strategy_child(&endpoint_order)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: closed integer range has ordered endpoints"
                            .to_string(),
                        vec![result],
                    )
                    .into(),
                )
            }
            // An integer half-open range is nonempty exactly when its start is below its end.
            // Example: `2 <= n` proves `$is_nonempty_set(range(1, n))`.
            Obj::Range(range) => {
                let endpoint_order: AtomicFact = LessFact::new(
                    range.start.as_ref().clone(),
                    range.end.as_ref().clone(),
                    fact.line_file.clone(),
                )
                .into();
                let result = self.verify_builtin_strategy_child(&endpoint_order)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: half-open integer range has strictly ordered endpoints"
                            .to_string(),
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
                    LessEqualFact::new(
                        interval.start().clone(),
                        interval.end().clone(),
                        fact.line_file.clone(),
                    )
                    .into()
                } else {
                    LessFact::new(
                        interval.start().clone(),
                        interval.end().clone(),
                        fact.line_file.clone(),
                    )
                    .into()
                };
                let result = self.verify_builtin_strategy_child(&endpoint_order)?;
                if !result.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                let reason = if both_closed {
                    "nonempty-set strategy: closed real interval has weakly ordered endpoints"
                } else {
                    "nonempty-set strategy: real interval with an open endpoint has strictly ordered endpoints"
                };
                Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        reason.to_string(),
                        vec![result],
                    )
                    .into(),
                )
            }
            Obj::Union(union) => {
                for set in [union.left.as_ref(), union.right.as_ref()] {
                    let child = IsNonemptySetFact::new(set.clone(), fact.line_file.clone());
                    let result = self.verify_is_nonempty_set_strategy_child(&child)?;
                    if result.is_true() {
                        return Ok(
                            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                                fact.clone().into(),
                                "nonempty-set strategy: a union has a nonempty side".to_string(),
                                vec![result],
                            )
                            .into(),
                        );
                    }
                }
                Ok(StmtUnknown::new().into())
            }
            Obj::Cart(cart) => {
                let mut results = Vec::with_capacity(cart.args.len());
                for set in &cart.args {
                    let child =
                        IsNonemptySetFact::new(set.as_ref().clone(), fact.line_file.clone());
                    let result = self.verify_is_nonempty_set_strategy_child(&child)?;
                    if !result.is_true() {
                        return Ok(StmtUnknown::new().into());
                    }
                    results.push(result);
                }
                Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        fact.clone().into(),
                        "nonempty-set strategy: all Cartesian factors are nonempty".to_string(),
                        results,
                    )
                    .into(),
                )
            }
            Obj::FnSet(fn_set) => self.verify_nonempty_constructor_strategy(
                fact,
                fn_set.body.ret_set.as_ref(),
                "nonempty-set strategy: function codomain is nonempty",
            ),
            Obj::AnonymousFn(function) => self.verify_nonempty_constructor_strategy(
                fact,
                function.body.ret_set.as_ref(),
                "nonempty-set strategy: anonymous-function codomain is nonempty",
            ),
            Obj::FiniteSeqSet(sequence) => self.verify_nonempty_constructor_strategy(
                fact,
                sequence.set.as_ref(),
                "nonempty-set strategy: finite-sequence codomain is nonempty",
            ),
            Obj::SeqSet(sequence) => self.verify_nonempty_constructor_strategy(
                fact,
                sequence.set.as_ref(),
                "nonempty-set strategy: sequence codomain is nonempty",
            ),
            Obj::MatrixSet(matrix) => self.verify_nonempty_constructor_strategy(
                fact,
                matrix.set.as_ref(),
                "nonempty-set strategy: matrix entry set is nonempty",
            ),
            _ => Ok(StmtUnknown::new().into()),
        }
    }

    fn verify_nonempty_constructor_strategy(
        &mut self,
        fact: &IsNonemptySetFact,
        child_set: &Obj,
        reason: &str,
    ) -> Result<StmtResult, RuntimeError> {
        let child = IsNonemptySetFact::new(child_set.clone(), fact.line_file.clone());
        let result = self.verify_is_nonempty_set_strategy_child(&child)?;
        if !result.is_true() {
            return Ok(StmtUnknown::new().into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                fact.clone().into(),
                reason.to_string(),
                vec![result],
            )
            .into(),
        )
    }

    fn verify_is_nonempty_set_strategy_child(
        &mut self,
        fact: &IsNonemptySetFact,
    ) -> Result<StmtResult, RuntimeError> {
        let atomic_fact: AtomicFact = fact.clone().into();
        let direct = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(&atomic_fact)?;
        if direct.is_true() {
            return Ok(direct);
        }
        self.verify_is_nonempty_set_with_builtin_strategy(fact)
    }
}
