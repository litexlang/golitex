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
