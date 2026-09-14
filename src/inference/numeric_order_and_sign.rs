use crate::prelude::*;
use crate::verification::{compare_normalized_number_str_to_zero, NumberCompareResult};

impl Runtime {
    // Order atom with exactly one side a resolved numeric literal: may store `0 < x` or `x <= 0` for the other side.
    // Example: `2 < a` (literal left) infers `0 < a` when the constant branch applies; `b < 0` pairs use the `<= 0` path on `b`.
    //
    // Additionally: comparing `x` with `0` on the **right** (`x < 0`, `x <= 0`, …) may infer the
    // opposite sign on `(-1)*x` (e.g. `x < 0` => `(-1)*x >= 0`) when `x` is known real. We do **not**
    // infer from `0 < x` (literal 0 on the left), and unknown carriers simply receive no flipped fact.
    // Skips operands already of the form `(-1)*u` so we do not chain `(-1)*((-1)*n)`.
    pub(in crate::inference) fn infer_numeric_order_sign_from_order_atomic(
        &mut self,
        atomic_fact: &AtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let (left, right, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            AtomicFact::GreaterFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::LessEqualFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::LessFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            _ => return Ok(SuccessInferResult::new()),
        };
        let verify_state = VerifyState::initial().with_inference_state(inference_state);
        if self
            .verify_objects_are_known_reals(&[&left, &right], &line_file, &verify_state)?
            .is_none()
        {
            return Ok(SuccessInferResult::new());
        }
        let mut acc = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                self.infer_numeric_order_sign_greater_equal(f, inference_state)
            }
            AtomicFact::GreaterFact(f) => self.infer_numeric_order_sign_greater(f, inference_state),
            AtomicFact::LessEqualFact(f) => {
                self.infer_numeric_order_sign_less_equal(f, inference_state)
            }
            AtomicFact::LessFact(f) => self.infer_numeric_order_sign_less(f, inference_state),
            _ => Ok(SuccessInferResult::new()),
        }?;
        let flip = self.infer_flip_mul_minus_one_order_vs_zero(atomic_fact, inference_state)?;
        acc.new_infer_result_inside(flip);
        Ok(acc)
    }

    fn order_flip_infer_operand_ok(&self, x: &Obj) -> bool {
        self.peel_mul_by_literal_neg_one(x).is_none()
    }

    fn obj_mul_literal_neg_one(&self, x: Obj) -> Obj {
        Mul::new(Number::new("-1".to_string()).into(), x).into()
    }

    fn atomic_fact_infer_opposite_mul_minus_one_target(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<AtomicFact> {
        let z = Number::new("0".to_string()).into();
        match atomic_fact {
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if !self.order_flip_infer_operand_ok(&f.left) {
                    return None;
                }
                Some(
                    self.new_greater_equal_fact(
                        self.obj_mul_literal_neg_one(f.left.clone()),
                        z,
                        f.line_file.clone(),
                    )
                    .into(),
                )
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if !self.order_flip_infer_operand_ok(&f.left) {
                    return None;
                }
                Some(
                    self.new_greater_equal_fact(
                        self.obj_mul_literal_neg_one(f.left.clone()),
                        z,
                        f.line_file.clone(),
                    )
                    .into(),
                )
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if !self.order_flip_infer_operand_ok(&f.left) {
                    return None;
                }
                Some(
                    self.new_less_fact(
                        self.obj_mul_literal_neg_one(f.left.clone()),
                        z,
                        f.line_file.clone(),
                    )
                    .into(),
                )
            }
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if !self.order_flip_infer_operand_ok(&f.left) {
                    return None;
                }
                Some(
                    self.new_less_equal_fact(
                        self.obj_mul_literal_neg_one(f.left.clone()),
                        z,
                        f.line_file.clone(),
                    )
                    .into(),
                )
            }
            // No infer when literal `0` is on the **left** (e.g. `0 < a` from `a > k`, k>0).
            // Flipping would store `(-1)*a < 0`, which requires `a $in R` for well-defined; parameters in a
            // finite list or other scopes may not have that yet.
            _ => None,
        }
    }

    fn infer_flip_mul_minus_one_order_vs_zero(
        &mut self,
        atomic_fact: &AtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let Some(inferred_atomic) =
            self.atomic_fact_infer_opposite_mul_minus_one_target(atomic_fact)
        else {
            return Ok(SuccessInferResult::new());
        };
        let source_operand = match atomic_fact {
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.right) => f.left.clone(),
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.right) => f.left.clone(),
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.right) => f.left.clone(),
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                f.left.clone()
            }
            _ => return Ok(SuccessInferResult::new()),
        };
        let source_in_r: AtomicFact = self
            .new_in_fact(
                source_operand,
                StandardSet::R.into(),
                atomic_fact.line_file(),
            )
            .into();
        let verify_state = VerifyState::initial().with_inference_state(inference_state);
        let source_in_r_result = self.verify_atomic_except_equality_with_bounded_builtin_routes(
            &source_in_r,
            &verify_state,
        )?;
        if !source_in_r_result.is_success() {
            return Ok(SuccessInferResult::new());
        }
        let fact_to_store: Fact = inferred_atomic.clone().into();
        let mut result = SuccessInferResult::new();
        result.new_fact(&fact_to_store);
        // Do not run full `verify_fact_well_defined_result` here: WD for the flipped atom can re-enter
        // `verify_fn_obj_well_defined` (e.g. intermediate `… $in N`) and this infer path again,
        // causing mutual recursion / stack overflow (see `examples/_internal/regression/opaque_euler_phi_interface.lit`).
        let conclusion_infers = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                inferred_atomic,
                InferReason::StoredFact.store_reason(),
                inference_state,
            )
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer opposite sign mul (-1): failed to store inferred order fact".to_string(),
                    atomic_fact.line_file(),
                    Some(previous_error),
                    vec![],
                )))
            })?;
        result.add_rule_application_preserving_conclusion_result_structure(
            InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero,
            vec![atomic_fact.clone().into()],
            vec![SuccessStoreFactResult::new(
                fact_to_store,
                conclusion_infers,
            )],
        );
        Ok(result)
    }

    fn infer_numeric_order_sign_greater_equal(
        &mut self,
        f: &GreaterEqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(SuccessInferResult::new()),
            (None, Some(k)) => {
                // L >= k and k > 0 => store `0 < L`
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(
                        f.left.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
            (Some(k), None) => {
                // k >= R => R <= k; k < 0 => R <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less
                ) {
                    self.infer_store_le_zero(
                        f.right.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_greater(
        &mut self,
        f: &GreaterFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(SuccessInferResult::new()),
            (None, Some(k)) => {
                // L > k and k > 0 => store `0 < L`. If k == 0 the premise is already `0 < L`; do not re-store (avoids infinite infer).
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(
                        f.left.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
            (Some(k), None) => {
                // k > R => R < k; k <= 0 => R <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) {
                    self.infer_store_le_zero(
                        f.right.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_less_equal(
        &mut self,
        f: &LessEqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(SuccessInferResult::new()),
            (None, Some(k)) => {
                // L <= k and k < 0 => L <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less
                ) {
                    self.infer_store_le_zero(
                        f.left.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
            (Some(k), None) => {
                // k <= R => R >= k; k > 0 => store `0 < R`
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(
                        f.right.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_less(
        &mut self,
        f: &LessFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(SuccessInferResult::new()),
            (None, Some(k)) => {
                // L < k and k <= 0 => L <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    self.infer_strict_order_compared_to_zero_implies_weak_order(f, inference_state)
                } else if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less
                ) {
                    self.infer_store_le_zero(
                        f.left.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
            (Some(k), None) => {
                // k < R and k > 0 => store `0 < R`. If k == 0, premise is already `0 < R`; do not re-store (avoids infinite infer).
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(
                        f.right.clone(),
                        f.line_file.clone(),
                        f.clone().into(),
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
        }
    }

    fn infer_strict_order_compared_to_zero_implies_weak_order(
        &mut self,
        source: &LessFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let conclusion_atomic: AtomicFact = self
            .new_less_equal_fact(
                source.left.clone(),
                Number::new("0".to_string()).into(),
                source.line_file.clone(),
            )
            .into();
        let conclusion_fact: Fact = conclusion_atomic.clone().into();
        let mut result = SuccessInferResult::new();
        result.new_fact(&conclusion_fact);
        let conclusion_infers = self
            .store_typed_inference_conclusion_and_infer(conclusion_fact.clone(), inference_state)?;
        result.add_rule_application_preserving_conclusion_result_structure(
            InferRule::StrictOrderComparedToZeroImpliesWeakOrder,
            vec![source.clone().into()],
            vec![SuccessStoreFactResult::new(
                conclusion_fact,
                conclusion_infers,
            )],
        );
        Ok(result)
    }

    fn infer_store_gt_zero(
        &mut self,
        x: Obj,
        line_file: LineFile,
        source: AtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let conclusion_atomic: AtomicFact = self
            .new_less_fact(Number::new("0".to_string()).into(), x, line_file.clone())
            .into();
        let fact_to_store: Fact = conclusion_atomic.clone().into();
        let mut result = SuccessInferResult::new();
        let conclusion_infers = self
            .store_typed_inference_conclusion_and_infer(fact_to_store.clone(), inference_state)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer numeric order sign: failed to store inferred (0 < x) bound".to_string(),
                    line_file,
                    Some(previous_error),
                    vec![],
                )))
            })?;
        result.add_rule_application_preserving_conclusion_result_structure(
            InferRule::NumericOrderBoundImpliesZeroSign,
            vec![source.into()],
            vec![SuccessStoreFactResult::new(
                fact_to_store,
                conclusion_infers,
            )],
        );
        Ok(result)
    }

    fn infer_store_le_zero(
        &mut self,
        x: Obj,
        line_file: LineFile,
        source: AtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let conclusion_atomic: AtomicFact = self
            .new_less_equal_fact(x, Number::new("0".to_string()).into(), line_file.clone())
            .into();
        let fact_to_store: Fact = conclusion_atomic.clone().into();
        let mut result = SuccessInferResult::new();
        let conclusion_infers = self
            .store_typed_inference_conclusion_and_infer(fact_to_store.clone(), inference_state)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer numeric order sign: failed to store inferred <= 0 bound".to_string(),
                    line_file,
                    Some(previous_error),
                    vec![],
                )))
            })?;
        result.add_rule_application_preserving_conclusion_result_structure(
            InferRule::NumericOrderBoundImpliesZeroSign,
            vec![source.into()],
            vec![SuccessStoreFactResult::new(
                fact_to_store,
                conclusion_infers,
            )],
        );
        Ok(result)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/inference/numeric_order_and_sign/tests.rs"]
mod tests;
