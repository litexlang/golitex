use crate::prelude::*;
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

impl Runtime {
    // Order atom with exactly one side a resolved numeric literal: may store `0 < x` or `x <= 0` for the other side.
    // Example: `2 < a` (literal left) infers `0 < a` when the constant branch applies; `b < 0` pairs use the `<= 0` path on `b`.
    //
    // Additionally: comparing `x` with `0` on the **right** (`x < 0`, `x <= 0`, …) may infer the
    // opposite sign on `(-1)*x` (e.g. `x < 0` => `(-1)*x >= 0`). We do **not** infer from `0 < x`
    // (literal 0 on the left): that would require `x $in R` to store `(-1)*x < 0`, which often
    // fails for scoped parameters. Verification builtins still prove such goals when needed.
    // Skips operands already of the form `(-1)*u` so we do not chain `(-1)*((-1)*n)`.
    pub fn infer_numeric_order_sign_from_order_atomic(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut acc = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => self.infer_numeric_order_sign_greater_equal(f),
            AtomicFact::GreaterFact(f) => self.infer_numeric_order_sign_greater(f),
            AtomicFact::LessEqualFact(f) => self.infer_numeric_order_sign_less_equal(f),
            AtomicFact::LessFact(f) => self.infer_numeric_order_sign_less(f),
            _ => Ok(InferResult::new()),
        }?;
        let flip = self.infer_flip_mul_minus_one_order_vs_zero(atomic_fact)?;
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
                    GreaterEqualFact::new(
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
                    GreaterEqualFact::new(
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
                    LessFact::new(
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
                    LessEqualFact::new(
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
    ) -> Result<InferResult, RuntimeError> {
        let Some(inferred_atomic) =
            self.atomic_fact_infer_opposite_mul_minus_one_target(atomic_fact)
        else {
            return Ok(InferResult::new());
        };
        let fact_to_store: Fact = inferred_atomic.clone().into();
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&fact_to_store);
        // Do not run full `verify_fact_well_defined` here: well-defined for the flipped atom can re-enter
        // `verify_fn_obj_well_defined` (e.g. intermediate `… $in N`) and this infer path again,
        // causing mutual recursion / stack overflow (see `examples/euler_phi.lit`).
        let inner = self
            .store_atomic_fact_without_well_defined_verified_and_infer(inferred_atomic)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer opposite sign mul (-1): failed to store inferred order fact".to_string(),
                    atomic_fact.line_file(),
                    Some(previous_error),
                    vec![],
                )))
            })?;
        infer_result.new_infer_result_inside(inner);
        Ok(infer_result)
    }

    fn infer_numeric_order_sign_greater_equal(
        &mut self,
        f: &GreaterEqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(InferResult::new()),
            (None, Some(k)) => {
                // L >= k and k > 0 => store `0 < L`
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(f.left.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
            (Some(k), None) => {
                // k >= R => R <= k; k < 0 => R <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less
                ) {
                    self.infer_store_le_zero(f.right.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_greater(
        &mut self,
        f: &GreaterFact,
    ) -> Result<InferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(InferResult::new()),
            (None, Some(k)) => {
                // L > k and k > 0 => store `0 < L`. If k == 0 the premise is already `0 < L`; do not re-store (avoids infinite infer).
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(f.left.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
            (Some(k), None) => {
                // k > R => R < k; k <= 0 => R <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) {
                    self.infer_store_le_zero(f.right.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_less_equal(
        &mut self,
        f: &LessEqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(InferResult::new()),
            (None, Some(k)) => {
                // L <= k and k < 0 => L <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less
                ) {
                    self.infer_store_le_zero(f.left.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
            (Some(k), None) => {
                // k <= R => R >= k; k > 0 => store `0 < R`
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(f.right.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
        }
    }

    fn infer_numeric_order_sign_less(&mut self, f: &LessFact) -> Result<InferResult, RuntimeError> {
        let left_num = self.resolve_obj_to_number(&f.left);
        let right_num = self.resolve_obj_to_number(&f.right);
        match (left_num, right_num) {
            (Some(_), Some(_)) | (None, None) => Ok(InferResult::new()),
            (None, Some(k)) => {
                // L < k and k <= 0 => L <= 0
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Less | NumberCompareResult::Equal
                ) {
                    self.infer_store_le_zero(f.left.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
            (Some(k), None) => {
                // k < R and k > 0 => store `0 < R`. If k == 0, premise is already `0 < R`; do not re-store (avoids infinite infer).
                if matches!(
                    compare_normalized_number_str_to_zero(&k.normalized_value),
                    NumberCompareResult::Greater
                ) {
                    self.infer_store_gt_zero(f.right.clone(), f.line_file.clone())
                } else {
                    Ok(InferResult::new())
                }
            }
        }
    }

    fn infer_store_gt_zero(
        &mut self,
        x: Obj,
        line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        let fact_to_store =
            LessFact::new(Number::new("0".to_string()).into(), x, line_file.clone()).into();
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&fact_to_store);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact_to_store)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer numeric order sign: failed to store inferred (0 < x) bound".to_string(),
                    line_file,
                    Some(previous_error),
                    vec![],
                )))
            })?;
        Ok(infer_result)
    }

    fn infer_store_le_zero(
        &mut self,
        x: Obj,
        line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        let fact_to_store =
            LessEqualFact::new(x, Number::new("0".to_string()).into(), line_file.clone()).into();
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&fact_to_store);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact_to_store)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "infer numeric order sign: failed to store inferred <= 0 bound".to_string(),
                    line_file,
                    Some(previous_error),
                    vec![],
                )))
            })?;
        Ok(infer_result)
    }
}

#[cfg(test)]
mod tests {
    use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

    #[test]
    fn compare_to_zero_matches_expectations() {
        assert!(matches!(
            compare_normalized_number_str_to_zero("1"),
            NumberCompareResult::Greater
        ));
        assert!(matches!(
            compare_normalized_number_str_to_zero("0"),
            NumberCompareResult::Equal
        ));
        assert!(matches!(
            compare_normalized_number_str_to_zero("-2"),
            NumberCompareResult::Less
        ));
    }
}
