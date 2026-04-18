use crate::prelude::*;
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

impl Runtime {
    // Order atom with exactly one side a resolved numeric literal: may store `0 < x` or `x <= 0` for the other side.
    // Example: `2 < a` (literal left) infers `0 < a` when the constant branch applies; `b < 0` pairs use the `<= 0` path on `b`.
    pub fn infer_numeric_order_sign_from_order_atomic(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => self.infer_numeric_order_sign_greater_equal(f),
            AtomicFact::GreaterFact(f) => self.infer_numeric_order_sign_greater(f),
            AtomicFact::LessEqualFact(f) => self.infer_numeric_order_sign_less_equal(f),
            AtomicFact::LessFact(f) => self.infer_numeric_order_sign_less(f),
            _ => Ok(InferResult::new()),
        }
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
        self.store_fact_without_well_defined_verified_and_infer(fact_to_store)
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
        self.store_fact_without_well_defined_verified_and_infer(fact_to_store)
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
