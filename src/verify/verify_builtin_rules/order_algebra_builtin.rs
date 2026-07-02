// Structural order on R (+, -, *, /) moved from Lit `BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES`.
// Called from `verify_order_atomic_fact_numeric_builtin_only` before the `0 <=` cone rules.
//
// Addition (weak): `a <= b + c` from (`a <= b` and `0 <= c`) or (`a <= c` and `0 <= b`); and
// `a <= a + b` from `0 <= b`. Strict: `a < b + c` from (`a < b` and `0 <= c`) or (`a < c` and `0 <= b`).
// Subtraction: order is preserved by subtracting the same term; subtracting a nonnegative term
// cannot increase a value; and subtractors can move across an inequality as addends.
//
// Multiplication monotonicity on R: for fixed k, t |-> k*t preserves non-strict order when 0 <= k
// (a <= b => k*a <= k*b with k on the same side of both products), reverses when k <= 0 (b <= a =>
// k*a <= k*b). Strict: 0 < k and a < b => k*a < k*b; k < 0 and b < a => k*a < k*b.

use super::number_compare::normalized_decimal_string_is_even_integer;
use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_order_algebra_structural_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => self.try_less_equal_algebra(f, atomic_fact),
            AtomicFact::LessFact(f) => self.try_less_algebra(f, atomic_fact),
            _ => Ok(None),
        }
    }

    fn verify_order_subgoal(&mut self, fact: AtomicFact) -> Result<StmtResult, RuntimeError> {
        let mut result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fact)?;
        if !result.is_true() {
            result = self.verify_order_atomic_fact_numeric_builtin_only(&fact)?;
        }
        Ok(result)
    }

    pub(crate) fn literal_zero_obj() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    pub(crate) fn literal_one_obj() -> Obj {
        Obj::Number(Number::new("1".to_string()))
    }

    fn obj_is_positive_integer_number(obj: &Obj) -> bool {
        let Obj::Number(number) = obj else {
            return false;
        };
        let Ok(integer) = number.normalized_value.parse::<i128>() else {
            return false;
        };
        integer > 0
    }

    fn verify_obj_in_n_pos_subgoal(
        &mut self,
        obj: &Obj,
        lf: &LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let in_n_pos: AtomicFact =
            InFact::new(obj.clone(), StandardSet::NPos.into(), lf.clone()).into();
        self.verify_non_equational_known_then_builtin_rules_only(
            &in_n_pos,
            &VerifyState::new(0, true),
        )
    }

    fn obj_is_nonnegative_integer_number(obj: &Obj) -> bool {
        match Self::integer_value_of_number_obj(obj) {
            Some(integer) => integer >= 0,
            None => false,
        }
    }

    fn integer_value_of_number_obj(obj: &Obj) -> Option<i128> {
        let Obj::Number(number) = obj else {
            return None;
        };
        number.normalized_value.parse::<i128>().ok()
    }

    fn obj_plus_nonnegative_integer_offset(obj: &Obj, offset: i128) -> Obj {
        if offset == 0 {
            return obj.clone();
        }
        if let Some(base) = Self::integer_value_of_number_obj(obj) {
            if let Some(sum) = base.checked_add(offset) {
                return Number::new(sum.to_string()).into();
            }
        }
        Add::new(obj.clone(), Number::new(offset.to_string()).into()).into()
    }

    fn obj_is_positive_odd_integer_number(obj: &Obj) -> bool {
        let Obj::Number(number) = obj else {
            return false;
        };
        let Ok(integer) = number.normalized_value.parse::<i128>() else {
            return false;
        };
        integer > 0 && integer % 2 == 1
    }

    fn obj_is_positive_even_integer_number(obj: &Obj) -> bool {
        let Obj::Number(number) = obj else {
            return false;
        };
        if !normalized_decimal_string_is_even_integer(&number.normalized_value) {
            return false;
        };
        let Ok(integer) = number.normalized_value.parse::<i128>() else {
            return false;
        };
        integer > 0
    }

    // k in N_pos and k % 2 = 0, or k is a positive even literal.
    fn verify_even_exponent_in_n_pos_subgoal(
        &mut self,
        exp: &Obj,
        lf: &LineFile,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        if Self::obj_is_positive_even_integer_number(exp) {
            return Ok(Some(Vec::new()));
        }
        let mut steps = Vec::new();
        let n_pos_result = self.verify_obj_in_n_pos_subgoal(exp, lf)?;
        if !n_pos_result.is_true() {
            return Ok(None);
        }
        steps.push(n_pos_result);
        let two: Obj = Number::new("2".to_string()).into();
        if self.known_mod_equals_zero(exp, &two) {
            return Ok(Some(steps));
        }
        Ok(None)
    }

    fn known_mod_equals_zero(&self, dividend: &Obj, divisor: &Obj) -> bool {
        let zero = Self::literal_zero_obj();
        let mod_obj: Obj = Mod::new(dividend.clone(), divisor.clone()).into();
        self.objs_have_same_known_equality_rc_in_some_env(&mod_obj, &zero)
    }

    // k in N_pos and k % 2 = 1, or k is a positive odd literal.
    fn verify_odd_exponent_in_n_pos_subgoal(
        &mut self,
        exp: &Obj,
        lf: &LineFile,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        if Self::obj_is_positive_odd_integer_number(exp) {
            return Ok(Some(Vec::new()));
        }
        let mut steps = Vec::new();
        let n_pos_result = self.verify_obj_in_n_pos_subgoal(exp, lf)?;
        if !n_pos_result.is_true() {
            return Ok(None);
        }
        steps.push(n_pos_result);
        let two: Obj = Number::new("2".to_string()).into();
        let one = Self::literal_one_obj();
        let mod_obj: Obj = Mod::new(exp.clone(), two).into();
        let odd_result = self.verify_objs_are_equal_known_only(&mod_obj, &one, lf.clone());
        if odd_result.is_true() {
            steps.push(odd_result);
            return Ok(Some(steps));
        }
        Ok(None)
    }

    fn objs_same_by_display(left: &Obj, right: &Obj) -> bool {
        left.to_string() == right.to_string()
    }

    fn add_common_remaining(left: &Add, right: &Add) -> Option<(Obj, Obj)> {
        let pairs = [
            (
                left.left.as_ref(),
                left.right.as_ref(),
                right.left.as_ref(),
                right.right.as_ref(),
            ),
            (
                left.left.as_ref(),
                left.right.as_ref(),
                right.right.as_ref(),
                right.left.as_ref(),
            ),
            (
                left.right.as_ref(),
                left.left.as_ref(),
                right.left.as_ref(),
                right.right.as_ref(),
            ),
            (
                left.right.as_ref(),
                left.left.as_ref(),
                right.right.as_ref(),
                right.left.as_ref(),
            ),
        ];
        for (left_common, left_remaining, right_common, right_remaining) in pairs {
            if Self::objs_same_by_display(left_common, right_common) {
                return Some((left_remaining.clone(), right_remaining.clone()));
            }
        }
        None
    }

    // a^n <= b^n from 0 <= a, a <= b, and positive integer n.
    // Example: from `0 <= a <= b`, prove `a^2 <= b^2`.
    fn try_pow_le_same_positive_integer_exponent_nonnegative_base(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let mut step_results = Vec::new();
        if !Self::obj_is_positive_integer_number(left_pow.exponent.as_ref()) {
            let exponent_result =
                self.verify_obj_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?;
            if !exponent_result.is_true() {
                return Ok(None);
            }
            step_results.push(exponent_result);
        }

        let z = Self::literal_zero_obj();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoals: [AtomicFact; 2] = [
            LessEqualFact::new(z, left_base.clone(), lf.clone()).into(),
            LessEqualFact::new(left_base.clone(), right_base.clone(), lf.clone()).into(),
        ];
        for subgoal in subgoals {
            let result = self.verify_order_subgoal(subgoal)?;
            if !result.is_true() {
                return Ok(None);
            }
            step_results.push(result);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from 0 <= a, a <= b, and positive integer n".to_string(),
                step_results,
            ),
        )))
    }

    fn collect_known_power_le_candidates(
        &self,
        left_base: &Obj,
        right_base: &Obj,
    ) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                for known_fact in known_facts_map.values() {
                    let AtomicFact::LessEqualFact(known_le) = known_fact else {
                        continue;
                    };
                    let (Obj::Pow(left_pow), Obj::Pow(right_pow)) =
                        (&known_le.left, &known_le.right)
                    else {
                        continue;
                    };
                    if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
                        continue;
                    }
                    if !Self::objs_same_by_display(left_pow.base.as_ref(), left_base) {
                        continue;
                    }
                    if !Self::objs_same_by_display(right_pow.base.as_ref(), right_base) {
                        continue;
                    }
                    candidates.push(known_fact.clone());
                }
            }
        }
        candidates
    }

    // a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N_pos.
    // Example: from `0 <= x`, `0 <= y`, `m $in N_pos`, and `x^m <= y^m`, prove `x <= y`.
    fn try_base_le_from_pow_le_same_positive_integer_exponent_nonnegative_base(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let candidates = self.collect_known_power_le_candidates(&f.left, &f.right);
        for candidate in candidates {
            let AtomicFact::LessEqualFact(power_le) = &candidate else {
                continue;
            };
            let (Obj::Pow(left_pow), Obj::Pow(_)) = (&power_le.left, &power_le.right) else {
                continue;
            };

            let exponent_result =
                self.verify_obj_in_n_pos_subgoal(left_pow.exponent.as_ref(), &f.line_file)?;
            if !exponent_result.is_true() {
                continue;
            }

            let z = Self::literal_zero_obj();
            let left_nonnegative: AtomicFact =
                LessEqualFact::new(z.clone(), f.left.clone(), f.line_file.clone()).into();
            let right_nonnegative: AtomicFact =
                LessEqualFact::new(z, f.right.clone(), f.line_file.clone()).into();
            let power_le_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            let left_result = self.verify_order_subgoal(left_nonnegative)?;
            let right_result = self.verify_order_subgoal(right_nonnegative)?;
            if power_le_result.is_true() && left_result.is_true() && right_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N_pos".to_string(),
                        vec![exponent_result, left_result, right_result, power_le_result],
                    ),
                )));
            }
        }
        Ok(None)
    }

    // a^n <= b^n from a <= b when n is a positive odd integer.
    // Example: from `a <= b`, prove `a^3 <= b^3`.
    fn try_pow_le_same_positive_odd_integer_exponent(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };

        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoal: AtomicFact =
            LessEqualFact::new(left_base.clone(), right_base.clone(), lf.clone()).into();
        let result = self.verify_order_subgoal(subgoal)?;
        if !result.is_true() {
            return Ok(None);
        }
        step_results.push(result);

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from a <= b and positive odd integer n".to_string(),
                step_results,
            ),
        )))
    }

    // Negative integer powers reverse order on positive bases.
    // Example: from `0 < b <= a` and `n < 0`, prove `a^n <= b^n`.
    fn try_pow_le_same_negative_integer_exponent_positive_base_reverses_order(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }

        let exponent = left_pow.exponent.as_ref();
        let zero = Self::literal_zero_obj();
        let subgoals: [AtomicFact; 4] = [
            InFact::new(exponent.clone(), StandardSet::Z.into(), lf.clone()).into(),
            LessFact::new(exponent.clone(), zero.clone(), lf.clone()).into(),
            LessFact::new(zero, right_pow.base.as_ref().clone(), lf.clone()).into(),
            LessEqualFact::new(
                right_pow.base.as_ref().clone(),
                left_pow.base.as_ref().clone(),
                lf.clone(),
            )
            .into(),
        ];

        let mut step_results = Vec::with_capacity(subgoals.len());
        for subgoal in subgoals {
            let result = self.verify_order_subgoal(subgoal)?;
            if !result.is_true() {
                return Ok(None);
            }
            step_results.push(result);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from 0 < b <= a and negative integer n".to_string(),
                step_results,
            ),
        )))
    }

    // a^k <= b^k from abs(a) <= abs(b) when k in N_pos and k % 2 = 0.
    // Example: `forall x, y R: abs(x) <= abs(y) => x^2 <= y^2`.
    fn try_pow_le_even_exponent_from_abs_le(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) =
            self.verify_even_exponent_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };
        let abs_le: AtomicFact = LessEqualFact::new(
            Abs::new(left_pow.base.as_ref().clone()).into(),
            Abs::new(right_pow.base.as_ref().clone()).into(),
            lf.clone(),
        )
        .into();
        let abs_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&abs_le)?;
        if !abs_result.is_true() {
            return Ok(None);
        }
        step_results.push(abs_result);
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^k <= b^k from abs(a) <= abs(b) and even k in N_pos".to_string(),
                step_results,
            ),
        )))
    }

    // a^k < b^k from abs(a) < abs(b) when k in N_pos and k % 2 = 0.
    fn try_pow_lt_even_exponent_from_abs_lt(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) =
            self.verify_even_exponent_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };
        let abs_lt: AtomicFact = LessFact::new(
            Abs::new(left_pow.base.as_ref().clone()).into(),
            Abs::new(right_pow.base.as_ref().clone()).into(),
            lf.clone(),
        )
        .into();
        let abs_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&abs_lt)?;
        if !abs_result.is_true() {
            return Ok(None);
        }
        step_results.push(abs_result);
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^k < b^k from abs(a) < abs(b) and even k in N_pos".to_string(),
                step_results,
            ),
        )))
    }

    // Positive-real powers are strictly increasing in the base for a fixed positive real exponent.
    // Example: from `0 < a`, `0 < b`, `a < b`, `0 < q`, and `q $in R` or `q $in Q`,
    // prove `a^q < b^q`.
    fn try_pow_lt_same_positive_real_exponent_positive_base(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !Self::objs_same_by_display(left_pow.exponent.as_ref(), right_pow.exponent.as_ref()) {
            return Ok(None);
        }

        let zero = Self::literal_zero_obj();
        let exponent = left_pow.exponent.as_ref();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();

        let exponent_in_r: AtomicFact =
            InFact::new(exponent.clone(), StandardSet::R.into(), lf.clone()).into();
        let mut exponent_result = self.verify_order_subgoal(exponent_in_r)?;
        if !exponent_result.is_true() {
            let exponent_in_q: AtomicFact =
                InFact::new(exponent.clone(), StandardSet::Q.into(), lf.clone()).into();
            exponent_result = self.verify_order_subgoal(exponent_in_q)?;
        }
        if !exponent_result.is_true() {
            return Ok(None);
        }

        let subgoals: [AtomicFact; 4] = [
            LessFact::new(zero.clone(), exponent.clone(), lf.clone()).into(),
            LessFact::new(zero.clone(), left_base.clone(), lf.clone()).into(),
            LessFact::new(zero, right_base.clone(), lf.clone()).into(),
            LessFact::new(left_base.clone(), right_base.clone(), lf.clone()).into(),
        ];

        let mut step_results = Vec::with_capacity(subgoals.len() + 1);
        step_results.push(exponent_result);
        for subgoal in subgoals {
            let result = self.verify_order_subgoal(subgoal)?;
            if !result.is_true() {
                return Ok(None);
            }
            step_results.push(result);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^q < b^q from 0 < a, 0 < b, a < b, 0 < q, and q in R or Q".to_string(),
                step_results,
            ),
        )))
    }

    // a^n < b^n from a < b when n is a positive odd integer.
    // Example: from `a < b`, prove `a^3 < b^3`.
    fn try_pow_lt_same_positive_odd_integer_exponent(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };

        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoal: AtomicFact =
            LessFact::new(left_base.clone(), right_base.clone(), lf.clone()).into();
        let result = self.verify_order_subgoal(subgoal)?;
        if !result.is_true() {
            return Ok(None);
        }
        step_results.push(result);

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < b^n from a < b and positive odd integer n".to_string(),
                step_results,
            ),
        )))
    }

    // Negative sign preservation for positive odd integer powers.
    // Example: from `x <= 0` and odd `n`, prove `x^n <= 0`.
    fn try_pow_le_zero_odd_exponent_from_nonpositive_base(
        &mut self,
        pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };

        let zero = Self::literal_zero_obj();
        let base_nonpositive: AtomicFact =
            LessEqualFact::new(pow.base.as_ref().clone(), zero, lf.clone()).into();
        let base_result = self.verify_order_subgoal(base_nonpositive)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        step_results.push(base_result);

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= 0 from a <= 0 and positive odd integer n".to_string(),
                step_results,
            ),
        )))
    }

    // Strict negative sign preservation for positive odd integer powers.
    // Example: from `x < 0` and odd `n`, prove `x^n < 0`.
    fn try_pow_lt_zero_odd_exponent_from_negative_base(
        &mut self,
        pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(pow.exponent.as_ref(), lf)?
        else {
            return Ok(None);
        };

        let zero = Self::literal_zero_obj();
        let base_negative: AtomicFact =
            LessFact::new(pow.base.as_ref().clone(), zero, lf.clone()).into();
        let base_result = self.verify_order_subgoal(base_negative)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        step_results.push(base_result);

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < 0 from a < 0 and positive odd integer n".to_string(),
                step_results,
            ),
        )))
    }

    // a^n < b^n from 0 <= a, a < b, and positive integer n.
    // Example: from `0 <= a < b`, prove `a^2 < b^2`; equivalently,
    // from `b > a` and `a >= 0`, prove `b^n > a^n`.
    fn try_pow_lt_same_positive_integer_exponent_nonnegative_base(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let mut step_results = Vec::new();
        if !Self::obj_is_positive_integer_number(left_pow.exponent.as_ref()) {
            let exponent_result =
                self.verify_obj_in_n_pos_subgoal(left_pow.exponent.as_ref(), lf)?;
            if !exponent_result.is_true() {
                return Ok(None);
            }
            step_results.push(exponent_result);
        }

        let z = Self::literal_zero_obj();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoals: [AtomicFact; 2] = [
            LessEqualFact::new(z.clone(), left_base.clone(), lf.clone()).into(),
            LessFact::new(left_base.clone(), right_base.clone(), lf.clone()).into(),
        ];
        for subgoal in subgoals {
            let result = self.verify_order_subgoal(subgoal)?;
            if !result.is_true() {
                return Ok(None);
            }
            step_results.push(result);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < b^n from 0 <= a, a < b, and positive integer n".to_string(),
                step_results,
            ),
        )))
    }

    // k*u <= k*v from 0 <= k and u <= v; or k*u <= k*v from k <= 0 and v <= u (order reversal).
    fn try_mul_le_shared_left(
        &mut self,
        x: &Obj,
        u: &Obj,
        v: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        msg_nonneg: &str,
        msg_nonpos: &str,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let g0 = LessEqualFact::new(z.clone(), x.clone(), lf.clone()).into();
        let g_ord = LessEqualFact::new(u.clone(), v.clone(), lf.clone()).into();
        let r0 = self.verify_order_subgoal(g0)?;
        let r1 = self.verify_order_subgoal(g_ord)?;
        if r0.is_true() && r1.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_nonneg.to_string(),
                    vec![r0, r1],
                ),
            )));
        }
        let g_x_nonpos = LessEqualFact::new(x.clone(), z.clone(), lf.clone()).into();
        let g_rev = LessEqualFact::new(v.clone(), u.clone(), lf.clone()).into();
        let r2 = self.verify_order_subgoal(g_x_nonpos)?;
        let r3 = self.verify_order_subgoal(g_rev)?;
        if r2.is_true() && r3.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_nonpos.to_string(),
                    vec![r2, r3],
                ),
            )));
        }
        Ok(None)
    }

    // k*u < k*v from 0 < k and u < v; or k*u < k*v from k < 0 and v < u.
    fn try_mul_lt_shared_left(
        &mut self,
        x: &Obj,
        u: &Obj,
        v: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        msg_pos: &str,
        msg_neg: &str,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let g_pos = LessFact::new(z.clone(), x.clone(), lf.clone()).into();
        let g_ord = LessFact::new(u.clone(), v.clone(), lf.clone()).into();
        let r0 = self.verify_order_subgoal(g_pos)?;
        let r1 = self.verify_order_subgoal(g_ord)?;
        if r0.is_true() && r1.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_pos.to_string(),
                    vec![r0, r1],
                ),
            )));
        }
        let g_x_neg = LessFact::new(x.clone(), z.clone(), lf.clone()).into();
        let g_rev = LessFact::new(v.clone(), u.clone(), lf.clone()).into();
        let r2 = self.verify_order_subgoal(g_x_neg)?;
        let r3 = self.verify_order_subgoal(g_rev)?;
        if r2.is_true() && r3.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_neg.to_string(),
                    vec![r2, r3],
                ),
            )));
        }
        Ok(None)
    }

    // x1*x2 <= y1*y2 when 0 <= x1,x2,y1,y2 and (x1 <= y1, x2 <= y2) or (x1 <= y2, x2 <= y1).
    // Example: (m+1)*2 <= 2^m * 2 from IH and 2 <= 2, with m+1, 2, 2^m, 2 all nonnegative.
    fn try_mul_le_componentwise_nonnegative_factors(
        &mut self,
        l1: &Obj,
        l2: &Obj,
        r1: &Obj,
        r2: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let mut try_pairing =
            |x1: &Obj, x2: &Obj, y1: &Obj, y2: &Obj| -> Result<Option<StmtResult>, RuntimeError> {
                let subgoals: [AtomicFact; 6] = [
                    LessEqualFact::new(z.clone(), x1.clone(), lf.clone()).into(),
                    LessEqualFact::new(z.clone(), x2.clone(), lf.clone()).into(),
                    LessEqualFact::new(z.clone(), y1.clone(), lf.clone()).into(),
                    LessEqualFact::new(z.clone(), y2.clone(), lf.clone()).into(),
                    LessEqualFact::new(x1.clone(), y1.clone(), lf.clone()).into(),
                    LessEqualFact::new(x2.clone(), y2.clone(), lf.clone()).into(),
                ];
                let mut rec = Vec::with_capacity(6);
                for g in subgoals {
                    let r = self.verify_order_subgoal(g)?;
                    if !r.is_true() {
                        return Ok(None);
                    }
                    rec.push(r);
                }
                Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "x1 * x2 <= y1 * y2 from 0 <= factors and componentwise <=".to_string(),
                        rec,
                    ),
                )))
            };
        if let Some(r) = try_pairing(l1, l2, r1, r2)? {
            return Ok(Some(r));
        }
        try_pairing(l1, l2, r2, r1)
    }

    // 0 <= a*b when a,b have the same weak sign; a*b <= 0 when they have opposite weak signs.
    // Example: from `a <= 0` and `0 <= b`, prove `a * b <= 0`.
    fn try_mul_le_zero_by_weak_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let mut try_signs =
            |negative: &Obj, positive: &Obj| -> Result<Option<StmtResult>, RuntimeError> {
                let g_neg = LessEqualFact::new(negative.clone(), z.clone(), lf.clone()).into();
                let g_pos = LessEqualFact::new(z.clone(), positive.clone(), lf.clone()).into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_pos = self.verify_order_subgoal(g_pos)?;
                if r_neg.is_true() && r_pos.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a * b <= 0 from a <= 0 and 0 <= b".to_string(),
                            vec![r_neg, r_pos],
                        ),
                    )));
                }
                Ok(None)
            };
        if let Some(r) = try_signs(left, right)? {
            return Ok(Some(r));
        }
        try_signs(right, left)
    }

    fn try_zero_le_mul_by_weak_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let mut try_signs = |first_nonnegative: bool| -> Result<Option<StmtResult>, RuntimeError> {
            let subgoals: [AtomicFact; 2] = if first_nonnegative {
                [
                    LessEqualFact::new(z.clone(), left.clone(), lf.clone()).into(),
                    LessEqualFact::new(z.clone(), right.clone(), lf.clone()).into(),
                ]
            } else {
                [
                    LessEqualFact::new(left.clone(), z.clone(), lf.clone()).into(),
                    LessEqualFact::new(right.clone(), z.clone(), lf.clone()).into(),
                ]
            };
            let r0 = self.verify_order_subgoal(subgoals[0].clone())?;
            let r1 = self.verify_order_subgoal(subgoals[1].clone())?;
            if r0.is_true() && r1.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "0 <= a * b from a,b having the same weak sign".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
            Ok(None)
        };
        if let Some(r) = try_signs(true)? {
            return Ok(Some(r));
        }
        try_signs(false)
    }

    // Strict product sign rules require both factors to be strictly away from zero.
    fn try_mul_lt_zero_by_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let mut try_signs =
            |negative: &Obj, positive: &Obj| -> Result<Option<StmtResult>, RuntimeError> {
                let g_neg = LessFact::new(negative.clone(), z.clone(), lf.clone()).into();
                let g_pos = LessFact::new(z.clone(), positive.clone(), lf.clone()).into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_pos = self.verify_order_subgoal(g_pos)?;
                if r_neg.is_true() && r_pos.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a * b < 0 from opposite strict signs".to_string(),
                            vec![r_neg, r_pos],
                        ),
                    )));
                }
                Ok(None)
            };
        if let Some(r) = try_signs(left, right)? {
            return Ok(Some(r));
        }
        try_signs(right, left)
    }

    fn try_zero_lt_mul_by_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let cases: [(AtomicFact, AtomicFact); 4] = [
            (
                LessFact::new(z.clone(), left.clone(), lf.clone()).into(),
                LessFact::new(z.clone(), right.clone(), lf.clone()).into(),
            ),
            (
                LessFact::new(z.clone(), right.clone(), lf.clone()).into(),
                LessFact::new(z.clone(), left.clone(), lf.clone()).into(),
            ),
            (
                LessFact::new(left.clone(), z.clone(), lf.clone()).into(),
                LessFact::new(right.clone(), z.clone(), lf.clone()).into(),
            ),
            (
                LessFact::new(right.clone(), z.clone(), lf.clone()).into(),
                LessFact::new(left.clone(), z.clone(), lf.clone()).into(),
            ),
        ];
        for (g0, g1) in cases {
            let r0 = self.verify_order_subgoal(g0)?;
            let r1 = self.verify_order_subgoal(g1)?;
            if r0.is_true() && r1.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "0 < a * b from same strict signs".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
        }
        Ok(None)
    }

    // Finite sum monotonicity on a shared integer range.
    // Example: from `forall i Z: m <= i <= n => f(i) <= g(i)`, prove
    // `sum(m, n, '(i Z) R {f(i)}) <= sum(m, n, '(i Z) R {g(i)})`.
    fn try_less_equal_sum_pointwise_on_same_integer_range(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Sum(left_sum), Obj::Sum(right_sum)) = (&f.left, &f.right) else {
            return Ok(None);
        };

        let verify_state = VerifyState::new(0, true);
        let start_result = self.verify_objs_are_equal_in_equality_builtin(
            left_sum.start.as_ref(),
            right_sum.start.as_ref(),
            f.line_file.clone(),
            &verify_state,
        )?;
        if !start_result.is_true() {
            return Ok(None);
        }
        let end_result = self.verify_objs_are_equal_in_equality_builtin(
            left_sum.end.as_ref(),
            right_sum.end.as_ref(),
            f.line_file.clone(),
            &verify_state,
        )?;
        if !end_result.is_true() {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) =
            self.instantiate_unary_anonymous_summand_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_anonymous_summand_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let pointwise_fact: AtomicFact =
            LessEqualFact::new(left_inst, right_inst, f.line_file.clone()).into();
        let dom_lo: Fact = LessEqualFact::new(
            (*left_sum.start).clone(),
            x_obj.clone(),
            f.line_file.clone(),
        )
        .into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj, (*left_sum.end).clone(), f.line_file.clone()).into();
        let pointwise_result = self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_name],
                ParamType::Obj(StandardSet::Z.into()),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            rt.store_fact_without_forall_coverage_check_and_infer(dom_lo)?;
            rt.store_fact_without_forall_coverage_check_and_infer(dom_hi)?;
            rt.verify_atomic_fact(&pointwise_fact, &verify_state)
        })?;
        if !pointwise_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "finite sum monotonicity from pointwise order on the integer range".to_string(),
                vec![start_result, end_result, pointwise_result],
            ),
        )))
    }

    fn try_less_equal_algebra(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();

        if let (Obj::Pow(left_pow), Obj::Pow(right_pow)) = (&f.left, &f.right) {
            if let Some(r) = self.try_pow_le_same_positive_integer_exponent_nonnegative_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_le_same_positive_odd_integer_exponent(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self
                .try_pow_le_same_negative_integer_exponent_positive_base_reverses_order(
                    left_pow,
                    right_pow,
                    lf,
                    atomic_fact,
                )?
            {
                return Ok(Some(r));
            }
            if let Some(r) =
                self.try_pow_le_even_exponent_from_abs_le(left_pow, right_pow, lf, atomic_fact)?
            {
                return Ok(Some(r));
            }
        }

        if let Some(r) = self
            .try_base_le_from_pow_le_same_positive_integer_exponent_nonnegative_base(
                f,
                atomic_fact,
            )?
        {
            return Ok(Some(r));
        }

        if let Some(r) = self.try_less_equal_sum_pointwise_on_same_integer_range(f, atomic_fact)? {
            return Ok(Some(r));
        }

        if let (Obj::Add(left_add), Obj::Add(right_add)) = (&f.left, &f.right) {
            if let Some((left_remaining, right_remaining)) =
                Self::add_common_remaining(left_add, right_add)
            {
                let subgoal: AtomicFact =
                    LessEqualFact::new(left_remaining, right_remaining, lf.clone()).into();
                let result = self.verify_order_subgoal(subgoal)?;
                if result.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "u + a <= u + b from a <= b".to_string(),
                            vec![result],
                        ),
                    )));
                }
            }
        }

        if let Obj::Sub(sub) = &f.left {
            // Subtracting a nonnegative term cannot increase the left side.
            // Example: from `a <= b` and `0 <= c`, prove `a - c <= b`.
            let order_subgoal: AtomicFact =
                LessEqualFact::new(sub.left.as_ref().clone(), f.right.clone(), lf.clone()).into();
            let nonnegative_subtractor: AtomicFact =
                LessEqualFact::new(z.clone(), sub.right.as_ref().clone(), lf.clone()).into();
            let order_result = self.verify_order_subgoal(order_subgoal)?;
            let nonnegative_result = self.verify_order_subgoal(nonnegative_subtractor)?;
            if order_result.is_true() && nonnegative_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c <= b from a <= b and 0 <= c".to_string(),
                        vec![order_result, nonnegative_result],
                    ),
                )));
            }

            // Move a left subtractor to the right side as an addend.
            // Example: from `a <= b + c`, prove `a - c <= b`.
            let shifted_right: Obj = Add::new(f.right.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact =
                LessEqualFact::new(sub.left.as_ref().clone(), shifted_right, lf.clone()).into();
            let shifted_result = self.verify_order_subgoal(shifted_subgoal)?;
            if shifted_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c <= b from a <= b + c".to_string(),
                        vec![shifted_result],
                    ),
                )));
            }
        }

        if let Obj::Add(add) = &f.right {
            let left_s = f.left.to_string();
            let b_opt = if add.left.as_ref().to_string() == left_s {
                Some(add.right.as_ref().clone())
            } else if add.right.as_ref().to_string() == left_s {
                Some(add.left.as_ref().clone())
            } else {
                None
            };
            if let Some(b) = b_opt {
                let g0 = LessEqualFact::new(z.clone(), b, lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if r0.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a <= a + b from 0 <= b".to_string(),
                            vec![r0],
                        ),
                    )));
                }
            }
            // a <= u + v from a <= u and 0 <= v (or symmetric addends).
            let g_a_left =
                LessEqualFact::new(f.left.clone(), add.left.as_ref().clone(), lf.clone()).into();
            let g0_right =
                LessEqualFact::new(z.clone(), add.right.as_ref().clone(), lf.clone()).into();
            let r1 = self.verify_order_subgoal(g_a_left)?;
            let r2 = self.verify_order_subgoal(g0_right)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b + c from a <= b and 0 <= c".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }
            let g_a_right =
                LessEqualFact::new(f.left.clone(), add.right.as_ref().clone(), lf.clone()).into();
            let g0_left =
                LessEqualFact::new(z.clone(), add.left.as_ref().clone(), lf.clone()).into();
            let r3 = self.verify_order_subgoal(g_a_right)?;
            let r4 = self.verify_order_subgoal(g0_left)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b + c from a <= b and 0 <= c".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.right {
            // Move a right subtractor to the left side as an addend.
            // Example: from `a + c <= b`, prove `a <= b - c`.
            let shifted_left: Obj = Add::new(f.left.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact =
                LessEqualFact::new(shifted_left, sub.left.as_ref().clone(), lf.clone()).into();
            let shifted_result = self.verify_order_subgoal(shifted_subgoal)?;
            if shifted_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b - c from a + c <= b".to_string(),
                        vec![shifted_result],
                    ),
                )));
            }

            if let Some(offset) = Self::integer_value_of_number_obj(sub.right.as_ref()) {
                if offset >= 0 {
                    let shifted_left = Self::obj_plus_nonnegative_integer_offset(&f.left, offset);
                    let subgoal: AtomicFact =
                        LessEqualFact::new(shifted_left, sub.left.as_ref().clone(), lf.clone())
                            .into();
                    let result = self.verify_order_subgoal(subgoal)?;
                    if result.is_true() {
                        return Ok(Some(StmtResult::from(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                "a <= x - n from a + n <= x".to_string(),
                                vec![result],
                            ),
                        )));
                    }
                }
            }
        }

        if let Obj::Sub(sub) = &f.left {
            if sub.left.as_ref().to_string() == f.right.to_string()
                && Self::obj_is_nonnegative_integer_number(sub.right.as_ref())
            {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - n <= a for n >= 0".to_string(),
                        Vec::new(),
                    ),
                )));
            }
        }

        if f.right.to_string() == z.to_string() {
            if let Obj::Pow(pow) = &f.left {
                if let Some(r) =
                    self.try_pow_le_zero_odd_exponent_from_nonpositive_base(pow, lf, atomic_fact)?
                {
                    return Ok(Some(r));
                }
            }
            if let Obj::Mul(m) = &f.left {
                if let Some(r) = self.try_mul_le_zero_by_weak_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if f.left.to_string() == z.to_string() {
            if let Obj::Mul(m) = &f.right {
                if let Some(r) = self.try_zero_le_mul_by_weak_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = LessEqualFact::new(z.clone(), f.left.clone(), lf.clone()).into();
                let g1 = LessEqualFact::new(one, m.left.as_ref().clone(), lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if !r0.is_true() {
                    return Ok(None);
                }
                let r1 = self.verify_order_subgoal(g1)?;
                if !r1.is_true() {
                    return Ok(None);
                }
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b * a from 0 <= a and 1 <= b".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
        }

        if let (Obj::Mul(ml), Obj::Mul(mr)) = (&f.left, &f.right) {
            if let Some(r) = self.try_mul_le_componentwise_nonnegative_factors(
                ml.left.as_ref(),
                ml.right.as_ref(),
                mr.left.as_ref(),
                mr.right.as_ref(),
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_le_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "k * a <= k * b from 0 <= k and a <= b",
                    "k * a <= k * b from k <= 0 and b <= a",
                )? {
                    return Ok(Some(r));
                }
            }
            if ml.right.to_string() == mr.right.to_string() {
                if let Some(r) = self.try_mul_le_shared_left(
                    ml.right.as_ref(),
                    ml.left.as_ref(),
                    mr.left.as_ref(),
                    lf,
                    atomic_fact,
                    "a * k <= b * k from 0 <= k and a <= b",
                    "a * k <= b * k from k <= 0 and b <= a",
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1 = LessEqualFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2 = LessEqualFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1)?;
            if !r1.is_true() {
                return Ok(None);
            }
            let r2 = self.verify_order_subgoal(g2)?;
            if !r2.is_true() {
                return Ok(None);
            }
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "a + c <= b + d from a <= b and c <= d".to_string(),
                    vec![r1, r2],
                ),
            )));
        }

        if let (Obj::Sub(sl), Obj::Sub(sr)) = (&f.left, &f.right) {
            // Componentwise weak monotonicity for subtraction.
            // Example: from `a <= b` and `c <= d`, prove `a - d <= b - c`.
            let g1 = LessEqualFact::new(
                sl.left.as_ref().clone(),
                sr.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2 = LessEqualFact::new(
                sr.right.as_ref().clone(),
                sl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1)?;
            if !r1.is_true() {
                return Ok(None);
            }
            let r2 = self.verify_order_subgoal(g2)?;
            if !r2.is_true() {
                return Ok(None);
            }
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "a - d <= b - c from a <= b and c <= d".to_string(),
                    vec![r1, r2],
                ),
            )));
        }

        if let (Obj::Div(dl), Obj::Div(dr)) = (&f.left, &f.right) {
            if dl.right.to_string() == dr.right.to_string() {
                let c = dl.right.as_ref();
                let g_pos = LessFact::new(z.clone(), c.clone(), lf.clone()).into();
                let g_ab = LessEqualFact::new(
                    dl.left.as_ref().clone(),
                    dr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_pos = self.verify_order_subgoal(g_pos)?;
                let r_ab = self.verify_order_subgoal(g_ab)?;
                if r_pos.is_true() && r_ab.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a / c <= b / c from 0 < c and a <= b".to_string(),
                            vec![r_pos, r_ab],
                        ),
                    )));
                }
                let g_neg = LessFact::new(c.clone(), z.clone(), lf.clone()).into();
                let g_ab_flip = LessEqualFact::new(
                    dr.left.as_ref().clone(),
                    dl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_ab2 = self.verify_order_subgoal(g_ab_flip)?;
                if r_neg.is_true() && r_ab2.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "b / c <= a / c from c < 0 and a <= b".to_string(),
                            vec![r_neg, r_ab2],
                        ),
                    )));
                }
            }
        }

        Ok(None)
    }

    fn try_less_algebra(
        &mut self,
        f: &LessFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();

        if let (Obj::Pow(left_pow), Obj::Pow(right_pow)) = (&f.left, &f.right) {
            if let Some(r) = self.try_pow_lt_same_positive_integer_exponent_nonnegative_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_lt_same_positive_odd_integer_exponent(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) =
                self.try_pow_lt_even_exponent_from_abs_lt(left_pow, right_pow, lf, atomic_fact)?
            {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_lt_same_positive_real_exponent_positive_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
        }

        if let (Obj::Add(left_add), Obj::Add(right_add)) = (&f.left, &f.right) {
            if let Some((left_remaining, right_remaining)) =
                Self::add_common_remaining(left_add, right_add)
            {
                let subgoal: AtomicFact =
                    LessFact::new(left_remaining, right_remaining, lf.clone()).into();
                let result = self.verify_order_subgoal(subgoal)?;
                if result.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "u + a < u + b from a < b".to_string(),
                            vec![result],
                        ),
                    )));
                }
            }
        }

        if let (Obj::Sub(sl), Obj::Sub(sr)) = (&f.left, &f.right) {
            // Componentwise strict monotonicity for subtraction.
            // Example: from `a < b` and `c <= d`, prove `a - d < b - c`.
            let g1s = LessFact::new(
                sl.left.as_ref().clone(),
                sr.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2s = LessEqualFact::new(
                sr.right.as_ref().clone(),
                sl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1s)?;
            let r2 = self.verify_order_subgoal(g2s)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - d < b - c from a < b and c <= d".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }

            // A strict subtractor comparison also gives a strict result.
            // Example: from `a <= b` and `c < d`, prove `a - d < b - c`.
            let g1w = LessEqualFact::new(
                sl.left.as_ref().clone(),
                sr.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2w = LessFact::new(
                sr.right.as_ref().clone(),
                sl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r3 = self.verify_order_subgoal(g1w)?;
            let r4 = self.verify_order_subgoal(g2w)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - d < b - c from a <= b and c < d".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
        }

        if let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (&f.left, &f.right) {
            if let Obj::Sub(sub) = left_abs.arg.as_ref() {
                if Self::objs_same_by_display(sub.left.as_ref(), right_abs.arg.as_ref())
                    && Self::obj_is_positive_integer_number(sub.right.as_ref())
                {
                    let zero = Self::literal_zero_obj();
                    let positive_arg: AtomicFact =
                        LessFact::new(zero.clone(), right_abs.arg.as_ref().clone(), lf.clone())
                            .into();
                    let nonnegative_sub: AtomicFact =
                        LessEqualFact::new(zero, left_abs.arg.as_ref().clone(), lf.clone()).into();
                    let r_pos = self.verify_order_subgoal(positive_arg)?;
                    let r_sub = self.verify_order_subgoal(nonnegative_sub)?;
                    if r_pos.is_true() && r_sub.is_true() {
                        return Ok(Some(StmtResult::from(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                "abs(x - n) < abs(x) for positive x and nonnegative x - n"
                                    .to_string(),
                                vec![r_pos, r_sub],
                            ),
                        )));
                    }
                }
            }
        }

        if let Obj::Sub(sub) = &f.left {
            // Subtracting a nonnegative term preserves a strict upper bound.
            // Example: from `a < b` and `0 <= c`, prove `a - c < b`.
            let strict_order_subgoal: AtomicFact =
                LessFact::new(sub.left.as_ref().clone(), f.right.clone(), lf.clone()).into();
            let nonnegative_subtractor: AtomicFact =
                LessEqualFact::new(z.clone(), sub.right.as_ref().clone(), lf.clone()).into();
            let strict_order_result = self.verify_order_subgoal(strict_order_subgoal)?;
            let nonnegative_result = self.verify_order_subgoal(nonnegative_subtractor)?;
            if strict_order_result.is_true() && nonnegative_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a < b and 0 <= c".to_string(),
                        vec![strict_order_result, nonnegative_result],
                    ),
                )));
            }

            // Subtracting a positive term turns a weak upper bound into a strict one.
            // Example: from `a <= b` and `0 < c`, prove `a - c < b`.
            let weak_order_subgoal: AtomicFact =
                LessEqualFact::new(sub.left.as_ref().clone(), f.right.clone(), lf.clone()).into();
            let positive_subtractor: AtomicFact =
                LessFact::new(z.clone(), sub.right.as_ref().clone(), lf.clone()).into();
            let weak_order_result = self.verify_order_subgoal(weak_order_subgoal)?;
            let positive_result = self.verify_order_subgoal(positive_subtractor)?;
            if weak_order_result.is_true() && positive_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a <= b and 0 < c".to_string(),
                        vec![weak_order_result, positive_result],
                    ),
                )));
            }

            // Move a left subtractor to the right side as an addend.
            // Example: from `a < b + c`, prove `a - c < b`.
            let shifted_right: Obj = Add::new(f.right.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact =
                LessFact::new(sub.left.as_ref().clone(), shifted_right, lf.clone()).into();
            let shifted_result = self.verify_order_subgoal(shifted_subgoal)?;
            if shifted_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a < b + c".to_string(),
                        vec![shifted_result],
                    ),
                )));
            }
        }

        if let Obj::Add(add) = &f.right {
            let left_s = f.left.to_string();
            let b_opt = if add.left.as_ref().to_string() == left_s {
                Some(add.right.as_ref().clone())
            } else if add.right.as_ref().to_string() == left_s {
                Some(add.left.as_ref().clone())
            } else {
                None
            };
            if let Some(b) = b_opt {
                let g0 = LessFact::new(z.clone(), b, lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if r0.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a < a + b from 0 < b".to_string(),
                            vec![r0],
                        ),
                    )));
                }
            }
            // a < u + v from a < u and 0 <= v (or symmetric addends).
            let g_a_left =
                LessFact::new(f.left.clone(), add.left.as_ref().clone(), lf.clone()).into();
            let g0_right =
                LessEqualFact::new(z.clone(), add.right.as_ref().clone(), lf.clone()).into();
            let r1 = self.verify_order_subgoal(g_a_left)?;
            let r2 = self.verify_order_subgoal(g0_right)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b + c from a < b and 0 <= c".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }
            let g_a_right =
                LessFact::new(f.left.clone(), add.right.as_ref().clone(), lf.clone()).into();
            let g0_left =
                LessEqualFact::new(z.clone(), add.left.as_ref().clone(), lf.clone()).into();
            let r3 = self.verify_order_subgoal(g_a_right)?;
            let r4 = self.verify_order_subgoal(g0_left)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b + c from a < c and 0 <= b".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.right {
            // Move a right subtractor to the left side as an addend.
            // Example: from `a + c < b`, prove `a < b - c`.
            let shifted_left: Obj = Add::new(f.left.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact =
                LessFact::new(shifted_left, sub.left.as_ref().clone(), lf.clone()).into();
            let shifted_result = self.verify_order_subgoal(shifted_subgoal)?;
            if shifted_result.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b - c from a + c < b".to_string(),
                        vec![shifted_result],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.left {
            if sub.left.as_ref().to_string() == f.right.to_string()
                && Self::obj_is_positive_integer_number(sub.right.as_ref())
            {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - n < a for n > 0".to_string(),
                        Vec::new(),
                    ),
                )));
            }
        }

        // Dividing a positive quantity by a factor greater than one makes it smaller.
        // Example: from `a > 0` and `b > 1`, prove `a / b < a`.
        if let Obj::Div(div) = &f.left {
            if div.left.as_ref().to_string() == f.right.to_string() {
                let g_pos = LessFact::new(z.clone(), f.right.clone(), lf.clone()).into();
                let g_denom_gt_one =
                    LessFact::new(one.clone(), div.right.as_ref().clone(), lf.clone()).into();
                let r_pos = self.verify_order_subgoal(g_pos)?;
                if !r_pos.is_true() {
                    return Ok(None);
                }
                let r_denom_gt_one = self.verify_order_subgoal(g_denom_gt_one)?;
                if !r_denom_gt_one.is_true() {
                    return Ok(None);
                }
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a / b < a from 0 < a and 1 < b".to_string(),
                        vec![r_pos, r_denom_gt_one],
                    ),
                )));
            }
        }

        if f.right.to_string() == z.to_string() {
            if let Obj::Pow(pow) = &f.left {
                if let Some(r) =
                    self.try_pow_lt_zero_odd_exponent_from_negative_base(pow, lf, atomic_fact)?
                {
                    return Ok(Some(r));
                }
            }
            if let Obj::Mul(m) = &f.left {
                if let Some(r) = self.try_mul_lt_zero_by_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if f.left.to_string() == z.to_string() {
            if let Obj::Mul(m) = &f.right {
                if let Some(r) = self.try_zero_lt_mul_by_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = LessFact::new(z.clone(), f.left.clone(), lf.clone()).into();
                let g1 = LessFact::new(one, m.left.as_ref().clone(), lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if !r0.is_true() {
                    return Ok(None);
                }
                let r1 = self.verify_order_subgoal(g1)?;
                if !r1.is_true() {
                    return Ok(None);
                }
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b * a from 0 < a and 1 < b".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
        }

        if let (Obj::Mul(ml), Obj::Mul(mr)) = (&f.left, &f.right) {
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_lt_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "k * a < k * b from 0 < k and a < b",
                    "k * a < k * b from k < 0 and b < a",
                )? {
                    return Ok(Some(r));
                }
            }
            if ml.right.to_string() == mr.right.to_string() {
                if let Some(r) = self.try_mul_lt_shared_left(
                    ml.right.as_ref(),
                    ml.left.as_ref(),
                    mr.left.as_ref(),
                    lf,
                    atomic_fact,
                    "a * k < b * k from 0 < k and a < b",
                    "a * k < b * k from k < 0 and b < a",
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1s = LessFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2s = LessFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1s)?;
            let r2 = self.verify_order_subgoal(g2s)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c < d".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }
            let g1m = LessFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2m = LessEqualFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r3 = self.verify_order_subgoal(g1m)?;
            let r4 = self.verify_order_subgoal(g2m)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c <= d".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
            let g1w = LessEqualFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2w = LessFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r5 = self.verify_order_subgoal(g1w)?;
            let r6 = self.verify_order_subgoal(g2w)?;
            if r5.is_true() && r6.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a <= b and c < d".to_string(),
                        vec![r5, r6],
                    ),
                )));
            }
        }

        if let (Obj::Div(dl), Obj::Div(dr)) = (&f.left, &f.right) {
            if dl.right.to_string() == dr.right.to_string() {
                let c = dl.right.as_ref();
                let g_pos = LessFact::new(z.clone(), c.clone(), lf.clone()).into();
                let g_ab = LessFact::new(
                    dl.left.as_ref().clone(),
                    dr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_pos = self.verify_order_subgoal(g_pos)?;
                let r_ab = self.verify_order_subgoal(g_ab)?;
                if r_pos.is_true() && r_ab.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a / c < b / c from 0 < c and a < b".to_string(),
                            vec![r_pos, r_ab],
                        ),
                    )));
                }
                let g_neg = LessFact::new(c.clone(), z.clone(), lf.clone()).into();
                let g_ab_flip = LessFact::new(
                    dr.left.as_ref().clone(),
                    dl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_ab2 = self.verify_order_subgoal(g_ab_flip)?;
                if r_neg.is_true() && r_ab2.is_true() {
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "b / c < a / c from c < 0 and a < b".to_string(),
                            vec![r_neg, r_ab2],
                        ),
                    )));
                }
            }
        }

        Ok(None)
    }
}
