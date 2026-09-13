// Structural order on R (+, -, *, /) is implemented as a kernel verification rule.
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
    pub fn verify_order_algebra_structural_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => {
                self.try_less_equal_algebra(f, atomic_fact, builtin_state)
            }
            AtomicFact::LessFact(f) => self.try_less_algebra(f, atomic_fact, builtin_state),
            _ => Ok(None),
        }
    }

    fn try_verify_order_subgoal(
        &mut self,
        fact: AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        self.try_verify_atomic_fact_as_builtin_rule_premise(&fact, builtin_state)
    }

    pub fn literal_zero_obj() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    pub fn literal_one_obj() -> Obj {
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        let in_n_pos: AtomicFact = self
            .new_in_fact(obj.clone(), StandardSet::NPos.into(), lf.clone())
            .into();
        self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n_pos, builtin_state)
    }

    fn verify_positive_real_power_operands(
        &mut self,
        left_base: &Obj,
        right_base: &Obj,
        exponent: &Obj,
        lf: &LineFile,
        allow_strict_recursion: bool,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let positive_real_memberships: [AtomicFact; 3] = [
            self.new_in_fact(left_base.clone(), StandardSet::RPos.into(), lf.clone())
                .into(),
            self.new_in_fact(right_base.clone(), StandardSet::RPos.into(), lf.clone())
                .into(),
            self.new_in_fact(exponent.clone(), StandardSet::RPos.into(), lf.clone())
                .into(),
        ];
        if let Some(steps) =
            self.verify_builtin_rule_premises(&positive_real_memberships, builtin_state)?
        {
            return Ok(Some(steps));
        }

        let zero = Self::literal_zero_obj();
        let positive_exponent: AtomicFact = self
            .new_less_fact(zero.clone(), exponent.clone(), lf.clone())
            .into();
        let positive_left: AtomicFact = self
            .new_less_fact(zero.clone(), left_base.clone(), lf.clone())
            .into();
        let positive_right: AtomicFact = self
            .new_less_fact(zero, right_base.clone(), lf.clone())
            .into();
        let _ = allow_strict_recursion;
        let result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_in_fact(exponent.clone(), StandardSet::R.into(), lf.clone())
                        .into(),
                    positive_exponent.clone(),
                    positive_left.clone(),
                    positive_right.clone(),
                ],
                vec![
                    self.new_in_fact(exponent.clone(), StandardSet::Q.into(), lf.clone())
                        .into(),
                    positive_exponent,
                    positive_left,
                    positive_right,
                ],
            ],
            lf.clone(),
            builtin_state,
        )?;
        Ok(result.map(|result| vec![result]))
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

    // k in N+ and k % 2 = 0, or k is a positive even literal.
    fn verify_even_exponent_in_n_pos_subgoal(
        &mut self,
        exp: &Obj,
        lf: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if Self::obj_is_positive_even_integer_number(exp) {
            return Ok(Some(Vec::new()));
        }
        let mut steps = Vec::new();
        let Some(n_pos_result) = self.verify_obj_in_n_pos_subgoal(exp, lf, builtin_state)? else {
            return Ok(None);
        };
        steps.push(n_pos_result);
        let two: Obj = Number::new("2".to_string()).into();
        let zero = Self::literal_zero_obj();
        let mod_obj: Obj = Mod::new(exp.clone(), two).into();
        let even_fact: AtomicFact = self.new_equal_fact(mod_obj, zero, lf.clone()).into();
        let Some(even_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&even_fact, builtin_state)?
        else {
            return Ok(None);
        };
        steps.push(even_result);
        Ok(Some(steps))
    }

    // k in N+ and k % 2 = 1, or k is a positive odd literal.
    fn verify_odd_exponent_in_n_pos_subgoal(
        &mut self,
        exp: &Obj,
        lf: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if Self::obj_is_positive_odd_integer_number(exp) {
            return Ok(Some(Vec::new()));
        }
        let mut steps = Vec::new();
        let Some(n_pos_result) = self.verify_obj_in_n_pos_subgoal(exp, lf, builtin_state)? else {
            return Ok(None);
        };
        steps.push(n_pos_result);
        let two: Obj = Number::new("2".to_string()).into();
        let one = Self::literal_one_obj();
        let mod_obj: Obj = Mod::new(exp.clone(), two).into();
        let odd_fact: AtomicFact = self
            .new_equal_fact_from_refs(&mod_obj, &one, lf.clone())
            .into();
        let Some(odd_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&odd_fact, builtin_state)?
        else {
            return Ok(None);
        };
        steps.push(odd_result);
        Ok(Some(steps))
    }

    fn objs_have_same_display(left: &Obj, right: &Obj) -> bool {
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
            if Self::objs_have_same_display(left_common, right_common) {
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let mut subgoals = Vec::new();
        if !Self::obj_is_positive_integer_number(left_pow.exponent.as_ref()) {
            subgoals.push(
                self.new_in_fact(
                    left_pow.exponent.as_ref().clone(),
                    StandardSet::NPos.into(),
                    lf.clone(),
                )
                .into(),
            );
        }

        let z = Self::literal_zero_obj();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        subgoals.push(
            self.new_less_equal_fact(z, left_base.clone(), lf.clone())
                .into(),
        );
        subgoals.push(
            self.new_less_equal_fact(left_base.clone(), right_base.clone(), lf.clone())
                .into(),
        );
        let Some(step_results) = self.verify_builtin_rule_premises(&subgoals, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from 0 <= a, a <= b, and positive integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLeSamePositiveIntegerExponentNonnegativeBase,
                ),
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
            for known_facts_map in environment.facts.known_non_equational_facts.by_two_args.values() {
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
                    if !Self::objs_have_same_display(left_pow.base.as_ref(), left_base) {
                        continue;
                    }
                    if !Self::objs_have_same_display(right_pow.base.as_ref(), right_base) {
                        continue;
                    }
                    candidates.push(known_fact.clone());
                }
            }
        }
        candidates
    }

    fn collect_known_power_lt_candidates(
        &self,
        left_base: &Obj,
        right_base: &Obj,
    ) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.facts.known_non_equational_facts.by_two_args.values() {
                for known_fact in known_facts_map.values() {
                    let AtomicFact::LessFact(known_lt) = known_fact else {
                        continue;
                    };
                    let (Obj::Pow(left_pow), Obj::Pow(right_pow)) =
                        (&known_lt.left, &known_lt.right)
                    else {
                        continue;
                    };
                    if !Self::objs_have_same_display(
                        left_pow.exponent.as_ref(),
                        right_pow.exponent.as_ref(),
                    ) || !Self::objs_have_same_display(left_pow.base.as_ref(), left_base)
                        || !Self::objs_have_same_display(right_pow.base.as_ref(), right_base)
                    {
                        continue;
                    }
                    candidates.push(known_fact.clone());
                }
            }
        }
        candidates
    }

    // a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N+.
    // Example: from `0 <= x`, `0 <= y`, `m $in N+`, and `x^m <= y^m`, prove `x <= y`.
    fn try_base_le_from_pow_le_same_positive_integer_exponent_nonnegative_base(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let candidates = self.collect_known_power_le_candidates(&f.left, &f.right);
        for candidate in candidates {
            let AtomicFact::LessEqualFact(power_le) = &candidate else {
                continue;
            };
            let (Obj::Pow(left_pow), Obj::Pow(_)) = (&power_le.left, &power_le.right) else {
                continue;
            };

            let Some(exponent_result) = self.verify_obj_in_n_pos_subgoal(
                left_pow.exponent.as_ref(),
                &f.line_file,
                builtin_state,
            )?
            else {
                continue;
            };

            let z = Self::literal_zero_obj();
            let left_nonnegative: AtomicFact = self
                .new_less_equal_fact(z.clone(), f.left.clone(), f.line_file.clone())
                .into();
            let right_nonnegative: AtomicFact = self
                .new_less_equal_fact(z, f.right.clone(), f.line_file.clone())
                .into();
            let Some(power_le_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?
            else {
                continue;
            };
            let left_result = self.try_verify_order_subgoal(left_nonnegative, builtin_state)?;
            let right_result = self.try_verify_order_subgoal(right_nonnegative, builtin_state)?;
            if let (Some(left_result), Some(right_result)) = (left_result, right_result) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N+".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryBaseLeFromPowLeSamePositiveIntegerExponentNonnegativeBase),
                        vec![exponent_result, left_result, right_result, power_le_result],
                    ),
                )));
            }
        }
        Ok(None)
    }

    // Positive-real powers reflect weak order on positive bases.
    // Example: `0 < a`, `0 < b`, `0 < q`, and `a^q <= b^q` imply `a <= b`.
    fn try_base_le_from_pow_le_same_positive_real_exponent_positive_base(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let candidates = self.collect_known_power_le_candidates(&f.left, &f.right);
        for candidate in candidates {
            let AtomicFact::LessEqualFact(power_le) = &candidate else {
                continue;
            };
            let (Obj::Pow(left_pow), Obj::Pow(_)) = (&power_le.left, &power_le.right) else {
                continue;
            };
            let Some(mut steps) = self.verify_positive_real_power_operands(
                &f.left,
                &f.right,
                left_pow.exponent.as_ref(),
                &f.line_file,
                false,
                builtin_state,
            )?
            else {
                continue;
            };

            let Some(power_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?
            else {
                continue;
            };
            steps.push(power_result);
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a <= b from positive bases and exponent, and a^q <= b^q".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryBaseLeFromPowLeSamePositiveRealExponentPositiveBase),
                    steps,
                ),
            )));
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) = self.verify_odd_exponent_in_n_pos_subgoal(
            left_pow.exponent.as_ref(),
            lf,
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoal: AtomicFact = self
            .new_less_equal_fact(left_base.clone(), right_base.clone(), lf.clone())
            .into();
        let Some(result) = self.try_verify_order_subgoal(subgoal, builtin_state)? else {
            return Ok(None);
        };
        step_results.push(result);

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from a <= b and positive odd integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLeSamePositiveOddIntegerExponent,
                ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }

        let exponent = left_pow.exponent.as_ref();
        let zero = Self::literal_zero_obj();
        let subgoals: [AtomicFact; 4] = [
            self.new_in_fact(exponent.clone(), StandardSet::Z.into(), lf.clone())
                .into(),
            self.new_less_fact(exponent.clone(), zero.clone(), lf.clone())
                .into(),
            self.new_less_fact(zero, right_pow.base.as_ref().clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(
                right_pow.base.as_ref().clone(),
                left_pow.base.as_ref().clone(),
                lf.clone(),
            )
            .into(),
        ];

        let Some(step_results) = self.verify_builtin_rule_premises(&subgoals, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= b^n from 0 < b <= a and negative integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryPowLeSameNegativeIntegerExponentPositiveBaseReversesOrder),
                step_results,
            ),
        )))
    }

    // a^k <= b^k from abs(a) <= abs(b) when k in N+ and k % 2 = 0.
    // Example: `forall x, y R: abs(x) <= abs(y) => x^2 <= y^2`.
    fn try_pow_le_even_exponent_from_abs_le(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) = self.verify_even_exponent_in_n_pos_subgoal(
            left_pow.exponent.as_ref(),
            lf,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let abs_le: AtomicFact = self
            .new_less_equal_fact(
                Abs::new(left_pow.base.as_ref().clone()).into(),
                Abs::new(right_pow.base.as_ref().clone()).into(),
                lf.clone(),
            )
            .into();
        let Some(abs_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&abs_le, builtin_state)?
        else {
            return Ok(None);
        };
        step_results.push(abs_result);
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^k <= b^k from abs(a) <= abs(b) and even k in N+".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLeEvenExponentFromAbsLe,
                ),
                step_results,
            ),
        )))
    }

    // a^k < b^k from abs(a) < abs(b) when k in N+ and k % 2 = 0.
    fn try_pow_lt_even_exponent_from_abs_lt(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) = self.verify_even_exponent_in_n_pos_subgoal(
            left_pow.exponent.as_ref(),
            lf,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let abs_lt: AtomicFact = self
            .new_less_fact(
                Abs::new(left_pow.base.as_ref().clone()).into(),
                Abs::new(right_pow.base.as_ref().clone()).into(),
                lf.clone(),
            )
            .into();
        let Some(abs_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&abs_lt, builtin_state)?
        else {
            return Ok(None);
        };
        step_results.push(abs_result);
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^k < b^k from abs(a) < abs(b) and even k in N+".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLtEvenExponentFromAbsLt,
                ),
                step_results,
            ),
        )))
    }

    // Even powers compare absolute values: x^k <= y^k gives abs(x) <= abs(y).
    // Example: `k % 2 = 0`, `x^k <= y^k` => `abs(x) <= abs(y)`.
    fn try_abs_le_from_even_power_le(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (&f.left, &f.right) else {
            return Ok(None);
        };
        let candidates =
            self.collect_known_power_le_candidates(left_abs.arg.as_ref(), right_abs.arg.as_ref());
        for candidate in candidates {
            let AtomicFact::LessEqualFact(power_le) = &candidate else {
                continue;
            };
            let Obj::Pow(left_pow) = &power_le.left else {
                continue;
            };
            let Some(mut steps) = self.verify_even_exponent_in_n_pos_subgoal(
                left_pow.exponent.as_ref(),
                &f.line_file,
                builtin_state,
            )?
            else {
                continue;
            };
            let x_in_r: AtomicFact = self
                .new_in_fact(
                    left_abs.arg.as_ref().clone(),
                    StandardSet::R.into(),
                    f.line_file.clone(),
                )
                .into();
            let y_in_r: AtomicFact = self
                .new_in_fact(
                    right_abs.arg.as_ref().clone(),
                    StandardSet::R.into(),
                    f.line_file.clone(),
                )
                .into();
            let Some(x_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&x_in_r, builtin_state)?
            else {
                continue;
            };
            let Some(y_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&y_in_r, builtin_state)?
            else {
                continue;
            };
            let Some(power_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?
            else {
                continue;
            };
            steps.push(x_result);
            steps.push(y_result);
            steps.push(power_result);
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "abs(x) <= abs(y) from x^k <= y^k and even k in N+".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryAbsLeFromEvenPowerLe,
                    ),
                    steps,
                ),
            )));
        }
        Ok(None)
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if !Self::objs_have_same_display(left_pow.exponent.as_ref(), right_pow.exponent.as_ref()) {
            return Ok(None);
        }

        let zero = Self::literal_zero_obj();
        let exponent = left_pow.exponent.as_ref();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();

        let positive_exponent: AtomicFact = self
            .new_less_fact(zero.clone(), exponent.clone(), lf.clone())
            .into();
        let positive_left: AtomicFact = self
            .new_less_fact(zero.clone(), left_base.clone(), lf.clone())
            .into();
        let positive_right: AtomicFact = self
            .new_less_fact(zero, right_base.clone(), lf.clone())
            .into();
        let base_order: AtomicFact = self
            .new_less_fact(left_base.clone(), right_base.clone(), lf.clone())
            .into();
        let Some(premise_result) = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_in_fact(exponent.clone(), StandardSet::R.into(), lf.clone())
                        .into(),
                    positive_exponent.clone(),
                    positive_left.clone(),
                    positive_right.clone(),
                    base_order.clone(),
                ],
                vec![
                    self.new_in_fact(exponent.clone(), StandardSet::Q.into(), lf.clone())
                        .into(),
                    positive_exponent,
                    positive_left,
                    positive_right,
                    base_order,
                ],
            ],
            lf.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let step_results = vec![premise_result];

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^q < b^q from 0 < a, 0 < b, a < b, 0 < q, and q in R or Q".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLtSamePositiveRealExponentPositiveBase,
                ),
                step_results,
            ),
        )))
    }

    // Positive-real powers reflect strict order on positive bases.
    // Example: `0 < a`, `0 < b`, `0 < q`, and `a^q < b^q` imply `a < b`.
    fn try_base_lt_from_pow_lt_same_positive_real_exponent_positive_base(
        &mut self,
        f: &LessFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let candidates = self.collect_known_power_lt_candidates(&f.left, &f.right);
        for candidate in candidates {
            let AtomicFact::LessFact(power_lt) = &candidate else {
                continue;
            };
            let (Obj::Pow(left_pow), Obj::Pow(_)) = (&power_lt.left, &power_lt.right) else {
                continue;
            };
            let Some(mut steps) = self.verify_positive_real_power_operands(
                &f.left,
                &f.right,
                left_pow.exponent.as_ref(),
                &f.line_file,
                true,
                builtin_state,
            )?
            else {
                continue;
            };

            let Some(power_result) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&candidate, builtin_state)?
            else {
                continue;
            };
            steps.push(power_result);
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a < b from positive bases and exponent, and a^q < b^q".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryBaseLtFromPowLtSamePositiveRealExponentPositiveBase),
                    steps,
                ),
            )));
        }
        Ok(None)
    }

    // a^n < b^n from a < b when n is a positive odd integer.
    // Example: from `a < b`, prove `a^3 < b^3`.
    fn try_pow_lt_same_positive_odd_integer_exponent(
        &mut self,
        left_pow: &Pow,
        right_pow: &Pow,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let Some(mut step_results) = self.verify_odd_exponent_in_n_pos_subgoal(
            left_pow.exponent.as_ref(),
            lf,
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        let subgoal: AtomicFact = self
            .new_less_fact(left_base.clone(), right_base.clone(), lf.clone())
            .into();
        let Some(result) = self.try_verify_order_subgoal(subgoal, builtin_state)? else {
            return Ok(None);
        };
        step_results.push(result);

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < b^n from a < b and positive odd integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLtSamePositiveOddIntegerExponent,
                ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(pow.exponent.as_ref(), lf, builtin_state)?
        else {
            return Ok(None);
        };

        let zero = Self::literal_zero_obj();
        let base_nonpositive: AtomicFact = self
            .new_less_equal_fact(pow.base.as_ref().clone(), zero, lf.clone())
            .into();
        let Some(base_result) = self.try_verify_order_subgoal(base_nonpositive, builtin_state)?
        else {
            return Ok(None);
        };
        step_results.push(base_result);

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n <= 0 from a <= 0 and positive odd integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLeZeroOddExponentFromNonpositiveBase,
                ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(mut step_results) =
            self.verify_odd_exponent_in_n_pos_subgoal(pow.exponent.as_ref(), lf, builtin_state)?
        else {
            return Ok(None);
        };

        let zero = Self::literal_zero_obj();
        let base_negative: AtomicFact = self
            .new_less_fact(pow.base.as_ref().clone(), zero, lf.clone())
            .into();
        let Some(base_result) = self.try_verify_order_subgoal(base_negative, builtin_state)? else {
            return Ok(None);
        };
        step_results.push(base_result);

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < 0 from a < 0 and positive odd integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLtZeroOddExponentFromNegativeBase,
                ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if left_pow.exponent.to_string() != right_pow.exponent.to_string() {
            return Ok(None);
        }
        let mut subgoals = Vec::new();
        if !Self::obj_is_positive_integer_number(left_pow.exponent.as_ref()) {
            subgoals.push(
                self.new_in_fact(
                    left_pow.exponent.as_ref().clone(),
                    StandardSet::NPos.into(),
                    lf.clone(),
                )
                .into(),
            );
        }

        let z = Self::literal_zero_obj();
        let left_base = left_pow.base.as_ref();
        let right_base = right_pow.base.as_ref();
        subgoals.push(
            self.new_less_equal_fact(z, left_base.clone(), lf.clone())
                .into(),
        );
        subgoals.push(
            self.new_less_fact(left_base.clone(), right_base.clone(), lf.clone())
                .into(),
        );
        let Some(step_results) = self.verify_builtin_rule_premises(&subgoals, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a^n < b^n from 0 <= a, a < b, and positive integer n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryPowLtSamePositiveIntegerExponentNonnegativeBase,
                ),
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        for (premises, message, rule) in [
            (
                vec![
                    self.new_less_equal_fact(z.clone(), x.clone(), lf.clone())
                        .into(),
                    self.new_less_equal_fact(u.clone(), v.clone(), lf.clone())
                        .into(),
                ],
                msg_nonneg,
                ArithmeticBuiltinRule::MulCommonFactorLessEqualNonnegative,
            ),
            (
                vec![
                    self.new_less_equal_fact(x.clone(), z, lf.clone()).into(),
                    self.new_less_equal_fact(v.clone(), u.clone(), lf.clone())
                        .into(),
                ],
                msg_nonpos,
                ArithmeticBuiltinRule::MulCommonFactorLessEqualNonpositive,
            ),
        ] {
            let mut children = Vec::with_capacity(premises.len());
            for premise in premises {
                let Some(result) = self.try_verify_order_subgoal(premise, builtin_state)? else {
                    children.clear();
                    break;
                };
                children.push(result);
            }
            if children.len() == 2 {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        message.to_string(),
                        BuiltinRuleEvidence::Arithmetic(rule),
                        children,
                    ),
                )));
            }
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        for (premises, message, rule) in [
            (
                vec![
                    self.new_less_fact(z.clone(), x.clone(), lf.clone()).into(),
                    self.new_less_fact(u.clone(), v.clone(), lf.clone()).into(),
                ],
                msg_pos,
                ArithmeticBuiltinRule::MulCommonFactorLessPositive,
            ),
            (
                vec![
                    self.new_less_fact(x.clone(), z, lf.clone()).into(),
                    self.new_less_fact(v.clone(), u.clone(), lf.clone()).into(),
                ],
                msg_neg,
                ArithmeticBuiltinRule::MulCommonFactorLessNegative,
            ),
        ] {
            let mut children = Vec::with_capacity(premises.len());
            for premise in premises {
                let Some(result) = self.try_verify_order_subgoal(premise, builtin_state)? else {
                    children.clear();
                    break;
                };
                children.push(result);
            }
            if children.len() == 2 {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        message.to_string(),
                        BuiltinRuleEvidence::Arithmetic(rule),
                        children,
                    ),
                )));
            }
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let nonnegative = vec![
            self.new_less_equal_fact(z.clone(), l1.clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(z.clone(), l2.clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(z.clone(), r1.clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(z, r2.clone(), lf.clone()).into(),
        ];
        let mut direct = nonnegative.clone();
        direct.push(
            self.new_less_equal_fact(l1.clone(), r1.clone(), lf.clone())
                .into(),
        );
        direct.push(
            self.new_less_equal_fact(l2.clone(), r2.clone(), lf.clone())
                .into(),
        );
        let mut crossed = nonnegative;
        crossed.push(
            self.new_less_equal_fact(l1.clone(), r2.clone(), lf.clone())
                .into(),
        );
        crossed.push(
            self.new_less_equal_fact(l2.clone(), r1.clone(), lf.clone())
                .into(),
        );
        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![direct, crossed],
            lf.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "x1 * x2 <= y1 * y2 from 0 <= factors and either componentwise pairing"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryMulLeComponentwiseNonnegativeFactors,
                    ),
                    vec![premise_result],
                ),
            )));
        }
        Ok(None)
    }

    // 0 <= a*b when a,b have the same weak sign; a*b <= 0 when they have opposite weak signs.
    // Example: from `a <= 0` and `0 <= b`, prove `a * b <= 0`.
    fn try_mul_le_zero_by_weak_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_less_equal_fact(left.clone(), z.clone(), lf.clone())
                        .into(),
                    self.new_less_equal_fact(z.clone(), right.clone(), lf.clone())
                        .into(),
                ],
                vec![
                    self.new_less_equal_fact(right.clone(), z.clone(), lf.clone())
                        .into(),
                    self.new_less_equal_fact(z, left.clone(), lf.clone()).into(),
                ],
            ],
            lf.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a * b <= 0 from either opposite weak-sign pairing".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryMulLeZeroByWeakSigns,
                    ),
                    vec![premise_result],
                ),
            )));
        }
        Ok(None)
    }

    fn try_zero_le_mul_by_weak_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_less_equal_fact(z.clone(), left.clone(), lf.clone())
                        .into(),
                    self.new_less_equal_fact(z.clone(), right.clone(), lf.clone())
                        .into(),
                ],
                vec![
                    self.new_less_equal_fact(left.clone(), z.clone(), lf.clone())
                        .into(),
                    self.new_less_equal_fact(right.clone(), z, lf.clone())
                        .into(),
                ],
            ],
            lf.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 <= a * b from either same weak-sign branch".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryZeroLeMulByWeakSigns,
                    ),
                    vec![premise_result],
                ),
            )));
        }
        Ok(None)
    }

    // Strict product sign rules require both factors to be strictly away from zero.
    fn try_mul_lt_zero_by_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_less_fact(left.clone(), z.clone(), lf.clone())
                        .into(),
                    self.new_less_fact(z.clone(), right.clone(), lf.clone())
                        .into(),
                ],
                vec![
                    self.new_less_fact(right.clone(), z.clone(), lf.clone())
                        .into(),
                    self.new_less_fact(z, left.clone(), lf.clone()).into(),
                ],
            ],
            lf.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a * b < 0 from either opposite strict-sign pairing".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryMulLtZeroBySigns),
                    vec![premise_result],
                ),
            )));
        }
        Ok(None)
    }

    fn try_zero_lt_mul_by_signs(
        &mut self,
        left: &Obj,
        right: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let alternatives = vec![
            vec![
                self.new_less_fact(z.clone(), left.clone(), lf.clone())
                    .into(),
                self.new_less_fact(z.clone(), right.clone(), lf.clone())
                    .into(),
            ],
            vec![
                self.new_less_fact(z.clone(), right.clone(), lf.clone())
                    .into(),
                self.new_less_fact(z.clone(), left.clone(), lf.clone())
                    .into(),
            ],
            vec![
                self.new_less_fact(left.clone(), z.clone(), lf.clone())
                    .into(),
                self.new_less_fact(right.clone(), z.clone(), lf.clone())
                    .into(),
            ],
            vec![
                self.new_less_fact(right.clone(), z.clone(), lf.clone())
                    .into(),
                self.new_less_fact(left.clone(), z.clone(), lf.clone())
                    .into(),
            ],
        ];
        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            alternatives,
            lf.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 < a * b from either same strict-sign branch".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryZeroLtMulBySigns),
                    vec![premise_result],
                ),
            )));
        }
        Ok(None)
    }

    // Finite sum monotonicity on a shared range, using the summand's unary
    // parameter set when it is explicit.
    // Example: from `forall i N+: m <= i <= n => f(i) <= g(i)`, prove
    // `sum(m, n, fn(i N+) R {f(i)}) <= sum(m, n, fn(i N+) R {g(i)})`.
    pub fn try_less_equal_sum_pointwise_on_same_integer_range(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (Obj::Sum(left_sum), Obj::Sum(right_sum)) = (&f.left, &f.right) else {
            return Ok(None);
        };

        let start_equality: AtomicFact = self
            .new_equal_fact(
                left_sum.start.as_ref().clone(),
                right_sum.start.as_ref().clone(),
                f.line_file.clone(),
            )
            .into();
        let start_result = self.verify_atomic_fact(&start_equality, verify_state)?;
        if !start_result.is_success() {
            return Ok(None);
        }
        let end_equality: AtomicFact = self
            .new_equal_fact(
                left_sum.end.as_ref().clone(),
                right_sum.end.as_ref().clone(),
                f.line_file.clone(),
            )
            .into();
        let end_result = self.verify_atomic_fact(&end_equality, verify_state)?;
        if !end_result.is_success() {
            return Ok(None);
        }
        let left_param_set = Self::unary_anonymous_function_param_set(left_sum.func.as_ref());
        let right_param_set = Self::unary_anonymous_function_param_set(right_sum.func.as_ref());
        let index_param_set = match (left_param_set, right_param_set) {
            (Some(left_set), Some(right_set)) => {
                let set_result = self.verify_atomic_fact(
                    &self
                        .new_equal_fact(left_set.clone(), right_set, f.line_file.clone())
                        .into(),
                    verify_state,
                )?;
                if !set_result.is_success() {
                    return Ok(None);
                }
                left_set
            }
            (Some(left_set), None) => left_set,
            (None, Some(right_set)) => right_set,
            (None, None) => StandardSet::Z.into(),
        };

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(left_inst) = self.instantiate_unary_function_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let pointwise_fact: AtomicFact = self
            .new_less_equal_fact(left_inst, right_inst, f.line_file.clone())
            .into();
        let dom_lo: Fact = self
            .new_less_equal_fact(
                (*left_sum.start).clone(),
                x_obj.clone(),
                f.line_file.clone(),
            )
            .into();
        let dom_hi: Fact = self
            .new_less_equal_fact(x_obj, (*left_sum.end).clone(), f.line_file.clone())
            .into();
        let pointwise_forall = self.new_forall_fact(
            TypedParameterList::new(vec![TypedParameterGroup::new(
                vec![x_binding],
                ParamType::Obj(index_param_set),
            )]),
            vec![dom_lo, dom_hi],
            vec![pointwise_fact.into()],
            f.line_file.clone(),
        )?;
        let pointwise_fact: Fact = pointwise_forall.clone().into();
        let pointwise_result = self.verify_forall_fact(&pointwise_forall, verify_state)?;
        if !pointwise_result.is_success() {
            return Ok(None);
        }

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "finite sum monotonicity from pointwise order on the index range".to_string(),
                BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(
                    IntegerRangeSumPointwiseOrderBuiltinRuleEvidence::new(
                        atomic_fact.clone().into(),
                        start_equality.into(),
                        end_equality.into(),
                        pointwise_fact,
                    ),
                ),
                vec![start_result, end_result, pointwise_result],
            ),
        )))
    }

    // Finite-set sum monotonicity on a shared finite set.
    // Example: from `forall x X: f(x) <= g(x)`, prove
    // `finite_set_sum(X, f) <= finite_set_sum(X, g)`.
    pub fn try_less_equal_finite_set_sum_pointwise_on_same_set(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (Obj::SumOfFiniteSet(left_sum), Obj::SumOfFiniteSet(right_sum)) = (&f.left, &f.right)
        else {
            return Ok(None);
        };

        let set_result = self.verify_atomic_fact(
            &self
                .new_equal_fact(
                    left_sum.set.as_ref().clone(),
                    right_sum.set.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into(),
            verify_state,
        )?;
        if !set_result.is_success() {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(left_inst) = self.instantiate_unary_function_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let pointwise_fact: AtomicFact = self
            .new_less_equal_fact(left_inst, right_inst, f.line_file.clone())
            .into();
        let pointwise_result =
            self.run_in_local_verification_env(verify_state, |rt, local_verify_state| {
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![x_binding],
                    ParamType::Obj(left_sum.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                rt.verify_atomic_fact(&pointwise_fact, local_verify_state)
            })?;
        if !pointwise_result.is_success() {
            return Ok(None);
        }

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "finite-set sum monotonicity from pointwise order on the finite set".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryLessEqualFiniteSetSumPointwiseOnSameSet,
                ),
                vec![set_result, pointwise_result],
            ),
        )))
    }

    // A non-negative summand is no larger than the finite sum containing it.
    // Example: from `x $in X` and `forall y X: h(y) >= 0`, prove
    // `h(x) <= finite_set_sum(X, h)`.
    pub fn try_less_equal_finite_set_summand_nonnegative_sum(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::SumOfFiniteSet(sum) = &f.right else {
            return Ok(None);
        };
        let Obj::FnObj(call) = &f.left else {
            return Ok(None);
        };
        let [args] = call.body.as_slice() else {
            return Ok(None);
        };
        let [member] = args.as_slice() else {
            return Ok(None);
        };
        let member = member.as_ref().clone();

        let Some(summand) = self.instantiate_unary_function_at(sum.func.as_ref(), &member)? else {
            return Ok(None);
        };
        let summand_result = self.verify_atomic_fact(
            &self
                .new_equal_fact(f.left.clone(), summand, f.line_file.clone())
                .into(),
            verify_state,
        )?;
        if !summand_result.is_success() {
            return Ok(None);
        }

        let member_fact: AtomicFact = self
            .new_in_fact(member, sum.set.as_ref().clone(), f.line_file.clone())
            .into();
        let member_result = self.verify_atomic_fact(&member_fact, verify_state)?;
        if !member_result.is_success() {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(summand_at_x) = self.instantiate_unary_function_at(sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let nonnegative_fact: AtomicFact = self
            .new_less_equal_fact(Self::literal_zero_obj(), summand_at_x, f.line_file.clone())
            .into();
        let nonnegative_result =
            self.run_in_local_verification_env(verify_state, |rt, local_verify_state| {
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![x_binding],
                    ParamType::Obj(sum.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                rt.verify_atomic_fact(&nonnegative_fact, local_verify_state)
            })?;
        if !nonnegative_result.is_success() {
            return Ok(None);
        }

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "finite-set sum: non-negative summand is at most the total".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryLessEqualFiniteSetSummandNonnegativeSum,
                ),
                vec![summand_result, member_result, nonnegative_result],
            ),
        )))
    }

    fn try_less_equal_algebra(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();
        let structural_state = VerifyState::initial();

        if let Some(result) = self.try_less_equal_sum_pointwise_on_same_integer_range(
            f,
            atomic_fact,
            &structural_state,
        )? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_less_equal_finite_set_sum_pointwise_on_same_set(
            f,
            atomic_fact,
            &structural_state,
        )? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_less_equal_finite_set_summand_nonnegative_sum(
            f,
            atomic_fact,
            &structural_state,
        )? {
            return Ok(Some(result));
        }

        // Prefer the exact same-denominator rule before the more general
        // denominator-moving rules below.  The latter may explore a harder
        // product goal; failed exploration intentionally consumes the shared
        // builtin recursion budget.
        if let (Obj::Div(left_div), Obj::Div(right_div)) = (&f.left, &f.right) {
            if left_div.right.to_string() == right_div.right.to_string() {
                let denominator = left_div.right.as_ref();
                let positive_denominator: AtomicFact = self
                    .new_less_fact(z.clone(), denominator.clone(), lf.clone())
                    .into();
                let numerator_bound: AtomicFact = self
                    .new_less_equal_fact(
                        left_div.left.as_ref().clone(),
                        right_div.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into();
                let positive_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &positive_denominator,
                    builtin_state,
                )?;
                if let Some(positive_result) = positive_result {
                    let numerator_result =
                        self.try_verify_order_subgoal(numerator_bound, builtin_state)?;
                    if let Some(numerator_result) = numerator_result {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "a / c <= b / c from 0 < c and a <= b".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra01),
                                vec![positive_result, numerator_result],
                            ),
                        )));
                    }
                }

                let negative_denominator: AtomicFact = self
                    .new_less_fact(denominator.clone(), z.clone(), lf.clone())
                    .into();
                let reversed_numerator_bound: AtomicFact = self
                    .new_less_equal_fact(
                        right_div.left.as_ref().clone(),
                        left_div.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into();
                let negative_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &negative_denominator,
                    builtin_state,
                )?;
                if let Some(negative_result) = negative_result {
                    let numerator_result =
                        self.try_verify_order_subgoal(reversed_numerator_bound, builtin_state)?;
                    if let Some(numerator_result) = numerator_result {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "b / c <= a / c from c < 0 and a <= b".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra02),
                                vec![negative_result, numerator_result],
                            ),
                        )));
                    }
                }
            }
        }

        if let (Obj::Pow(left_pow), Obj::Pow(right_pow)) = (&f.left, &f.right) {
            if let Some(r) = self.try_pow_le_same_positive_integer_exponent_nonnegative_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_le_same_positive_odd_integer_exponent(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self
                .try_pow_le_same_negative_integer_exponent_positive_base_reverses_order(
                    left_pow,
                    right_pow,
                    lf,
                    atomic_fact,
                    builtin_state,
                )?
            {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_le_even_exponent_from_abs_le(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
        }

        if let Some(r) = self
            .try_base_le_from_pow_le_same_positive_integer_exponent_nonnegative_base(
                f,
                atomic_fact,
                builtin_state,
            )?
        {
            return Ok(Some(r));
        }

        if let Some(r) = self.try_base_le_from_pow_le_same_positive_real_exponent_positive_base(
            f,
            atomic_fact,
            builtin_state,
        )? {
            return Ok(Some(r));
        }

        if let Some(r) = self.try_abs_le_from_even_power_le(f, atomic_fact, builtin_state)? {
            return Ok(Some(r));
        }

        if let Some(r) =
            self.try_less_equal_from_positive_division_product_bound(f, atomic_fact, builtin_state)?
        {
            return Ok(Some(r));
        }

        if let Some(r) =
            self.try_less_equal_from_positive_denominator_bound(f, atomic_fact, builtin_state)?
        {
            return Ok(Some(r));
        }

        if let (Obj::Add(left_add), Obj::Add(right_add)) = (&f.left, &f.right) {
            if let Some((left_remaining, right_remaining)) =
                Self::add_common_remaining(left_add, right_add)
            {
                let subgoal: AtomicFact = self
                    .new_less_equal_fact(left_remaining, right_remaining, lf.clone())
                    .into();
                if let Some(result) = self.try_verify_order_subgoal(subgoal, builtin_state)? {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "u + a <= u + b from a <= b".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::AddCommonLeftLessEqual,
                            ),
                            vec![result],
                        ),
                    )));
                }
            }
        }

        if let Obj::Sub(sub) = &f.left {
            // Exchange the target subtrahend with the weak upper bound.
            // Example: from `a - b <= c`, prove `a - c <= b`.
            let swapped_left: Obj = Sub::new(sub.left.as_ref().clone(), f.right.clone()).into();
            let swapped_subgoal: AtomicFact = self
                .new_less_equal_fact(swapped_left, sub.right.as_ref().clone(), lf.clone())
                .into();
            if let Some(swapped_result) =
                self.try_verify_order_subgoal(swapped_subgoal, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c <= b from a - b <= c".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::SubLessEqualSwap,
                        ),
                        vec![swapped_result],
                    ),
                )));
            }

            // Subtracting a nonnegative term cannot increase the left side.
            // Example: from `a <= b` and `0 <= c`, prove `a - c <= b`.
            let order_subgoal: AtomicFact = self
                .new_less_equal_fact(sub.left.as_ref().clone(), f.right.clone(), lf.clone())
                .into();
            let nonnegative_subtractor: AtomicFact = self
                .new_less_equal_fact(z.clone(), sub.right.as_ref().clone(), lf.clone())
                .into();
            let order_result = self.try_verify_order_subgoal(order_subgoal, builtin_state)?;
            let nonnegative_result =
                self.try_verify_order_subgoal(nonnegative_subtractor, builtin_state)?;
            if let (Some(order_result), Some(nonnegative_result)) =
                (order_result, nonnegative_result)
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c <= b from a <= b and 0 <= c".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::SubRightNonnegativeLessEqual,
                        ),
                        vec![order_result, nonnegative_result],
                    ),
                )));
            }

            // Move a left subtractor to the right side as an addend.
            // Example: from `a <= b + c`, prove `a - c <= b`.
            for shifted_right in [
                Add::new(f.right.clone(), sub.right.as_ref().clone()).into(),
                Add::new(sub.right.as_ref().clone(), f.right.clone()).into(),
            ] {
                let shifted_subgoal: AtomicFact = self
                    .new_less_equal_fact(sub.left.as_ref().clone(), shifted_right, lf.clone())
                    .into();
                if let Some(shifted_result) =
                    self.try_verify_order_subgoal(shifted_subgoal, builtin_state)?
                {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "a - c <= b from a <= b + c".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::LessEqualAddImpliesSubLessEqual,
                            ),
                            vec![shifted_result],
                        ),
                    )));
                }
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
                let g0 = self.new_less_equal_fact(z.clone(), b, lf.clone()).into();
                if let Some(r0) = self.try_verify_order_subgoal(g0, builtin_state)? {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "a <= a + b from 0 <= b".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::AddRightNonnegativeLessEqual,
                            ),
                            vec![r0],
                        ),
                    )));
                }
            }
            // a <= u + v from a <= u and 0 <= v (or symmetric addends).
            let g_a_left = self
                .new_less_equal_fact(f.left.clone(), add.left.as_ref().clone(), lf.clone())
                .into();
            let g0_right = self
                .new_less_equal_fact(z.clone(), add.right.as_ref().clone(), lf.clone())
                .into();
            let g_a_right = self
                .new_less_equal_fact(f.left.clone(), add.right.as_ref().clone(), lf.clone())
                .into();
            let g0_left = self
                .new_less_equal_fact(z.clone(), add.left.as_ref().clone(), lf.clone())
                .into();
            let premise_result = self.try_verify_builtin_rule_premise_alternatives(
                vec![vec![g_a_left, g0_right], vec![g_a_right, g0_left]],
                lf.clone(),
                builtin_state,
            )?;
            if let Some(premise_result) = premise_result {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b + c from either compatible addend-bound conjunction".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra04),
                        vec![premise_result],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.right {
            // Move a right subtractor to the left side as an addend.
            // Example: from `a + c <= b`, prove `a <= b - c`.
            let shifted_left: Obj = Add::new(f.left.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact = self
                .new_less_equal_fact(shifted_left, sub.left.as_ref().clone(), lf.clone())
                .into();
            if let Some(shifted_result) =
                self.try_verify_order_subgoal(shifted_subgoal, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b - c from a + c <= b".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra05),
                        vec![shifted_result],
                    ),
                )));
            }

            if let Some(offset) = Self::integer_value_of_number_obj(sub.right.as_ref()) {
                if offset >= 0 {
                    let shifted_left = Self::obj_plus_nonnegative_integer_offset(&f.left, offset);
                    let subgoal: AtomicFact = self
                        .new_less_equal_fact(shifted_left, sub.left.as_ref().clone(), lf.clone())
                        .into();
                    if let Some(result) = self.try_verify_order_subgoal(subgoal, builtin_state)? {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "a <= x - n from a + n <= x".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra06),
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
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - n <= a for n >= 0".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra07),
                        Vec::new(),
                    ),
                )));
            }
        }

        if f.right.to_string() == z.to_string() {
            // A sum of nonpositive real terms is nonpositive.
            // Example: `a <= 0, b <= 0 => a + b <= 0`.
            if let Obj::Add(add) = &f.left {
                let left_nonpositive: AtomicFact = self
                    .new_less_equal_fact(add.left.as_ref().clone(), z.clone(), lf.clone())
                    .into();
                let right_nonpositive: AtomicFact = self
                    .new_less_equal_fact(add.right.as_ref().clone(), z.clone(), lf.clone())
                    .into();
                let left_result = self.try_verify_order_subgoal(left_nonpositive, builtin_state)?;
                let right_result =
                    self.try_verify_order_subgoal(right_nonpositive, builtin_state)?;
                if let (Some(left_result), Some(right_result)) = (left_result, right_result) {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "a + b <= 0 from a <= 0 and b <= 0".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra08),
                            vec![left_result, right_result],
                        ),
                    )));
                }
            }
            if let Obj::Pow(pow) = &f.left {
                if let Some(r) = self.try_pow_le_zero_odd_exponent_from_nonpositive_base(
                    pow,
                    lf,
                    atomic_fact,
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
            if let Obj::Mul(m) = &f.left {
                if let Some(r) = self.try_mul_le_zero_by_weak_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                    builtin_state,
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
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = self
                    .new_less_equal_fact(z.clone(), f.left.clone(), lf.clone())
                    .into();
                let g1 = self
                    .new_less_equal_fact(one, m.left.as_ref().clone(), lf.clone())
                    .into();
                let Some(r0) = self.try_verify_order_subgoal(g0, builtin_state)? else {
                    return Ok(None);
                };
                let Some(r1) = self.try_verify_order_subgoal(g1, builtin_state)? else {
                    return Ok(None);
                };
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b * a from 0 <= a and 1 <= b".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualAlgebra09),
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
                builtin_state,
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
                    builtin_state,
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
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1 = self
                .new_less_equal_fact(
                    al.left.as_ref().clone(),
                    bl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2 = self
                .new_less_equal_fact(
                    al.right.as_ref().clone(),
                    bl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let Some(r1) = self.try_verify_order_subgoal(g1, builtin_state)? else {
                return Ok(None);
            };
            let Some(r2) = self.try_verify_order_subgoal(g2, builtin_state)? else {
                return Ok(None);
            };
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a + c <= b + d from a <= b and c <= d".to_string(),
                    BuiltinRuleEvidence::Arithmetic(
                        ArithmeticBuiltinRule::AddComponentwiseLessEqual,
                    ),
                    vec![r1, r2],
                ),
            )));
        }

        if let (Obj::Sub(sl), Obj::Sub(sr)) = (&f.left, &f.right) {
            // Componentwise weak monotonicity for subtraction.
            // Example: from `a <= b` and `c <= d`, prove `a - d <= b - c`.
            let g1 = self
                .new_less_equal_fact(
                    sl.left.as_ref().clone(),
                    sr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2 = self
                .new_less_equal_fact(
                    sr.right.as_ref().clone(),
                    sl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let Some(r1) = self.try_verify_order_subgoal(g1, builtin_state)? else {
                return Ok(None);
            };
            let Some(r2) = self.try_verify_order_subgoal(g2, builtin_state)? else {
                return Ok(None);
            };
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "a - d <= b - c from a <= b and c <= d".to_string(),
                    BuiltinRuleEvidence::Arithmetic(
                        ArithmeticBuiltinRule::SubComponentwiseLessEqual,
                    ),
                    vec![r1, r2],
                ),
            )));
        }

        Ok(None)
    }

    // A positive factor can be moved across a weak inequality and expressed as division.
    // Example: from `0 < c` and `c * a <= b or a * c <= b`, prove `a <= b / c`.
    fn try_less_equal_from_positive_division_product_bound(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Div(quotient) = &f.right else {
            return Ok(None);
        };

        let denominator = quotient.right.as_ref().clone();
        let numerator = quotient.left.as_ref().clone();
        let line_file = f.line_file.clone();
        let positive_denominator: AtomicFact = self
            .new_less_fact(
                Self::literal_zero_obj(),
                denominator.clone(),
                line_file.clone(),
            )
            .into();
        let Some(positive_result) = self
            .try_verify_atomic_fact_as_builtin_rule_premise(&positive_denominator, builtin_state)?
        else {
            return Ok(None);
        };

        let left_product: Obj = Mul::new(denominator.clone(), f.left.clone()).into();
        let right_product: Obj = Mul::new(f.left.clone(), denominator).into();
        let left_product_bound: AtomicFact = self
            .new_less_equal_fact(left_product, numerator.clone(), line_file.clone())
            .into();
        let right_product_bound: AtomicFact = self
            .new_less_equal_fact(right_product, numerator, line_file)
            .into();
        let product_bound_premise = QuantifierFreeFact::OrFact(self.new_or_fact(
            vec![left_product_bound.into(), right_product_bound.into()],
            f.line_file.clone(),
        ));
        let Some(product_bound_result) =
            self.try_verify_builtin_rule_premise(&product_bound_premise, builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "a <= b / c from 0 < c and (c * a <= b or a * c <= b)".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryLessEqualFromPositiveDivisionProductBound,
                ),
                vec![positive_result, product_bound_result],
            ),
        )))
    }

    // A positive denominator can be moved across a weak quotient inequality.
    // Example: from `0 < c` and `a / c <= b`, prove `a <= b * c`.
    fn try_less_equal_from_positive_denominator_bound(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Mul(product) = &f.right else {
            return Ok(None);
        };

        let line_file = f.line_file.clone();
        let candidates = [
            (
                product.left.as_ref().clone(),
                product.right.as_ref().clone(),
            ),
            (
                product.right.as_ref().clone(),
                product.left.as_ref().clone(),
            ),
        ];
        for (denominator, other_factor) in candidates {
            let positive_denominator: AtomicFact = self
                .new_less_fact(
                    Self::literal_zero_obj(),
                    denominator.clone(),
                    line_file.clone(),
                )
                .into();
            let Some(positive_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &positive_denominator,
                builtin_state,
            )?
            else {
                continue;
            };

            let quotient: Obj = Div::new(f.left.clone(), denominator).into();
            let quotient_bound: AtomicFact = self
                .new_less_equal_fact(quotient, other_factor, line_file.clone())
                .into();
            if let Some(quotient_bound_result) =
                self.try_verify_order_subgoal(quotient_bound, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b * c from 0 < c and a / c <= b".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessEqualFromPositiveDenominatorBound),
                        vec![positive_result, quotient_bound_result],
                    ),
                )));
            }
        }

        Ok(None)
    }

    fn try_less_algebra(
        &mut self,
        f: &LessFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();

        // As in the weak-order dispatcher, handle the exact same-denominator
        // shape before attempting more general algebraic rewrites.
        if let (Obj::Div(left_div), Obj::Div(right_div)) = (&f.left, &f.right) {
            if left_div.right.to_string() == right_div.right.to_string() {
                let denominator = left_div.right.as_ref();
                let positive_denominator: AtomicFact = self
                    .new_less_fact(z.clone(), denominator.clone(), lf.clone())
                    .into();
                let numerator_bound: AtomicFact = self
                    .new_less_fact(
                        left_div.left.as_ref().clone(),
                        right_div.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into();
                if let Some(positive_result) =
                    self.try_verify_order_subgoal(positive_denominator, builtin_state)?
                {
                    let numerator_result =
                        self.try_verify_order_subgoal(numerator_bound, builtin_state)?;
                    if let Some(numerator_result) = numerator_result {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "a / c < b / c from 0 < c and a < b".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra01),
                                vec![positive_result, numerator_result],
                            ),
                        )));
                    }
                }

                let negative_denominator: AtomicFact = self
                    .new_less_fact(denominator.clone(), z.clone(), lf.clone())
                    .into();
                let reversed_numerator_bound: AtomicFact = self
                    .new_less_fact(
                        right_div.left.as_ref().clone(),
                        left_div.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into();
                if let Some(negative_result) =
                    self.try_verify_order_subgoal(negative_denominator, builtin_state)?
                {
                    let numerator_result =
                        self.try_verify_order_subgoal(reversed_numerator_bound, builtin_state)?;
                    if let Some(numerator_result) = numerator_result {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "b / c < a / c from c < 0 and a < b".to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra02),
                                vec![negative_result, numerator_result],
                            ),
                        )));
                    }
                }
            }
        }

        if let (Obj::Pow(left_pow), Obj::Pow(right_pow)) = (&f.left, &f.right) {
            if let Some(r) = self.try_pow_lt_same_positive_integer_exponent_nonnegative_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_lt_same_positive_odd_integer_exponent(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_lt_even_exponent_from_abs_lt(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
            if let Some(r) = self.try_pow_lt_same_positive_real_exponent_positive_base(
                left_pow,
                right_pow,
                lf,
                atomic_fact,
                builtin_state,
            )? {
                return Ok(Some(r));
            }
        }

        if let Some(r) = self.try_base_lt_from_pow_lt_same_positive_real_exponent_positive_base(
            f,
            atomic_fact,
            builtin_state,
        )? {
            return Ok(Some(r));
        }

        if let (Obj::Add(left_add), Obj::Add(right_add)) = (&f.left, &f.right) {
            if let Some((left_remaining, right_remaining)) =
                Self::add_common_remaining(left_add, right_add)
            {
                let subgoal: AtomicFact = self
                    .new_less_fact(left_remaining, right_remaining, lf.clone())
                    .into();
                if let Some(result) = self.try_verify_order_subgoal(subgoal, builtin_state)? {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "u + a < u + b from a < b".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::AddCommonLeftLess,
                            ),
                            vec![result],
                        ),
                    )));
                }
            }
        }

        if let (Obj::Sub(sl), Obj::Sub(sr)) = (&f.left, &f.right) {
            // Componentwise strict monotonicity for subtraction.
            // Example: from `a < b` and `c <= d`, prove `a - d < b - c`.
            let g1s = self
                .new_less_fact(
                    sl.left.as_ref().clone(),
                    sr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2s = self
                .new_less_equal_fact(
                    sr.right.as_ref().clone(),
                    sl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let r1 = self.try_verify_order_subgoal(g1s, builtin_state)?;
            let r2 = self.try_verify_atomic_fact_as_builtin_rule_premise(&g2s, builtin_state)?;
            if let (Some(r1), Some(r2)) = (r1, r2) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - d < b - c from a < b and c <= d".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra03),
                        vec![r1, r2],
                    ),
                )));
            }

            // A strict subtractor comparison also gives a strict result.
            // Example: from `a <= b` and `c < d`, prove `a - d < b - c`.
            let g1w = self
                .new_less_equal_fact(
                    sl.left.as_ref().clone(),
                    sr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2w = self
                .new_less_fact(
                    sr.right.as_ref().clone(),
                    sl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let r3 = self.try_verify_atomic_fact_as_builtin_rule_premise(&g1w, builtin_state)?;
            let r4 = self.try_verify_order_subgoal(g2w, builtin_state)?;
            if let (Some(r3), Some(r4)) = (r3, r4) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - d < b - c from a <= b and c < d".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::SubComponentwiseLessEqualLess,
                        ),
                        vec![r3, r4],
                    ),
                )));
            }
        }

        if let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (&f.left, &f.right) {
            if let Obj::Sub(sub) = left_abs.arg.as_ref() {
                if Self::objs_have_same_display(sub.left.as_ref(), right_abs.arg.as_ref())
                    && Self::obj_is_positive_integer_number(sub.right.as_ref())
                {
                    let zero = Self::literal_zero_obj();
                    let positive_arg: AtomicFact = self
                        .new_less_fact(zero.clone(), right_abs.arg.as_ref().clone(), lf.clone())
                        .into();
                    let nonnegative_sub: AtomicFact = self
                        .new_less_equal_fact(zero, left_abs.arg.as_ref().clone(), lf.clone())
                        .into();
                    let r_pos = self.try_verify_order_subgoal(positive_arg, builtin_state)?;
                    let r_sub = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &nonnegative_sub,
                        builtin_state,
                    )?;
                    if let (Some(r_pos), Some(r_sub)) = (r_pos, r_sub) {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "abs(x - n) < abs(x) for positive x and nonnegative x - n"
                                    .to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra05),
                                vec![r_pos, r_sub],
                            ),
                        )));
                    }
                }
            }
        }

        if let Obj::Sub(sub) = &f.left {
            // Exchange the target subtrahend with the strict upper bound.
            // Example: from `a - b < c`, prove `a - c < b`.
            let swapped_left: Obj = Sub::new(sub.left.as_ref().clone(), f.right.clone()).into();
            let swapped_subgoal: AtomicFact = self
                .new_less_fact(swapped_left, sub.right.as_ref().clone(), lf.clone())
                .into();
            if let Some(swapped_result) =
                self.try_verify_order_subgoal(swapped_subgoal, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a - b < c".to_string(),
                        BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::SubLessSwap),
                        vec![swapped_result],
                    ),
                )));
            }
            // Subtracting a nonnegative term preserves a strict upper bound.
            // Example: from `a < b` and `0 <= c`, prove `a - c < b`.
            let strict_order_subgoal: AtomicFact = self
                .new_less_fact(sub.left.as_ref().clone(), f.right.clone(), lf.clone())
                .into();
            let nonnegative_subtractor: AtomicFact = self
                .new_less_equal_fact(z.clone(), sub.right.as_ref().clone(), lf.clone())
                .into();
            let strict_order_result =
                self.try_verify_order_subgoal(strict_order_subgoal, builtin_state)?;
            let nonnegative_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &nonnegative_subtractor,
                builtin_state,
            )?;
            if let (Some(strict_order_result), Some(nonnegative_result)) =
                (strict_order_result, nonnegative_result)
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a < b and 0 <= c".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra06),
                        vec![strict_order_result, nonnegative_result],
                    ),
                )));
            }

            // Subtracting a positive term turns a weak upper bound into a strict one.
            // Example: from `a <= b` and `0 < c`, prove `a - c < b`.
            let weak_order_subgoal: AtomicFact = self
                .new_less_equal_fact(sub.left.as_ref().clone(), f.right.clone(), lf.clone())
                .into();
            let positive_subtractor: AtomicFact = self
                .new_less_fact(z.clone(), sub.right.as_ref().clone(), lf.clone())
                .into();
            let weak_order_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &weak_order_subgoal,
                builtin_state,
            )?;
            let positive_result =
                self.try_verify_order_subgoal(positive_subtractor, builtin_state)?;
            if let (Some(weak_order_result), Some(positive_result)) =
                (weak_order_result, positive_result)
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a <= b and 0 < c".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra07),
                        vec![weak_order_result, positive_result],
                    ),
                )));
            }

            // Move a left subtractor to the right side as an addend.
            // Example: from `a < b + c`, prove `a - c < b`.
            let shifted_right: Obj = Add::new(f.right.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact = self
                .new_less_fact(sub.left.as_ref().clone(), shifted_right, lf.clone())
                .into();
            if let Some(shifted_result) =
                self.try_verify_order_subgoal(shifted_subgoal, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - c < b from a < b + c".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra08),
                        vec![shifted_result],
                    ),
                )));
            }
        }

        if let Obj::Add(add) = &f.right {
            // Move either target addend to the left as a subtractor.
            // Example: from `a - b < c`, prove `a < b + c`.
            for (subtrahend, remaining_bound) in [
                (add.left.as_ref(), add.right.as_ref()),
                (add.right.as_ref(), add.left.as_ref()),
            ] {
                let shifted_left: Obj = Sub::new(f.left.clone(), subtrahend.clone()).into();
                let shifted_subgoal: AtomicFact = self
                    .new_less_fact(shifted_left, remaining_bound.clone(), lf.clone())
                    .into();
                if let Some(shifted_result) =
                    self.try_verify_order_subgoal(shifted_subgoal, builtin_state)?
                {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "a < b + c from a - b < c".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::SubLessImpliesLessAdd,
                            ),
                            vec![shifted_result],
                        ),
                    )));
                }
            }
            let left_s = f.left.to_string();
            let b_opt = if add.left.as_ref().to_string() == left_s {
                Some(add.right.as_ref().clone())
            } else if add.right.as_ref().to_string() == left_s {
                Some(add.left.as_ref().clone())
            } else {
                None
            };
            if let Some(b) = b_opt {
                let g0 = self.new_less_fact(z.clone(), b, lf.clone()).into();
                if let Some(r0) = self.try_verify_order_subgoal(g0, builtin_state)? {
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "a < a + b from 0 < b".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra09),
                            vec![r0],
                        ),
                    )));
                }
            }
            // a < u + v from a < u and 0 <= v (or symmetric addends).
            let g_a_left = self
                .new_less_fact(f.left.clone(), add.left.as_ref().clone(), lf.clone())
                .into();
            let g0_right = self
                .new_less_equal_fact(z.clone(), add.right.as_ref().clone(), lf.clone())
                .into();
            let g_a_right = self
                .new_less_fact(f.left.clone(), add.right.as_ref().clone(), lf.clone())
                .into();
            let g0_left = self
                .new_less_equal_fact(z.clone(), add.left.as_ref().clone(), lf.clone())
                .into();
            let premise_result = self.try_verify_builtin_rule_premise_alternatives(
                vec![vec![g_a_left, g0_right], vec![g_a_right, g0_left]],
                lf.clone(),
                builtin_state,
            )?;
            if let Some(premise_result) = premise_result {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b + c from either compatible strict addend-bound conjunction"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra10),
                        vec![premise_result],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.right {
            // Move a right subtractor to the left side as an addend.
            // Example: from `a + c < b`, prove `a < b - c`.
            let shifted_left: Obj = Add::new(f.left.clone(), sub.right.as_ref().clone()).into();
            let shifted_subgoal: AtomicFact = self
                .new_less_fact(shifted_left, sub.left.as_ref().clone(), lf.clone())
                .into();
            if let Some(shifted_result) =
                self.try_verify_order_subgoal(shifted_subgoal, builtin_state)?
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b - c from a + c < b".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra11),
                        vec![shifted_result],
                    ),
                )));
            }
        }

        if let Obj::Sub(sub) = &f.left {
            if sub.left.as_ref().to_string() == f.right.to_string()
                && Self::obj_is_positive_integer_number(sub.right.as_ref())
            {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a - n < a for n > 0".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra12),
                        Vec::new(),
                    ),
                )));
            }
        }

        // Dividing a positive quantity by a factor greater than one makes it smaller.
        // Example: from `a > 0` and `b > 1`, prove `a / b < a`.
        if let Obj::Div(div) = &f.left {
            if div.left.as_ref().to_string() == f.right.to_string() {
                let g_pos = self
                    .new_less_fact(z.clone(), f.right.clone(), lf.clone())
                    .into();
                let g_denom_gt_one = self
                    .new_less_fact(one.clone(), div.right.as_ref().clone(), lf.clone())
                    .into();
                let Some(r_pos) = self.try_verify_order_subgoal(g_pos, builtin_state)? else {
                    return Ok(None);
                };
                let Some(r_denom_gt_one) =
                    self.try_verify_order_subgoal(g_denom_gt_one, builtin_state)?
                else {
                    return Ok(None);
                };
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a / b < a from 0 < a and 1 < b".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::DivByGreaterThanOneLessSelf,
                        ),
                        vec![r_pos, r_denom_gt_one],
                    ),
                )));
            }
        }

        if f.right.to_string() == z.to_string() {
            // A sum is strictly negative when one term is negative and the other is nonpositive.
            // Example: `a < 0, b <= 0 => a + b < 0`.
            if let Obj::Add(add) = &f.left {
                let cases: [(AtomicFact, AtomicFact); 2] = [
                    (
                        self.new_less_fact(add.left.as_ref().clone(), z.clone(), lf.clone())
                            .into(),
                        self.new_less_equal_fact(add.right.as_ref().clone(), z.clone(), lf.clone())
                            .into(),
                    ),
                    (
                        self.new_less_equal_fact(add.left.as_ref().clone(), z.clone(), lf.clone())
                            .into(),
                        self.new_less_fact(add.right.as_ref().clone(), z.clone(), lf.clone())
                            .into(),
                    ),
                ];
                for (negative, nonpositive) in cases {
                    let negative_result = self.try_verify_order_subgoal(negative, builtin_state)?;
                    let nonpositive_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &nonpositive,
                        builtin_state,
                    )?;
                    if let (Some(negative_result), Some(nonpositive_result)) =
                        (negative_result, nonpositive_result)
                    {
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                "a + b < 0 from one negative term and one nonpositive term"
                                    .to_string(),
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra14),
                                vec![negative_result, nonpositive_result],
                            ),
                        )));
                    }
                }
            }
            if let Obj::Pow(pow) = &f.left {
                if let Some(r) = self.try_pow_lt_zero_odd_exponent_from_negative_base(
                    pow,
                    lf,
                    atomic_fact,
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
            if let Obj::Mul(m) = &f.left {
                if let Some(r) = self.try_mul_lt_zero_by_signs(
                    m.left.as_ref(),
                    m.right.as_ref(),
                    lf,
                    atomic_fact,
                    builtin_state,
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
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = self
                    .new_less_fact(z.clone(), f.left.clone(), lf.clone())
                    .into();
                let g1 = self
                    .new_less_fact(one, m.left.as_ref().clone(), lf.clone())
                    .into();
                let Some(r0) = self.try_verify_order_subgoal(g0, builtin_state)? else {
                    return Ok(None);
                };
                let Some(r1) = self.try_verify_order_subgoal(g1, builtin_state)? else {
                    return Ok(None);
                };
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b * a from 0 < a and 1 < b".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryLessAlgebra15),
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
                    builtin_state,
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
                    builtin_state,
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1s = self
                .new_less_fact(
                    al.left.as_ref().clone(),
                    bl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2s = self
                .new_less_fact(
                    al.right.as_ref().clone(),
                    bl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let r1 = self.try_verify_order_subgoal(g1s, builtin_state)?;
            let r2 = self.try_verify_order_subgoal(g2s, builtin_state)?;
            if let (Some(r1), Some(r2)) = (r1, r2) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c < d".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::AddComponentwiseLess,
                        ),
                        vec![r1, r2],
                    ),
                )));
            }
            let g1m = self
                .new_less_fact(
                    al.left.as_ref().clone(),
                    bl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2m = self
                .new_less_equal_fact(
                    al.right.as_ref().clone(),
                    bl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let r3 = self.try_verify_order_subgoal(g1m, builtin_state)?;
            let r4 = self.try_verify_atomic_fact_as_builtin_rule_premise(&g2m, builtin_state)?;
            if let (Some(r3), Some(r4)) = (r3, r4) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c <= d".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::AddComponentwiseLessLessEqual,
                        ),
                        vec![r3, r4],
                    ),
                )));
            }
            let g1w = self
                .new_less_equal_fact(
                    al.left.as_ref().clone(),
                    bl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let g2w = self
                .new_less_fact(
                    al.right.as_ref().clone(),
                    bl.right.as_ref().clone(),
                    lf.clone(),
                )
                .into();
            let r5 = self.try_verify_atomic_fact_as_builtin_rule_premise(&g1w, builtin_state)?;
            let r6 = self.try_verify_order_subgoal(g2w, builtin_state)?;
            if let (Some(r5), Some(r6)) = (r5, r6) {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a <= b and c < d".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::AddComponentwiseLessEqualLess,
                        ),
                        vec![r5, r6],
                    ),
                )));
            }
        }

        Ok(None)
    }
}
