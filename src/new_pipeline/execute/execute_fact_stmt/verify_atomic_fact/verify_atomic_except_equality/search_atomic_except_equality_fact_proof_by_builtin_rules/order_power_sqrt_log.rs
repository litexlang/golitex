//! Power / square-root / logarithm order builtins for `<=` and `<`.
//!
//! One matcher ↔ one dedicated proof struct (see less_equal.rs / less.rs).

use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, LessEqualFact, LessFact, NotEqualFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    ArithmeticOperator, ExpLogOperator, Literal, Log, Mul, Number, Obj, Pow, Sqrt, StandardSet,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    EvenPowPositiveFromNonzeroBuiltinRuleProof, LessFactSearchProofByBuiltinRule,
    LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof,
    LogOrderPreservingStrictBuiltinRuleProof, LogPositiveFromBaseAndArgGtOneBuiltinRuleProof,
    PowPositiveFromPositiveBaseBuiltinRuleProof, SqrtMonotoneIncreasingBuiltinRuleProof,
    SqrtPositiveBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    is_zero_obj, zero_obj, EvenPowNonnegativeBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof, LessEqualFactSearchProofByBuiltinRule,
    LogOrderPreservingWeakBuiltinRuleProof, PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof,
    PowNonnegFromPositiveBaseBuiltinRuleProof, SqrtMonotoneNondecreasingBuiltinRuleProof,
    SqrtNonnegativeBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::IN;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Shape / premise search for power, sqrt, and log weak-order builtins.
    // Example goals: `0 <= x^2`, `0 <= sqrt(x)`, `1 <= n`, `log(2,x) <= log(2,y)`.
    pub(super) fn search_order_power_sqrt_log_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if is_one_obj(&fact.left) {
            if let Some(cite_fact_id) = self.known_in_positive_natural_fact_id(&fact.right) {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(
                        FromKnownInPositiveNaturalBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }

        if let (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: left_arg })),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: right_arg })),
        ) = (&fact.left, &fact.right)
        {
            return self.sqrt_monotone_nondecreasing_proof(
                left_arg.as_ref(),
                right_arg.as_ref(),
                verify_state,
            );
        }

        if let (
            Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                base: left_base,
                arg: left_arg,
            })),
            Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                base: right_base,
                arg: right_arg,
            })),
        ) = (&fact.left, &fact.right)
        {
            if left_base.as_ref().ir() == right_base.as_ref().ir() {
                return self.log_order_preserving_weak_proof(
                    left_base.as_ref(),
                    left_arg.as_ref(),
                    right_arg.as_ref(),
                    verify_state,
                );
            }
        }

        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }

        match &fact.right {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right }))
                if left.as_ref().ir() == right.as_ref().ir() =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(
                        EvenPowNonnegativeBuiltinRuleProof {},
                    ),
                ))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base: _, exponent }))
                if is_even_integer_literal(exponent.as_ref()) =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(
                        EvenPowNonnegativeBuiltinRuleProof {},
                    ),
                ))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) => {
                if let Some(proof) = self
                    .pow_nonneg_from_positive_base_proof(base.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
                self.pow_nonneg_from_nonneg_base_pos_int_exp_proof(
                    base.as_ref(),
                    exponent.as_ref(),
                    verify_state,
                )
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })) => {
                self.sqrt_nonnegative_proof(arg.as_ref(), verify_state)
            }
            _ => Ok(None),
        }
    }

    // Shape / premise search for power, sqrt, and log strict-order builtins.
    // Example goals: `0 < x^2`, `0 < sqrt(x)`, `0 < log(2,x)`, `log(2,x) < log(2,y)`.
    pub(super) fn search_order_power_sqrt_log_less_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if let (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: left_arg })),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: right_arg })),
        ) = (&fact.left, &fact.right)
        {
            return self.sqrt_monotone_increasing_proof(
                left_arg.as_ref(),
                right_arg.as_ref(),
                verify_state,
            );
        }

        if let (
            Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                base: left_base,
                arg: left_arg,
            })),
            Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                base: right_base,
                arg: right_arg,
            })),
        ) = (&fact.left, &fact.right)
        {
            if left_base.as_ref().ir() == right_base.as_ref().ir() {
                return self.log_order_preserving_strict_proof(
                    left_base.as_ref(),
                    left_arg.as_ref(),
                    right_arg.as_ref(),
                    verify_state,
                );
            }
        }

        if is_zero_obj(&fact.right) {
            if let Obj::ExpLogOperator(ExpLogOperator::Log(Log { base, arg })) = &fact.left {
                return self.log_negative_from_base_gt_one_arg_in_unit_interval_proof(
                    base.as_ref(),
                    arg.as_ref(),
                    verify_state,
                );
            }
        }

        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }

        match &fact.right {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right }))
                if left.as_ref().ir() == right.as_ref().ir() =>
            {
                self.even_pow_positive_from_nonzero_proof(left.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent }))
                if is_even_integer_literal(exponent.as_ref()) =>
            {
                self.even_pow_positive_from_nonzero_proof(base.as_ref(), verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent: _ })) => {
                self.pow_positive_from_positive_base_proof(base.as_ref(), verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })) => {
                self.sqrt_positive_proof(arg.as_ref(), verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(Log { base, arg })) => {
                self.log_positive_from_base_and_arg_gt_one_proof(
                    base.as_ref(),
                    arg.as_ref(),
                    verify_state,
                )
            }
            _ => Ok(None),
        }
    }

    fn pow_nonneg_from_positive_base_proof(
        &mut self,
        base: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let base_positive_proof = self.verify_order_positive(base, verify_state)?;
        if base_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::PowNonnegFromPositiveBase(
                PowNonnegFromPositiveBaseBuiltinRuleProof {
                    base_positive_proof,
                },
            ),
        ))
    }

    fn pow_nonneg_from_nonneg_base_pos_int_exp_proof(
        &mut self,
        base: &Obj,
        exponent: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let base_nonnegative_proof = self.verify_order_nonnegative(base, verify_state.clone())?;
        if base_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let exp_in_positive_natural_proof =
            self.verify_in_positive_natural(exponent, verify_state)?;
        if exp_in_positive_natural_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::PowNonnegFromNonnegBasePosIntExp(
                PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof {
                    base_nonnegative_proof,
                    exp_in_positive_natural_proof,
                },
            ),
        ))
    }

    fn sqrt_nonnegative_proof(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let arg_nonnegative_proof = self.verify_order_nonnegative(arg, verify_state)?;
        if arg_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::SqrtNonnegative(
                SqrtNonnegativeBuiltinRuleProof {
                    arg_nonnegative_proof,
                },
            ),
        ))
    }

    fn sqrt_monotone_nondecreasing_proof(
        &mut self,
        left_arg: &Obj,
        right_arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let left_nonnegative_proof =
            self.verify_order_nonnegative(left_arg, verify_state.clone())?;
        if left_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let right_nonnegative_proof =
            self.verify_order_nonnegative(right_arg, verify_state.clone())?;
        if right_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let args_order = make_less_equal_fact(left_arg, right_arg, self);
        let args_order_proof = self.verify_fact(&args_order, verify_state)?;
        if args_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::SqrtMonotoneNondecreasing(
                SqrtMonotoneNondecreasingBuiltinRuleProof {
                    left_nonnegative_proof,
                    right_nonnegative_proof,
                    args_order_proof,
                },
            ),
        ))
    }

    fn log_order_preserving_weak_proof(
        &mut self,
        base: &Obj,
        left_arg: &Obj,
        right_arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let base_gt_one_proof = self.verify_order_gt_one(base, verify_state.clone())?;
        if base_gt_one_proof.is_failed() {
            return Ok(None);
        }
        let left_arg_positive_proof =
            self.verify_order_positive(left_arg, verify_state.clone())?;
        if left_arg_positive_proof.is_failed() {
            return Ok(None);
        }
        let right_arg_positive_proof =
            self.verify_order_positive(right_arg, verify_state.clone())?;
        if right_arg_positive_proof.is_failed() {
            return Ok(None);
        }
        let args_order = make_less_equal_fact(left_arg, right_arg, self);
        let args_order_proof = self.verify_fact(&args_order, verify_state)?;
        if args_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::LogOrderPreservingWeak(
                LogOrderPreservingWeakBuiltinRuleProof {
                    base_gt_one_proof,
                    left_arg_positive_proof,
                    right_arg_positive_proof,
                    args_order_proof,
                },
            ),
        ))
    }

    fn even_pow_positive_from_nonzero_proof(
        &mut self,
        base: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let base_nonzero_proof = self.verify_order_nonzero(base, verify_state)?;
        if base_nonzero_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::EvenPowPositiveFromNonzero(
                EvenPowPositiveFromNonzeroBuiltinRuleProof {
                    base_nonzero_proof,
                },
            ),
        ))
    }

    fn pow_positive_from_positive_base_proof(
        &mut self,
        base: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let base_positive_proof = self.verify_order_positive(base, verify_state)?;
        if base_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::PowPositiveFromPositiveBase(
                PowPositiveFromPositiveBaseBuiltinRuleProof {
                    base_positive_proof,
                },
            ),
        ))
    }

    fn sqrt_positive_proof(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let arg_positive_proof = self.verify_order_positive(arg, verify_state)?;
        if arg_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessFactSearchProofByBuiltinRule::SqrtPositive(
            SqrtPositiveBuiltinRuleProof {
                arg_positive_proof,
            },
        )))
    }

    fn sqrt_monotone_increasing_proof(
        &mut self,
        left_arg: &Obj,
        right_arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_nonnegative_proof =
            self.verify_order_nonnegative(left_arg, verify_state.clone())?;
        if left_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let right_nonnegative_proof =
            self.verify_order_nonnegative(right_arg, verify_state.clone())?;
        if right_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let args_order = make_less_fact(left_arg, right_arg, self);
        let args_order_proof = self.verify_fact(&args_order, verify_state)?;
        if args_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::SqrtMonotoneIncreasing(
                SqrtMonotoneIncreasingBuiltinRuleProof {
                    left_nonnegative_proof,
                    right_nonnegative_proof,
                    args_order_proof,
                },
            ),
        ))
    }

    fn log_order_preserving_strict_proof(
        &mut self,
        base: &Obj,
        left_arg: &Obj,
        right_arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let base_gt_one_proof = self.verify_order_gt_one(base, verify_state.clone())?;
        if base_gt_one_proof.is_failed() {
            return Ok(None);
        }
        let left_arg_positive_proof =
            self.verify_order_positive(left_arg, verify_state.clone())?;
        if left_arg_positive_proof.is_failed() {
            return Ok(None);
        }
        let right_arg_positive_proof =
            self.verify_order_positive(right_arg, verify_state.clone())?;
        if right_arg_positive_proof.is_failed() {
            return Ok(None);
        }
        let args_order = make_less_fact(left_arg, right_arg, self);
        let args_order_proof = self.verify_fact(&args_order, verify_state)?;
        if args_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::LogOrderPreservingStrict(
                LogOrderPreservingStrictBuiltinRuleProof {
                    base_gt_one_proof,
                    left_arg_positive_proof,
                    right_arg_positive_proof,
                    args_order_proof,
                },
            ),
        ))
    }

    fn log_positive_from_base_and_arg_gt_one_proof(
        &mut self,
        base: &Obj,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let base_gt_one_proof = self.verify_order_gt_one(base, verify_state.clone())?;
        if base_gt_one_proof.is_failed() {
            return Ok(None);
        }
        let arg_gt_one_proof = self.verify_order_gt_one(arg, verify_state)?;
        if arg_gt_one_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::LogPositiveFromBaseAndArgGtOne(
                LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
                    base_gt_one_proof,
                    arg_gt_one_proof,
                },
            ),
        ))
    }

    fn log_negative_from_base_gt_one_arg_in_unit_interval_proof(
        &mut self,
        base: &Obj,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let base_gt_one_proof = self.verify_order_gt_one(base, verify_state.clone())?;
        if base_gt_one_proof.is_failed() {
            return Ok(None);
        }
        let arg_positive_proof = self.verify_order_positive(arg, verify_state.clone())?;
        if arg_positive_proof.is_failed() {
            return Ok(None);
        }
        let arg_lt_one = make_less_fact(arg, &one_obj(), self);
        let arg_lt_one_proof = self.verify_fact(&arg_lt_one, verify_state)?;
        if arg_lt_one_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::LogNegativeFromBaseGtOneArgInUnitInterval(
                LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
                    base_gt_one_proof,
                    arg_positive_proof,
                    arg_lt_one_proof,
                },
            ),
        ))
    }

    pub(crate) fn verify_order_nonnegative(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = make_less_equal_fact(&zero_obj(), obj, self);
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn verify_order_positive(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = make_less_fact(&zero_obj(), obj, self);
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn verify_order_gt_one(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = make_less_fact(&one_obj(), obj, self);
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn verify_order_nonzero(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: obj.clone(),
            right: zero_obj(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn verify_in_positive_natural(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::NPos),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn known_in_positive_natural_fact_id(&self, element: &Obj) -> Option<FactId> {
        let key = (AtomicName::Plain { name: IN.into() }, true);
        let element_ir = element.ir();
        let n_pos_ir = Obj::StandardSet(StandardSet::NPos).ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::InFact(f) = known {
                    if f.element.ir() == element_ir && f.set.ir() == n_pos_ir {
                        return Some(f.fact_id);
                    }
                }
            }
        }
        None
    }
}

fn make_less_equal_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn make_less_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessFact(LessFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "1"
    )
}

fn is_even_integer_literal(obj: &Obj) -> bool {
    let Obj::Literal(Literal::Number(Number { normalized_value })) = obj else {
        return false;
    };
    let s = normalized_value.as_str();
    let int_part = if let Some((whole, frac)) = s.split_once('.') {
        if !frac.chars().all(|c| c == '0') {
            return false;
        }
        whole
    } else {
        s
    };
    let digits = int_part.strip_prefix('-').unwrap_or(int_part);
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    matches!(digits.chars().last(), Some('0' | '2' | '4' | '6' | '8'))
}
