//! Fixed checked-argument consumers; no arbitrary equality-class discovery.
use super::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, NotEqualFact};
use crate::ast::obj::{
    ArithmeticOperator as A, ExpLogOperator as E, IntegerOperator as I, Literal, Number, Obj, Pow,
    Sin, StandardSet, TrigOperator as T,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::{
    exact_rational::EvalRational, objs_equal_by_rational_expression_evaluation as same,
};
use crate::runtime::{Runtime, RuntimeResult};
pub enum ScalarExtraEqualityProof {
    SqrtProductFromKnownArgument(SqrtProductFromKnownArgumentProof),
    SqrtQuotientFromKnownArgument(SqrtQuotientFromKnownArgumentProof),
    ArcsinFromKnownSine(ArcsinFromKnownSineProof),
    RealLogFromKnownPower(RealLogFromKnownPowerProof),
    PositivePowerLogInverse(PositivePowerLogInverseProof),
    PositivePowerReciprocalRoot(PositivePowerReciprocalRootProof),
    PositiveIntegerPowerInjective(PositiveIntegerPowerInjectiveProof),
    NestedRemainderUnit(NestedRemainderUnitProof),
}
impl ScalarExtraEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SqrtProductFromKnownArgument(_) => "SqrtProductFromKnownArgument",
            Self::SqrtQuotientFromKnownArgument(_) => "SqrtQuotientFromKnownArgument",
            Self::ArcsinFromKnownSine(_) => "ArcsinFromKnownSine",
            Self::RealLogFromKnownPower(_) => "RealLogFromKnownPower",
            Self::PositivePowerLogInverse(_) => "PositivePowerLogInverse",
            Self::PositivePowerReciprocalRoot(_) => "PositivePowerReciprocalRoot",
            Self::PositiveIntegerPowerInjective(_) => "PositiveIntegerPowerInjective",
            Self::NestedRemainderUnit(_) => "NestedRemainderUnit",
        }
    }
}
pub struct SqrtProductFromKnownArgumentProof {
    pub argument_equality: Box<EqualFactSearchedProof>,
}
pub struct SqrtQuotientFromKnownArgumentProof {
    pub argument_equality: Box<EqualFactSearchedProof>,
}
pub struct ArcsinFromKnownSineProof {
    pub principal_bounds: Vec<VerifyFactResult>,
    pub sine_equality: Box<EqualFactSearchedProof>,
}
pub struct RealLogFromKnownPowerProof {
    pub base_guard: LogAlgebraBaseProof,
    pub exponent_real: VerifyFactResult,
    pub power_equality: Box<EqualFactSearchedProof>,
}
pub struct PositivePowerLogInverseProof {
    pub base_guard: LogAlgebraBaseProof,
}
pub struct PositivePowerReciprocalRootProof {
    pub base_positive: VerifyFactResult,
    pub exponent_positive_natural: VerifyFactResult,
}
pub struct PositiveIntegerPowerInjectiveProof {
    pub left_positive: VerifyFactResult,
    pub right_positive: VerifyFactResult,
    pub exponent_integer: VerifyFactResult,
    pub exponent_nonzero: VerifyFactResult,
    pub power_equality: Box<EqualFactSearchedProof>,
}
pub struct NestedRemainderUnitProof;
impl Runtime {
    pub(super) fn scalar_extra_equality(
        &mut self,
        f: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ScalarExtraEqualityProof>> {
        use ScalarExtraEqualityProof as P;
        for (left, right) in [(&f.left, &f.right), (&f.right, &f.left)] {
            if let Obj::ExpLogOperator(E::Sqrt(root)) = left {
                if let Obj::ArithmeticOperator(A::Mul(m)) = right {
                    if let (Obj::ExpLogOperator(E::Sqrt(a)), Obj::ExpLogOperator(E::Sqrt(b))) =
                        (&*m.left, &*m.right)
                    {
                        let product = Obj::ArithmeticOperator(A::Mul(crate::ast::obj::Mul {
                            left: a.arg.clone(),
                            right: b.arg.clone(),
                        }));
                        if let Some(e) =
                            self.lookup_exact_property_obj_equality(&root.arg, &product)
                        {
                            return Ok(Some(P::SqrtProductFromKnownArgument(
                                SqrtProductFromKnownArgumentProof::new(Box::new(e)),
                            )));
                        }
                    }
                }
                if let Obj::ArithmeticOperator(A::Div(m)) = right {
                    if let (Obj::ExpLogOperator(E::Sqrt(a)), Obj::ExpLogOperator(E::Sqrt(b))) =
                        (&*m.left, &*m.right)
                    {
                        let quotient = Obj::ArithmeticOperator(A::Div(crate::ast::obj::Div {
                            left: a.arg.clone(),
                            right: b.arg.clone(),
                        }));
                        if let Some(e) =
                            self.lookup_exact_property_obj_equality(&root.arg, &quotient)
                        {
                            return Ok(Some(P::SqrtQuotientFromKnownArgument(
                                SqrtQuotientFromKnownArgumentProof::new(Box::new(e)),
                            )));
                        }
                    }
                }
            }
            if let Obj::TrigOperator(T::Arcsin(a)) = left {
                let sine = Obj::TrigOperator(T::Sin(Sin {
                    arg: Box::new(right.clone()),
                }));
                if let Some(sine_equality) = self.lookup_exact_property_obj_equality(&a.arg, &sine)
                {
                    if let Some(principal_bounds) = self.verify_closed_interval_premises(
                        right,
                        &super::by_inverse_trig::negative_half_pi(),
                        &super::by_inverse_trig::half_pi(),
                        f,
                        state,
                    )? {
                        return Ok(Some(P::ArcsinFromKnownSine(ArcsinFromKnownSineProof::new(
                            principal_bounds,
                            Box::new(sine_equality),
                        ))));
                    }
                }
            }
            if let Obj::ExpLogOperator(E::Log(log)) = left {
                let power = Obj::ArithmeticOperator(A::Pow(Pow {
                    base: log.base.clone(),
                    exponent: Box::new(right.clone()),
                }));
                if let Some(power_equality) =
                    self.lookup_exact_property_obj_equality(&power, &log.arg)
                {
                    if let Some(base_guard) =
                        self.verify_log_algebra_base_guard(&log.base, state)?
                    {
                        let exponent_real =
                            self.scalar_extra_member(right, StandardSet::R, state)?;
                        if !exponent_real.is_failed() {
                            return Ok(Some(P::RealLogFromKnownPower(
                                RealLogFromKnownPowerProof::new(
                                    base_guard,
                                    exponent_real,
                                    Box::new(power_equality),
                                ),
                            )));
                        }
                    }
                }
            }
            if let Obj::ArithmeticOperator(A::Pow(power)) = left {
                if let Obj::ExpLogOperator(E::Log(log)) = &*power.exponent {
                    if same(&power.base, &log.base) && same(&log.arg, right) {
                        if let Some(base_guard) =
                            self.verify_log_algebra_base_guard(&power.base, state)?
                        {
                            return Ok(Some(P::PositivePowerLogInverse(
                                PositivePowerLogInverseProof::new(base_guard),
                            )));
                        }
                    }
                }
                if let (
                    Obj::ArithmeticOperator(A::Pow(inner)),
                    Obj::ArithmeticOperator(A::Div(reciprocal)),
                ) = (&*power.base, &*power.exponent)
                {
                    if same(&inner.base, right)
                        && EvalRational::from_obj(&reciprocal.left) == EvalRational::new(1, 1)
                        && same(&inner.exponent, &reciprocal.right)
                    {
                        let base_positive =
                            self.scalar_extra_member(right, StandardSet::RPos, state)?;
                        let exponent_positive_natural =
                            self.verify_in_positive_natural(&inner.exponent, state)?;
                        if !base_positive.is_failed() && !exponent_positive_natural.is_failed() {
                            return Ok(Some(P::PositivePowerReciprocalRoot(
                                PositivePowerReciprocalRootProof::new(
                                    base_positive,
                                    exponent_positive_natural,
                                ),
                            )));
                        }
                    }
                }
            }
            if let (Obj::IntegerOperator(I::Mod(a)), Obj::IntegerOperator(I::Mod(b))) =
                (left, right)
            {
                if EvalRational::from_obj(&a.right) == EvalRational::new(1, 1)
                    && EvalRational::from_obj(&b.right) == EvalRational::new(1, 1)
                {
                    if let Obj::IntegerOperator(I::Mod(inner)) = &*a.left {
                        if same(&inner.left, &b.left) {
                            return Ok(Some(P::NestedRemainderUnit(NestedRemainderUnitProof)));
                        }
                    }
                }
            }
        }
        // Direct same-exponent equality, with a nonzero integer exponent and positive bases.
        let mut exponents = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for fact in env.facts.facts_by_id.values() {
                if let Fact::AtomicFact(AtomicFact::EqualFact(e)) = fact {
                    for (a, b) in [(&e.left, &e.right), (&e.right, &e.left)] {
                        if let (
                            Obj::ArithmeticOperator(A::Pow(a)),
                            Obj::ArithmeticOperator(A::Pow(b)),
                        ) = (a, b)
                        {
                            if same(&a.base, &f.left)
                                && same(&b.base, &f.right)
                                && same(&a.exponent, &b.exponent)
                            {
                                exponents.push(*a.exponent.clone());
                            }
                        }
                    }
                }
            }
        }
        for n in exponents {
            let a = Obj::ArithmeticOperator(A::Pow(Pow {
                base: Box::new(f.left.clone()),
                exponent: Box::new(n.clone()),
            }));
            let b = Obj::ArithmeticOperator(A::Pow(Pow {
                base: Box::new(f.right.clone()),
                exponent: Box::new(n.clone()),
            }));
            let Some(power_equality) = self.lookup_exact_property_obj_equality(&a, &b) else {
                continue;
            };
            let left_positive = self.scalar_extra_member(&f.left, StandardSet::RPos, state)?;
            let right_positive = self.scalar_extra_member(&f.right, StandardSet::RPos, state)?;
            let exponent_integer = self.verify_in_integer(&n, state)?;
            let requirement: Fact = NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: n.clone(),
                right: Obj::Literal(Literal::Number(Number::new("0".into()))),
                line_file: None,
            }
            .into();
            let exponent_nonzero = self.verify_builtin_rule_premise(&requirement, state)?;
            if !left_positive.is_failed()
                && !right_positive.is_failed()
                && !exponent_integer.is_failed()
                && !exponent_nonzero.is_failed()
            {
                return Ok(Some(P::PositiveIntegerPowerInjective(
                    PositiveIntegerPowerInjectiveProof::new(
                        left_positive,
                        right_positive,
                        exponent_integer,
                        exponent_nonzero,
                        Box::new(power_equality),
                    ),
                )));
            }
        }
        Ok(None)
    }
    fn scalar_extra_member(
        &mut self,
        o: &Obj,
        set: StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: o.clone(),
            set: Obj::StandardSet(set),
            line_file: None,
        }
        .into();
        self.verify_builtin_rule_premise(&fact, state)
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/legacy_remaining_local_migration/tests.rs"]
mod legacy_remaining_local_migration_tests;

impl SqrtProductFromKnownArgumentProof {
    pub fn new(argument_equality: Box<EqualFactSearchedProof>) -> Self {
        Self { argument_equality }
    }
}

impl SqrtQuotientFromKnownArgumentProof {
    pub fn new(argument_equality: Box<EqualFactSearchedProof>) -> Self {
        Self { argument_equality }
    }
}

impl ArcsinFromKnownSineProof {
    pub fn new(
        principal_bounds: Vec<VerifyFactResult>,
        sine_equality: Box<EqualFactSearchedProof>,
    ) -> Self {
        Self {
            principal_bounds,
            sine_equality,
        }
    }
}

impl RealLogFromKnownPowerProof {
    pub fn new(
        base_guard: LogAlgebraBaseProof,
        exponent_real: VerifyFactResult,
        power_equality: Box<EqualFactSearchedProof>,
    ) -> Self {
        Self {
            base_guard,
            exponent_real,
            power_equality,
        }
    }
}

impl PositivePowerLogInverseProof {
    pub fn new(base_guard: LogAlgebraBaseProof) -> Self {
        Self { base_guard }
    }
}

impl PositivePowerReciprocalRootProof {
    pub fn new(
        base_positive: VerifyFactResult,
        exponent_positive_natural: VerifyFactResult,
    ) -> Self {
        Self {
            base_positive,
            exponent_positive_natural,
        }
    }
}

impl PositiveIntegerPowerInjectiveProof {
    pub fn new(
        left_positive: VerifyFactResult,
        right_positive: VerifyFactResult,
        exponent_integer: VerifyFactResult,
        exponent_nonzero: VerifyFactResult,
        power_equality: Box<EqualFactSearchedProof>,
    ) -> Self {
        Self {
            left_positive,
            right_positive,
            exponent_integer,
            exponent_nonzero,
            power_equality,
        }
    }
}
