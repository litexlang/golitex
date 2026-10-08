//! Fixed consumers of stored scalar orders; no multi-hop graph discovery.
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{AtomicFact, LessEqualFact, LessFact};
use crate::ast::obj::{Abs, ArithmeticOperator as A, Literal, Number, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::{
    exact_rational::EvalRational, objs_equal_by_rational_expression_evaluation, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};

pub struct SumStrictOperandsProof {
    pub first_order: AtomicExceptEqualityFactKnownProof,
    pub second_order: AtomicExceptEqualityFactKnownProof,
}
impl SumStrictOperandsProof {
    pub fn new(
        first_order: AtomicExceptEqualityFactKnownProof,
        second_order: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            first_order,
            second_order,
        }
    }
}
pub struct LiteralWeakBoundProof {
    pub source_order: AtomicExceptEqualityFactKnownProof,
}
impl LiteralWeakBoundProof {
    pub fn new(source_order: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { source_order }
    }
}
pub struct IntegerSuccessorGapProof {
    pub left_integer: VerifyFactResult,
    pub right_integer: VerifyFactResult,
    pub strict_order: AtomicExceptEqualityFactKnownProof,
}
impl IntegerSuccessorGapProof {
    pub fn new(
        left_integer: VerifyFactResult,
        right_integer: VerifyFactResult,
        strict_order: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            left_integer,
            right_integer,
            strict_order,
        }
    }
}
pub struct NegationStrictOrderProof {
    pub argument_order: AtomicExceptEqualityFactKnownProof,
}
impl NegationStrictOrderProof {
    pub fn new(argument_order: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { argument_order }
    }
}
pub struct NegationWeakOrderProof {
    pub argument_order: AtomicExceptEqualityFactKnownProof,
}
impl NegationWeakOrderProof {
    pub fn new(argument_order: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { argument_order }
    }
}
pub struct NegationNegativeFromLiteralBoundProof {
    pub positive_source: AtomicExceptEqualityFactKnownProof,
}
impl NegationNegativeFromLiteralBoundProof {
    pub fn new(positive_source: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { positive_source }
    }
}
pub struct AbsFromIntervalBoundsProof {
    pub lower_bound: AtomicExceptEqualityFactKnownProof,
    pub upper_bound: AtomicExceptEqualityFactKnownProof,
}
impl AbsFromIntervalBoundsProof {
    pub fn new(
        lower_bound: AtomicExceptEqualityFactKnownProof,
        upper_bound: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

impl Runtime {
    pub(super) fn search_scalar_less_relation(
        &mut self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        use LessFactSearchProofByBuiltinRule as P;
        // Adding two strict scalar orders; each written direction is cited.
        if let (Obj::ArithmeticOperator(A::Add(a)), Obj::ArithmeticOperator(A::Add(b))) =
            (&fact.left, &fact.right)
        {
            for (r1, r2) in [(&*b.left, &*b.right), (&*b.right, &*b.left)] {
                if let Some(first_order) = self.known_integer_interval_order(&a.left, r1, true) {
                    if let Some(second_order) =
                        self.known_integer_interval_order(&a.right, r2, true)
                    {
                        return Ok(Some(P::SumStrictOperands(SumStrictOperandsProof::new(
                            first_order,
                            second_order,
                        ))));
                    }
                }
            }
        }
        // a<b => -b<-a; all spellings denote the same scalar negation.
        if let (Some(left), Some(right)) = (
            negative_argument(&fact.left),
            negative_argument(&fact.right),
        ) {
            if let Some(argument_order) = self.known_integer_interval_order(right, left, true) {
                return Ok(Some(P::NegationStrictOrder(NegationStrictOrderProof::new(
                    argument_order,
                ))));
            }
        }
        // x>=k>0 or x>k>=0 => -x<0. Keep the actual literal-bound citation.
        if EvalRational::from_obj(&fact.right).is_some_and(|n| n.is_zero()) {
            if let Some(argument) = negative_argument(&fact.left) {
                let sources = scalar_order_sources(self);
                for (source, lower, upper, strict) in sources {
                    if !same(&upper, argument) {
                        continue;
                    }
                    let Some(bound) = EvalRational::from_obj(&lower) else {
                        continue;
                    };
                    let Some(order) = bound.compare(&EvalRational::new(0, 1).unwrap()) else {
                        continue;
                    };
                    if order == NumberCompareResult::Greater
                        || (strict && order == NumberCompareResult::Equal)
                    {
                        if let Some(positive_source) = self.lookup_known_atomic_premise(source) {
                            return Ok(Some(P::NegationNegativeFromLiteralBound(
                                NegationNegativeFromLiteralBoundProof::new(positive_source),
                            )));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    pub(super) fn search_scalar_less_equal_relation(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        use LessEqualFactSearchProofByBuiltinRule as P;
        if let (Some(left), Some(right)) = (
            negative_argument(&fact.left),
            negative_argument(&fact.right),
        ) {
            if let Some(argument_order) = self.known_integer_interval_order(right, left, false) {
                return Ok(Some(P::NegationWeakOrder(NegationWeakOrderProof::new(
                    argument_order,
                ))));
            }
        }
        // -b<=x<=b => abs(x)<=b. Record this separate interval guard shape.
        if let Obj::ArithmeticOperator(A::Abs(Abs { arg })) = &fact.left {
            let negative = Obj::ArithmeticOperator(A::Neg(crate::ast::obj::Neg {
                arg: Box::new(fact.right.clone()),
            }));
            if let Some(lower_bound) = self.known_integer_interval_order(&negative, arg, false) {
                if let Some(upper_bound) =
                    self.known_integer_interval_order(arg, &fact.right, false)
                {
                    return Ok(Some(P::AbsFromIntervalBounds(
                        AbsFromIntervalBoundsProof::new(lower_bound, upper_bound),
                    )));
                }
            }
        }
        // Real literal-bound weakening: x<k<=c => x<=c; c<=k<x => c<=x.
        // The literal comparison is exact; named or symbolic bounds are not resolved.
        for (source, lower, upper, _) in scalar_order_sources(self) {
            let lower_bound = EvalRational::from_obj(&lower);
            let upper_bound = EvalRational::from_obj(&upper);
            let target_left = EvalRational::from_obj(&fact.left);
            let target_right = EvalRational::from_obj(&fact.right);
            let weaker = if same(&upper, &fact.right) {
                matches!((target_left,lower_bound), (Some(a),Some(b)) if matches!(a.compare(&b),Some(NumberCompareResult::Less|NumberCompareResult::Equal)))
            } else if same(&lower, &fact.left) {
                matches!((upper_bound,target_right), (Some(a),Some(b)) if matches!(a.compare(&b),Some(NumberCompareResult::Less|NumberCompareResult::Equal)))
            } else {
                false
            };
            if weaker {
                if let Some(source_order) = self.lookup_known_atomic_premise(source) {
                    return Ok(Some(P::LiteralWeakBound(LiteralWeakBoundProof::new(
                        source_order,
                    ))));
                }
            }
        }
        // Integers have no gap between adjacent values: a<b => a+1<=b.
        // Pure arithmetic endpoint matching covers 5<=x from 4<x and x<=3
        // from x<4, but real x does not receive this discrete strengthening.
        let previous = Obj::ArithmeticOperator(A::Sub(crate::ast::obj::Sub {
            left: Box::new(fact.left.clone()),
            right: Box::new(number("1")),
        }));
        if let Some(strict_order) = self.known_integer_interval_order(&previous, &fact.right, true)
        {
            let (a, b) = strict_endpoints(&strict_order.fact).unwrap();
            let left_integer = self.verify_in_integer(a, state)?;
            let right_integer = self.verify_in_integer(b, state)?;
            if !left_integer.is_failed() && !right_integer.is_failed() {
                return Ok(Some(P::IntegerSuccessorGap(IntegerSuccessorGapProof::new(
                    left_integer,
                    right_integer,
                    strict_order,
                ))));
            }
        }
        let next = Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add {
            left: Box::new(fact.right.clone()),
            right: Box::new(number("1")),
        }));
        if let Some(strict_order) = self.known_integer_interval_order(&fact.left, &next, true) {
            let (a, b) = strict_endpoints(&strict_order.fact).unwrap();
            let left_integer = self.verify_in_integer(a, state)?;
            let right_integer = self.verify_in_integer(b, state)?;
            if !left_integer.is_failed() && !right_integer.is_failed() {
                return Ok(Some(P::IntegerSuccessorGap(IntegerSuccessorGapProof::new(
                    left_integer,
                    right_integer,
                    strict_order,
                ))));
            }
        }
        Ok(None)
    }
}
fn scalar_order_sources(runtime: &Runtime) -> Vec<(AtomicFact, Obj, Obj, bool)> {
    let mut sources = Vec::new();
    for env in runtime.execution_environments_stack.iter().rev() {
        for knowns in env
            .facts
            .known_atomic_except_equality_facts
            .by_prop
            .values()
        {
            for known in knowns {
                let pair = match known {
                    AtomicFact::LessFact(f) => Some((&f.left, &f.right, true)),
                    AtomicFact::GreaterFact(f) => Some((&f.right, &f.left, true)),
                    AtomicFact::LessEqualFact(f) => Some((&f.left, &f.right, false)),
                    AtomicFact::GreaterEqualFact(f) => Some((&f.right, &f.left, false)),
                    _ => None,
                };
                if let Some((lower, upper, strict)) = pair {
                    sources.push((known.clone(), lower.clone(), upper.clone(), strict));
                }
            }
        }
    }
    sources
}
fn negative_argument(value: &Obj) -> Option<&Obj> {
    match value {
        Obj::ArithmeticOperator(A::Neg(n)) => Some(&n.arg),
        Obj::ArithmeticOperator(A::Sub(s))
            if EvalRational::from_obj(&s.left).is_some_and(|n| n.is_zero()) =>
        {
            Some(&s.right)
        }
        Obj::ArithmeticOperator(A::Mul(m))
            if EvalRational::from_obj(&m.left) == EvalRational::new(-1, 1) =>
        {
            Some(&m.right)
        }
        Obj::ArithmeticOperator(A::Mul(m))
            if EvalRational::from_obj(&m.right) == EvalRational::new(-1, 1) =>
        {
            Some(&m.left)
        }
        _ => None,
    }
}
fn number(v: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(v.into())))
}
fn same(a: &Obj, b: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(a, b)
}

fn strict_endpoints(f: &AtomicFact) -> Option<(&Obj, &Obj)> {
    match f {
        AtomicFact::LessFact(f) => Some((&f.left, &f.right)),
        AtomicFact::GreaterFact(f) => Some((&f.right, &f.left)),
        _ => None,
    }
}
