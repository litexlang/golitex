use crate::ast::fact::{Fact, InFact};
use crate::ast::obj::{
    ArithmeticOperator as A, Div, ExpLogOperator, Neg, Obj, Sqrt, StandardSet, TrigOperator,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::pi_multiple::pi_coefficient;
use crate::runtime::{Runtime, RuntimeResult};

pub struct PeriodicTrigBuiltinRuleProof {
    pub coefficient: Obj,
    pub integer_requirements: Vec<VerifyFactResult>,
    pub value: Obj,
}
impl PeriodicTrigBuiltinRuleProof {
    fn new(coefficient: Obj, integer_requirements: Vec<VerifyFactResult>, value: Obj) -> Self {
        Self {
            coefficient,
            integer_requirements,
            value,
        }
    }
}

pub struct PeriodicTrigNonzeroBuiltinRuleProof {
    pub coefficient: Obj,
    pub integer_requirements: Vec<VerifyFactResult>,
}
impl PeriodicTrigNonzeroBuiltinRuleProof {
    fn new(coefficient: Obj, integer_requirements: Vec<VerifyFactResult>) -> Self {
        Self {
            coefficient,
            integer_requirements,
        }
    }
}

enum TrigKind {
    Sin,
    Cos,
    Tan,
    Cot,
}

// A local linear view of the pi coefficient, not a new mathematical atom/store.
struct CoefficientTerms {
    constant: EvalRational,
    terms: Vec<(EvalRational, Obj)>,
}
impl CoefficientTerms {
    fn new(constant: EvalRational, terms: Vec<(EvalRational, Obj)>) -> Self {
        Self { constant, terms }
    }
}

impl Runtime {
    // Reduce exact special angles modulo the checked integral period.
    // Example: k in Z proves tan(pi+2*k*pi)=0; k in R alone cannot.
    pub(crate) fn periodic_trig_value(
        &mut self,
        obj: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<PeriodicTrigBuiltinRuleProof>> {
        let (kind, angle) = match obj {
            Obj::TrigOperator(TrigOperator::Sin(a)) => (TrigKind::Sin, &*a.arg),
            Obj::TrigOperator(TrigOperator::Cos(a)) => (TrigKind::Cos, &*a.arg),
            Obj::TrigOperator(TrigOperator::Tan(a)) => (TrigKind::Tan, &*a.arg),
            Obj::TrigOperator(TrigOperator::Cot(a)) => (TrigKind::Cot, &*a.arg),
            _ => return Ok(None),
        };
        let Some(coefficient) = pi_coefficient(angle) else {
            return Ok(None);
        };
        let Some(terms) = split_terms(&coefficient, 0) else {
            return Ok(None);
        };
        let Some((period, value)) = exact_trig_value(kind, &terms.constant) else {
            return Ok(None);
        };
        let Some(integer_requirements) = self.verify_period_terms(&terms, period, state)? else {
            return Ok(None);
        };
        Ok(Some(PeriodicTrigBuiltinRuleProof::new(
            coefficient,
            integer_requirements,
            value,
        )))
    }

    // Zeros of sine/cosine at rational multiples of pi, modulo integer pi.
    // This separate leaf supplies tan/cot WD without assuming their value rule.
    pub(crate) fn periodic_trig_nonzero(
        &mut self,
        obj: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<PeriodicTrigNonzeroBuiltinRuleProof>> {
        let (sine, angle) = match obj {
            Obj::TrigOperator(TrigOperator::Sin(a)) => (true, &*a.arg),
            Obj::TrigOperator(TrigOperator::Cos(a)) => (false, &*a.arg),
            _ => return Ok(None),
        };
        let Some(coefficient) = pi_coefficient(angle) else {
            return Ok(None);
        };
        let Some(terms) = split_terms(&coefficient, 0) else {
            return Ok(None);
        };
        let Some(reduced) = terms.constant.modulo_integer(1) else {
            return Ok(None);
        };
        if (sine && reduced.is_zero()) || (!sine && reduced.parts() == (1, 2)) {
            return Ok(None);
        }
        let Some(integer_requirements) = self.verify_period_terms(&terms, 1, state)? else {
            return Ok(None);
        };
        Ok(Some(PeriodicTrigNonzeroBuiltinRuleProof::new(
            coefficient,
            integer_requirements,
        )))
    }

    fn verify_period_terms(
        &mut self,
        terms: &CoefficientTerms,
        period: i128,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<VerifyFactResult>>> {
        let mut proofs = Vec::new();
        for (scale, term) in &terms.terms {
            if scale.is_zero() {
                continue;
            }
            let Some(integer_scale) = scale.to_i128_if_integer() else {
                return Ok(None);
            };
            if integer_scale % period != 0 {
                return Ok(None);
            }
            let fact: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: term.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: None,
            }
            .into();
            let proof = self.verify_builtin_rule_premise(&fact, state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(proofs))
    }
}

fn split_terms(obj: &Obj, depth: usize) -> Option<CoefficientTerms> {
    if depth > 64 {
        return None;
    }
    if let Some(value) = EvalRational::from_obj(obj) {
        return Some(CoefficientTerms::new(value, Vec::new()));
    }
    match obj {
        Obj::ArithmeticOperator(A::Add(a)) => combine(
            split_terms(&a.left, depth + 1)?,
            split_terms(&a.right, depth + 1)?,
        ),
        Obj::ArithmeticOperator(A::Sub(a)) => combine(
            split_terms(&a.left, depth + 1)?,
            scale_terms(
                split_terms(&a.right, depth + 1)?,
                &EvalRational::new(-1, 1)?,
            )?,
        ),
        Obj::ArithmeticOperator(A::Neg(a)) => {
            scale_terms(split_terms(&a.arg, depth + 1)?, &EvalRational::new(-1, 1)?)
        }
        Obj::ArithmeticOperator(A::Mul(a)) => {
            if let Some(scale) = EvalRational::from_obj(&a.left) {
                return scale_terms(split_terms(&a.right, depth + 1)?, &scale);
            }
            if let Some(scale) = EvalRational::from_obj(&a.right) {
                return scale_terms(split_terms(&a.left, depth + 1)?, &scale);
            }
            Some(CoefficientTerms::new(
                EvalRational::new(0, 1)?,
                vec![(EvalRational::new(1, 1)?, obj.clone())],
            ))
        }
        Obj::ArithmeticOperator(A::Div(a)) => {
            let denominator = EvalRational::from_obj(&a.right)?;
            let scale = EvalRational::new(1, 1)?.div(&denominator)?;
            scale_terms(split_terms(&a.left, depth + 1)?, &scale)
        }
        _ => Some(CoefficientTerms::new(
            EvalRational::new(0, 1)?,
            vec![(EvalRational::new(1, 1)?, obj.clone())],
        )),
    }
}

fn scale_terms(mut terms: CoefficientTerms, scale: &EvalRational) -> Option<CoefficientTerms> {
    terms.constant = terms.constant.mul(scale)?;
    for (factor, _) in &mut terms.terms {
        *factor = factor.mul(scale)?;
    }
    Some(terms)
}

fn combine(mut left: CoefficientTerms, right: CoefficientTerms) -> Option<CoefficientTerms> {
    left.constant = left.constant.add(&right.constant)?;
    for (scale, term) in right.terms {
        if let Some((existing, _)) = left.terms.iter_mut().find(|(_, obj)| obj.ir() == term.ir()) {
            *existing = existing.add(&scale)?;
        } else {
            if left.terms.len() >= 64 {
                return None;
            }
            left.terms.push((scale, term));
        }
    }
    Some(left)
}

fn number(n: i128) -> Obj {
    EvalRational::new(n, 1)
        .expect("integer denominator")
        .to_obj()
}
fn negative(obj: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Neg(Neg { arg: Box::new(obj) }))
}
fn root(n: i128) -> Obj {
    Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
        arg: Box::new(number(n)),
    }))
}
fn quotient(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Div(Div {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

fn exact_trig_value(kind: TrigKind, constant: &EvalRational) -> Option<(i128, Obj)> {
    let reduced = constant.modulo_integer(if matches!(kind, TrigKind::Sin | TrigKind::Cos) {
        2
    } else {
        1
    })?;
    let parts = reduced.parts();
    // Integer zeros need only pi-periodicity, even for sine/cosine.
    if matches!(kind, TrigKind::Sin) && reduced.to_i128_if_integer().is_some() {
        return Some((1, number(0)));
    }
    if matches!(kind, TrigKind::Cos) && matches!(parts, (1, 2) | (3, 2)) {
        return Some((1, number(0)));
    }
    let period = if matches!(kind, TrigKind::Sin | TrigKind::Cos) {
        2
    } else {
        1
    };
    use TrigKind::*;
    let value = match (kind, parts) {
        (Sin, (1, 2)) | (Cos, (0, 1)) => number(1),
        (Sin, (3, 2)) | (Cos, (1, 1)) => number(-1),
        (Sin, (1, 6) | (5, 6)) | (Cos, (1, 3) | (5, 3)) => quotient(number(1), number(2)),
        (Sin, (7, 6) | (11, 6)) | (Cos, (2, 3) | (4, 3)) => quotient(number(-1), number(2)),
        (Sin, (1, 4) | (3, 4)) | (Cos, (1, 4) | (7, 4)) => quotient(root(2), number(2)),
        (Sin, (5, 4) | (7, 4)) | (Cos, (3, 4) | (5, 4)) => negative(quotient(root(2), number(2))),
        (Sin, (1, 3) | (2, 3)) | (Cos, (1, 6) | (11, 6)) => quotient(root(3), number(2)),
        (Sin, (4, 3) | (5, 3)) | (Cos, (5, 6) | (7, 6)) => negative(quotient(root(3), number(2))),
        (Tan, (0, 1)) | (Cot, (1, 2)) => number(0),
        (Tan | Cot, (1, 4)) => number(1),
        (Tan | Cot, (3, 4)) => number(-1),
        (Tan, (1, 6)) | (Cot, (1, 3)) => quotient(root(3), number(3)),
        (Tan, (5, 6)) | (Cot, (2, 3)) => negative(quotient(root(3), number(3))),
        (Tan, (1, 3)) | (Cot, (1, 6)) => root(3),
        (Tan, (2, 3)) | (Cot, (5, 6)) => negative(root(3)),
        _ => return None,
    };
    Some((period, value))
}
