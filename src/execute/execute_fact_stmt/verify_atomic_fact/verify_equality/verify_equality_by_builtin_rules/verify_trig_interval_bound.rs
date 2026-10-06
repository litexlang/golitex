//! Check the actual written bounds of fixed real trigonometric intervals.
use super::by_inverse_trig::{half_pi, negative_half_pi, zero_obj};
use crate::ast::fact::{AtomicFact, Fact, GreaterEqualFact, GreaterFact};
use crate::ast::obj::{ArithmeticOperator, Literal, Mul, Neg, Number, Obj, Sub};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub(in crate::execute) enum TrigIntervalBoundSide {
    Lower,
    Upper,
}

impl Runtime {
    // All candidates express the same fixed interval condition. Keep the
    // successful written fact and its real citation, rather than relabeling it
    // as a proof of the canonical spelling. At most four spellings and two
    // orientations; every candidate uses the inherited premise ceiling.
    // Example: -(pi/2)<=y is the lower bound of arcsin's principal interval.
    pub(in crate::execute) fn verify_trig_interval_bound(
        &mut self,
        premise: &Fact,
        side: TrigIntervalBoundSide,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let first = self.verify_builtin_rule_premise(premise, state.clone())?;
        if !first.is_failed() {
            return Ok(Some(first));
        }
        let (left, right) = match premise {
            Fact::AtomicFact(AtomicFact::LessFact(p)) => (&p.left, &p.right),
            Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => (&p.left, &p.right),
            _ => return Ok(None),
        };
        let bound = match side {
            TrigIntervalBoundSide::Lower => left,
            TrigIntervalBoundSide::Upper => right,
        };
        for (index, spelling) in trig_interval_bound_spellings(bound).into_iter().enumerate() {
            let (left, right) = match side {
                TrigIntervalBoundSide::Lower => (spelling, right.clone()),
                TrigIntervalBoundSide::Upper => (left.clone(), spelling),
            };
            for reverse in [false, true] {
                if index == 0 && !reverse {
                    continue;
                }
                let candidate: Fact = match premise {
                    Fact::AtomicFact(AtomicFact::LessFact(p)) if reverse => GreaterFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: right.clone(),
                        right: left.clone(),
                        line_file: p.line_file.clone(),
                    }
                    .into(),
                    Fact::AtomicFact(AtomicFact::LessEqualFact(p)) if reverse => GreaterEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: right.clone(),
                        right: left.clone(),
                        line_file: p.line_file.clone(),
                    }
                    .into(),
                    Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                        let mut p = p.clone();
                        p.fact_id = self.global_ids.allocate_fact_id();
                        p.left = left.clone();
                        p.right = right.clone();
                        p.into()
                    }
                    Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => {
                        let mut p = p.clone();
                        p.fact_id = self.global_ids.allocate_fact_id();
                        p.left = left.clone();
                        p.right = right.clone();
                        p.into()
                    }
                    _ => return Ok(None),
                };
                let proof = self.verify_builtin_rule_premise(&candidate, state.clone())?;
                if !proof.is_failed() {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }
}

// Pure fixed-constant surface recognition; no arbitrary symbolic rewrite.
// (-pi)/2, -(pi/2), 0-pi/2 and (-1)*(pi/2) have the same real value.
// The angle expression is untouched, and strictness is owned by the caller.
pub(in crate::execute) fn trig_interval_bound_spellings(bound: &Obj) -> Vec<Obj> {
    let mut result = vec![bound.clone()];
    if bound.ir() == negative_half_pi().ir() {
        result.push(Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(half_pi()),
        })));
        result.push(Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: Box::new(zero_obj()),
            right: Box::new(half_pi()),
        })));
        result.push(Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(Obj::Literal(Literal::Number(Number {
                normalized_value: "-1".to_string(),
            }))),
            right: Box::new(half_pi()),
        })));
    }
    result
}
