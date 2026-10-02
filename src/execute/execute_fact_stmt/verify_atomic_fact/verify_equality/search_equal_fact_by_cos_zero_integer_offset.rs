use super::by_builtin_strategy_result::CosZeroIntegerOffsetStrategySingleStep;
use super::verify_equality_by_builtin_rules::by_inverse_trig::{half_pi, pi_obj};
use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{
    Add, ArithmeticOperator, Cos, Div, Literal, Mul, Neg, Number, Obj, StandardSet, Sub,
    TrigOperator,
};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::rational_expression::{
    evaluate_obj_to_normalized_decimal_number, objs_equal_by_rational_expression_evaluation,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // See CosZeroIntegerOffsetStrategySingleStep for the mathematical rule.
    // The enclosing equality WD checks the real cosine argument first.
    pub fn search_equal_fact_by_cos_zero_integer_offset(
        &mut self,
        fact: &EqualFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<CosZeroIntegerOffsetStrategySingleStep>> {
        if !ctx.can_use_strategy() {
            return Ok(None);
        }
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) = left else {
                continue;
            };
            // A literal zero avoids silently cancelling unproved denominators
            // on the conclusion's other side.
            if !matches!(right, Obj::Literal(Literal::Number(n)) if n.normalized_value == "0") {
                continue;
            }
            let offset = divide(subtract(arg.as_ref().clone(), half_pi()), pi_obj());
            let direct = self.cos_integer_requirement(offset.clone());
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(vec![direct], ctx)?
            {
                return Ok(Some(CosZeroIntegerOffsetStrategySingleStep {
                    requirement_facts,
                    proof_of_requirement_facts,
                }));
            }

            // Try only candidates derived from this angle's syntax. They are
            // hints, never evidence: BOTH the equality and Z membership below
            // must be proved, including every division's nonzero obligation.
            let Some(coefficient) = pi_coefficient(arg) else {
                continue;
            };
            let shifted = subtract(coefficient.clone(), divide(number("1"), number("2")));
            let mut candidates = Vec::new();
            if let Some(value) = evaluate_obj_to_normalized_decimal_number(&shifted) {
                candidates.push(Obj::Literal(Literal::Number(value)));
            }
            candidates.push(shifted);
            collect_arithmetic_subterms(&coefficient, &mut candidates);
            let mut seen = std::collections::HashSet::new();
            for candidate in candidates {
                if !seen.insert(candidate.ir())
                    || !objs_equal_by_rational_expression_evaluation(&offset, &candidate)
                {
                    continue;
                }
                let equal: Fact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: offset.clone(),
                    right: candidate.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let integer = self.cos_integer_requirement(candidate);
                if let Some((requirement_facts, proof_of_requirement_facts)) =
                    self.verify_strategy_requirements(vec![equal, integer], ctx)?
                {
                    return Ok(Some(CosZeroIntegerOffsetStrategySingleStep {
                        requirement_facts,
                        proof_of_requirement_facts,
                    }));
                }
            }
        }
        Ok(None)
    }

    fn cos_integer_requirement(&mut self, element: Obj) -> Fact {
        InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set: Obj::StandardSet(StandardSet::Z),
            line_file: None,
        }
        .into()
    }
}

fn number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.to_string(),
    }))
}
fn subtract(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
fn divide(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
fn multiply(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

// Local syntactic extraction, not a new algebra normalizer. Any proposed
// coefficient is checked through an ordinary strategy equality subgoal.
fn pi_coefficient(angle: &Obj) -> Option<Obj> {
    match angle {
        Obj::Literal(Literal::Pi(_)) => Some(number("1")),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            if let Some(c) = pi_coefficient(left) {
                Some(multiply(c, right.as_ref().clone()))
            } else {
                pi_coefficient(right).map(|c| multiply(left.as_ref().clone(), c))
            }
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            pi_coefficient(left).map(|c| divide(c, right.as_ref().clone()))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => pi_coefficient(arg)
            .map(|c| Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(c) }))),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Some(Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(pi_coefficient(left)?),
                right: Box::new(pi_coefficient(right)?),
            })))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            Some(subtract(pi_coefficient(left)?, pi_coefficient(right)?))
        }
        _ => None,
    }
}

fn collect_arithmetic_subterms(obj: &Obj, result: &mut Vec<Obj>) {
    result.push(obj.clone());
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right }))
        | Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
        | Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right }))
        | Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            collect_arithmetic_subterms(left, result);
            collect_arithmetic_subterms(right, result);
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => {
            collect_arithmetic_subterms(arg, result)
        }
        _ => {}
    }
}
