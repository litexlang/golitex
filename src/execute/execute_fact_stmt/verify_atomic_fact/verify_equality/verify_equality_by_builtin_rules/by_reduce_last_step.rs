//! One nonempty left-fold step, consuming no fresh search budget.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, LessEqualFact};
use crate::ast::obj::{
    ArithmeticOperator, FnObj, FnObjHead, FunctionSpace, IteratedOperator, Literal, Number, Obj,
    Reduce, Sub,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct ReduceLastStepProof {
    pub nonempty: VerifyFactResult,
    pub endpoint: VerifyFactResult,
    pub result: VerifyFactResult,
}
impl Runtime {
    pub(super) fn search_reduce_last_step(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ReduceLastStepProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(r)) = left else {
                continue;
            };
            let nonempty = Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *r.start.clone(),
                right: *r.end.clone(),
                line_file: None,
            }));
            let nonempty = self.verify_builtin_rule_premise(&nonempty, state.clone())?;
            if nonempty.is_failed() {
                continue;
            }
            let previous_end = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                left: r.end.clone(),
                right: Box::new(Obj::Literal(Literal::Number(Number::new("1".into())))),
            }));
            let normalized_end =
                crate::rational_expression::evaluate_obj_to_normalized_decimal_number(
                    &previous_end,
                )
                .map(|number| Obj::Literal(Literal::Number(number)))
                .unwrap_or_else(|| previous_end.clone());
            let endpoint = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: previous_end,
                right: normalized_end.clone(),
                line_file: None,
            }));
            let endpoint = self.verify_builtin_rule_premise(&endpoint, state.clone())?;
            if endpoint.is_failed() {
                continue;
            }
            let previous = Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                start: r.start.clone(),
                end: Box::new(normalized_end),
                func: r.func.clone(),
                op: r.op.clone(),
                seed: r.seed.clone(),
            }));
            let Some(term) = apply(&r.func, vec![*r.end.clone()]) else {
                continue;
            };
            let Some(expected) = apply(&r.op, vec![previous, term]) else {
                continue;
            };
            let result = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: expected,
                right: right.clone(),
                line_file: None,
            }));
            let result = self.verify_builtin_rule_premise(&result, state.clone())?;
            if !result.is_failed() {
                return Ok(Some(ReduceLastStepProof {
                    nonempty,
                    endpoint,
                    result,
                }));
            }
        }
        Ok(None)
    }
}
fn apply(function: &Obj, args: Vec<Obj>) -> Option<Obj> {
    let (head, mut body) = match function {
        Obj::Identifier(id) => (FnObjHead::Identifier(id.clone()), vec![]),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)) => {
            (FnObjHead::AnonymousFnLiteral(Box::new(a.clone())), vec![])
        }
        Obj::FnObj(f) => (f.head.as_ref().clone(), f.body.clone()),
        _ => return None,
    };
    body.push(args.into_iter().map(Box::new).collect());
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body,
    }))
}
