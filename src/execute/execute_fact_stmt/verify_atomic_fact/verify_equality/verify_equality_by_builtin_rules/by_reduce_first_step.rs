//! Pop the first term into the seed of the remaining left fold.
use super::reduce_rule_helper::{reduce_application, ReduceNonemptyProof, ReduceObjectMatchProof};
use crate::ast::fact::EqualFact;
use crate::ast::obj::{IteratedOperator, Literal, Number, Obj};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::helper::add_objs;
use crate::runtime::{Runtime, RuntimeResult};

pub struct ReduceFirstStepProof {
    pub nonempty: ReduceNonemptyProof,
    pub matches: Vec<ReduceObjectMatchProof>,
}
impl Runtime {
    pub(super) fn search_reduce_first_step(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ReduceFirstStepProof>> {
        // reduce(a,b,f,op,s)=reduce(a+1,b,f,op,op(s,f(a))) when a<=b.
        // No exchange of operands and no associativity requirement.
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(whole)) = left else {
                continue;
            };
            let Obj::IteratedOperator(IteratedOperator::Reduce(rest)) = right else {
                continue;
            };
            let Some(nonempty) =
                self.reduce_nonempty_proof(&whole.start, &whole.end, fact, state)?
            else {
                continue;
            };
            let next = add_objs(
                *whole.start.clone(),
                Obj::Literal(Literal::Number(Number::new("1".into()))),
            );
            let Some(term) = reduce_application(&whole.func, vec![*whole.start.clone()]) else {
                continue;
            };
            let Some(seed) = reduce_application(&whole.op, vec![*whole.seed.clone(), term]) else {
                continue;
            };
            let mut matches = Vec::new();
            for (a, b) in [
                (&next, &*rest.start),
                (&*whole.end, &*rest.end),
                (&*whole.func, &*rest.func),
                (&*whole.op, &*rest.op),
                (&seed, &*rest.seed),
            ] {
                let Some(proof) = self.match_reduce_object(a, b) else {
                    break;
                };
                matches.push(proof);
            }
            if matches.len() == 5 {
                return Ok(Some(ReduceFirstStepProof { nonempty, matches }));
            }
        }
        Ok(None)
    }
}
