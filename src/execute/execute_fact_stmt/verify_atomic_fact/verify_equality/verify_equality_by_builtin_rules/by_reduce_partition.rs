//! Adjacent partition of a left fold; no associativity or commutativity is needed.
use crate::ast::fact::{EqualFact, Fact, LessEqualFact};
use crate::ast::obj::{IteratedOperator, Literal, Number, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::helper::add_objs;
use crate::runtime::{Runtime, RuntimeResult};

pub struct ReducePartitionProof {
    pub bounds: Vec<VerifyFactResult>,
    pub matches: Vec<VerifyFactResult>,
}

impl Runtime {
    pub(super) fn search_reduce_partition(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ReducePartitionProof>> {
        // reduce(a,c,f,op,s) = reduce(b+1,c,f,op,reduce(a,b,f,op,s)).
        // The first segment is nonempty; the second may be empty when b=c.
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(whole)) = left else {
                continue;
            };
            let Obj::IteratedOperator(IteratedOperator::Reduce(second)) = right else {
                continue;
            };
            let Obj::IteratedOperator(IteratedOperator::Reduce(first)) = &*second.seed else {
                continue;
            };
            let mut bounds = Vec::new();
            for (lower, upper) in [(&*whole.start, &*first.end), (&*first.end, &*whole.end)] {
                let goal: Fact = LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: lower.clone(),
                    right: upper.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let proof = self.verify_builtin_rule_premise(&goal, state.clone())?;
                if proof.is_failed() {
                    break;
                }
                bounds.push(proof);
            }
            if bounds.len() != 2 {
                continue;
            }
            let next = add_objs(
                *first.end.clone(),
                Obj::Literal(Literal::Number(Number::new("1".into()))),
            );
            let mut matches = Vec::new();
            for (a, b) in [
                (&*whole.start, &*first.start),
                (&*whole.end, &*second.end),
                (&next, &*second.start),
                (&*whole.func, &*first.func),
                (&*whole.func, &*second.func),
                (&*whole.op, &*first.op),
                (&*whole.op, &*second.op),
                (&*whole.seed, &*first.seed),
            ] {
                let goal: Fact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: a.clone(),
                    right: b.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let proof = self.verify_builtin_rule_premise(&goal, state.clone())?;
                if proof.is_failed() {
                    break;
                }
                matches.push(proof);
            }
            if matches.len() == 8 {
                return Ok(Some(ReducePartitionProof { bounds, matches }));
            }
        }
        Ok(None)
    }
}
