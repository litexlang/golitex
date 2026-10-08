//! Consume a checked Euclidean decomposition and a bounded natural remainder.
use crate::ast::fact::{EqualFact, Fact, InFact, LessFact};
use crate::ast::obj::{ArithmeticOperator, IntegerOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::runtime::{Runtime, RuntimeResult};

pub struct EuclideanRemainderProof {
    pub domains: Vec<VerifyFactResult>,
    pub remainder_bound: VerifyFactResult,
    pub decomposition: Box<EqualFactSearchedProof>,
}

impl Runtime {
    pub(super) fn search_euclidean_remainder(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<EuclideanRemainderProof>> {
        // a=m*q+r, a,q in Z, m in N+, r in N and r<m imply a%m=r.
        for (modulus_side, remainder) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = modulus_side else {
                continue;
            };
            let members = equivalence_class_members_with_paths_in_adjacency(
                &self.visible_equivalence_class_adjacency(),
                &rem.left,
            );
            for (candidate, _) in members {
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &candidate else {
                    continue;
                };
                for (product, r) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                    if r.ir() != remainder.ir() {
                        continue;
                    }
                    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = product else {
                        continue;
                    };
                    let quotient = if mul.left.ir() == rem.right.ir() {
                        &*mul.right
                    } else if mul.right.ir() == rem.right.ir() {
                        &*mul.left
                    } else {
                        continue;
                    };
                    let mut domains = Vec::new();
                    for (obj, set) in [
                        (&*rem.left, StandardSet::Z),
                        (quotient, StandardSet::Z),
                        (&*rem.right, StandardSet::NPos),
                        (remainder, StandardSet::N),
                    ] {
                        let goal: Fact = InFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            element: obj.clone(),
                            set: Obj::StandardSet(set),
                            line_file: fact.line_file.clone(),
                        }
                        .into();
                        let proof = self.verify_builtin_rule_premise(&goal, state)?;
                        if proof.is_failed() {
                            break;
                        }
                        domains.push(proof);
                    }
                    if domains.len() != 4 {
                        continue;
                    }
                    let bound: Fact = LessFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: remainder.clone(),
                        right: *rem.right.clone(),
                        line_file: fact.line_file.clone(),
                    }
                    .into();
                    let remainder_bound = self.verify_builtin_rule_premise(&bound, state)?;
                    if remainder_bound.is_failed() {
                        continue;
                    }
                    if let Some(decomposition) =
                        self.lookup_known_obj_equality(&rem.left, &candidate)
                    {
                        return Ok(Some(EuclideanRemainderProof {
                            domains,
                            remainder_bound,
                            decomposition: Box::new(decomposition),
                        }));
                    }
                }
            }
        }
        Ok(None)
    }
}
