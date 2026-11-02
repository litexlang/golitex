//! Finite expression trees, not a fixed number of summands or a search loop.
use super::result::*;
use crate::prelude::*;

pub struct FiniteSumUpperBoundProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct AbsoluteSumTriangleProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
impl FiniteSumUpperBoundProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl AbsoluteSumTriangleProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}

impl Runtime {
    pub(super) fn search_finite_additive_bound(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        let (left, right, line_file) = match fact {
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, &f.line_file),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, &f.line_file),
            _ => return Ok(None),
        };
        let mut leaves = Vec::new();
        if let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left {
            additive_leaves(&abs.arg, &mut leaves);
            if leaves.len() < 3 {
                return Ok(None);
            }
            let mut requirements = Vec::new();
            for leaf in &leaves {
                requirements.push(self.strategy_in_fact(
                    leaf.clone(),
                    Obj::StandardSet(StandardSet::R),
                    line_file.clone(),
                ));
            }
            let mut magnitudes = leaves.into_iter().map(|arg| {
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(arg) }))
            });
            let Some(mut upper) = magnitudes.next() else {
                return Ok(None);
            };
            for term in magnitudes {
                upper = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: Box::new(upper),
                    right: Box::new(term),
                }));
            }
            requirements.push(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: upper,
                    right: right.clone(),
                    line_file: line_file.clone(),
                }
                .into(),
            );
            let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, state)?
            else {
                return Ok(None);
            };
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsoluteSumTriangle(
                    AbsoluteSumTriangleProof::new(requirement_facts, proof_of_requirement_facts),
                ),
            ));
        }
        additive_leaves(left, &mut leaves);
        if leaves.len() < 3 {
            return Ok(None);
        }
        let count = leaves.len().to_string();
        let is_count = |obj: &Obj| matches!(obj, Obj::Literal(Literal::Number(n)) if n.normalized_value == count);
        let common = match right {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(product))
                if is_count(&product.left) =>
            {
                Some(product.right.as_ref())
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(product))
                if is_count(&product.right) =>
            {
                Some(product.left.as_ref())
            }
            _ => None,
        };
        let mut bounds = Vec::new();
        if let Some(bound) = common {
            bounds.resize(leaves.len(), bound.clone());
        } else {
            additive_leaves(right, &mut bounds);
        }
        if bounds.len() != leaves.len() {
            return Ok(None);
        }
        let requirements = leaves
            .into_iter()
            .zip(bounds)
            .map(|(leaf, bound)| self.strategy_less_equal_fact(leaf, bound, line_file.clone()))
            .collect();
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, state)?
        else {
            return Ok(None);
        };
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSumUpperBound(
                FiniteSumUpperBoundProof::new(requirement_facts, proof_of_requirement_facts),
            ),
        ))
    }
}

fn additive_leaves(obj: &Obj, leaves: &mut Vec<Obj>) {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = obj {
        additive_leaves(&sum.left, leaves);
        additive_leaves(&sum.right, leaves);
    } else {
        leaves.push(obj.clone());
    }
}
