use super::result::*;
use crate::prelude::*;

pub struct PositiveReciprocalLessEqualProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct PositiveReciprocalLessProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
impl PositiveReciprocalLessEqualProof {
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
impl PositiveReciprocalLessProof {
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
    pub(super) fn search_positive_reciprocal_order(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        let (left, right, strict, line_file) = match fact {
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false, &f.line_file),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, false, &f.line_file),
            AtomicFact::LessFact(f) => (&f.left, &f.right, true, &f.line_file),
            AtomicFact::GreaterFact(f) => (&f.right, &f.left, true, &f.line_file),
            _ => return Ok(None),
        };
        let (Some(y), Some(x)) = (reciprocal_denominator(left), reciprocal_denominator(right))
        else {
            return Ok(None);
        };
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        let mut requirements = vec![
            self.strategy_less_fact(zero.clone(), x.clone(), line_file.clone()),
            self.strategy_less_fact(zero, y.clone(), line_file.clone()),
        ];
        requirements.push(if strict {
            self.strategy_less_fact(x.clone(), y.clone(), line_file.clone())
        } else {
            self.strategy_less_equal_fact(x.clone(), y.clone(), line_file.clone())
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, state)?
        else {
            return Ok(None);
        };
        Ok(Some(if strict {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveReciprocalLess(
                PositiveReciprocalLessProof::new(requirement_facts, proof_of_requirement_facts),
            )
        } else {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveReciprocalLessEqual(
                PositiveReciprocalLessEqualProof::new(
                    requirement_facts,
                    proof_of_requirement_facts,
                ),
            )
        }))
    }
}

fn reciprocal_denominator(obj: &Obj) -> Option<&Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = obj else {
        return None;
    };
    matches!(div.left.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
        .then_some(div.right.as_ref())
}
