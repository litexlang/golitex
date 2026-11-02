//! Bounded composition of existing coordinate and magnitude evidence.
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::prelude::*;

pub struct CartesianCoordinateEqualityProof {
    pub left_shape: KnownTupleShapeProof,
    pub right_shape: KnownTupleShapeProof,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct AbsProductFromFactorsProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct FunctionApplicationCongruenceProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
impl CartesianCoordinateEqualityProof {
    pub fn new(
        left_shape: KnownTupleShapeProof,
        right_shape: KnownTupleShapeProof,
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            left_shape,
            right_shape,
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl AbsProductFromFactorsProof {
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
impl FunctionApplicationCongruenceProof {
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
    // Preserve equality of a callable prefix instead of flattening it into
    // equality of its inputs: F(a)=F(b) need not imply a=b.
    pub(super) fn search_function_application_congruence(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionApplicationCongruenceProof>> {
        let (Obj::FnObj(left), Obj::FnObj(right)) = (&fact.left, &fact.right) else {
            return Ok(None);
        };
        let (Some(left_args), Some(right_args)) = (left.body.last(), right.body.last()) else {
            return Ok(None);
        };
        if left_args.len() != right_args.len() {
            return Ok(None);
        }
        let mut pairs = vec![(
            super::helper::fn_obj_prefix_obj(left, left.body.len() - 1),
            super::helper::fn_obj_prefix_obj(right, right.body.len() - 1),
        )];
        pairs.extend(
            left_args
                .iter()
                .zip(right_args)
                .map(|(a, b)| (a.as_ref().clone(), b.as_ref().clone())),
        );
        let requirements = pairs
            .into_iter()
            .map(|(left, right)| {
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right,
                    line_file: fact.line_file.clone(),
                }
                .into()
            })
            .collect();
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, state)?
        else {
            return Ok(None);
        };
        Ok(Some(FunctionApplicationCongruenceProof::new(
            requirement_facts,
            proof_of_requirement_facts,
        )))
    }

    pub(super) fn search_cartesian_coordinate_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<CartesianCoordinateEqualityProof>> {
        let (Some(left_shape), Some(right_shape)) = (
            self.lookup_known_tuple_shape(&fact.left),
            self.lookup_known_tuple_shape(&fact.right),
        ) else {
            return Ok(None);
        };
        if left_shape.dimension() != right_shape.dimension() {
            return Ok(None);
        }
        let mut requirements = Vec::new();
        for index in 0..left_shape.dimension() {
            let (Ok(left), Ok(right)) = (
                finite_function_coordinate(&fact.left, index),
                finite_function_coordinate(&fact.right, index),
            ) else {
                return Ok(None);
            };
            requirements.push(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right,
                    line_file: fact.line_file.clone(),
                }
                .into(),
            );
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, state)?
        else {
            return Ok(None);
        };
        Ok(Some(CartesianCoordinateEqualityProof::new(
            left_shape,
            right_shape,
            requirement_facts,
            proof_of_requirement_facts,
        )))
    }

    pub(super) fn search_abs_product_from_factors(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AbsProductFromFactorsProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(input)) = abs.arg.as_ref() else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(output)) = right else {
                continue;
            };
            let mut alternatives = Vec::new();
            for (first, second) in [(&output.left, &output.right), (&output.right, &output.left)] {
                let mut requirements = Vec::new();
                for (argument, magnitude) in [(&input.left, first), (&input.right, second)] {
                    requirements.push(
                        EqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
                                arg: argument.clone(),
                            })),
                            right: magnitude.as_ref().clone(),
                            line_file: fact.line_file.clone(),
                        }
                        .into(),
                    );
                }
                alternatives.push(requirements);
            }
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.try_strategy_requirement_alternatives(alternatives, state)?
            {
                return Ok(Some(AbsProductFromFactorsProof::new(
                    requirement_facts,
                    proof_of_requirement_facts,
                )));
            }
        }
        Ok(None)
    }
}
