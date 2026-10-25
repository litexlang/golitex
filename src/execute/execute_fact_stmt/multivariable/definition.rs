use super::super::matrix_operations::anonymous;
use super::super::native_matrix::matrix_space;
use super::helper::*;
use crate::prelude::*;
use crate::rational_expression::helper::{div_objs, mul_objs, sub_objs};

impl Runtime {
    pub(crate) fn multivariable_defining_clauses(
        &mut self,
        relation: &MultivariableAnalysisRelation,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        let Some((source, _)) = self.multivariable_signature_requirements(relation, state)? else {
            return Ok(None);
        };
        let domain = actual_domain(&source.signature).unwrap();
        let args = relation.argument_refs();
        let function = args[0].clone();
        let point = args[1].clone();
        let n = input_dimension(relation);
        use MultivariableAnalysisRelation::*;
        let clauses = match relation {
            ScalarLimit(x) => vec![
                self.multivariable_accumulation(domain.clone(), point.clone(), n.clone()),
                self.multivariable_epsilon_control(
                    function,
                    domain,
                    point,
                    n,
                    None,
                    x.value.clone(),
                    false,
                ),
            ],
            VectorLimit(x) => vec![
                self.multivariable_accumulation(domain.clone(), point.clone(), n.clone()),
                self.multivariable_epsilon_control(
                    function,
                    domain,
                    point,
                    n,
                    Some(x.output_dimension.clone()),
                    x.value.clone(),
                    false,
                ),
            ],
            ScalarContinuousAt(_) => {
                let target = apply(&function, vec![point.clone()]);
                vec![self
                    .multivariable_epsilon_control(function, domain, point, n, None, target, true)]
            }
            VectorContinuousAt(x) => {
                let target = apply(&function, vec![point.clone()]);
                vec![self.multivariable_epsilon_control(
                    function,
                    domain,
                    point,
                    n,
                    Some(x.output_dimension.clone()),
                    target,
                    true,
                )]
            }
            ScalarDifferentiableAt(_) => {
                let value = self.fresh_internal_param();
                let candidate = relation_from_args(
                    self,
                    "has_scalar_differential_at",
                    vec![function, point, n.clone(), identifier(&value)],
                );
                vec![exists(
                    self,
                    value,
                    matrix_space(real(), number(1), n),
                    vec![candidate],
                )]
            }
            TotalDifferentiableAt(x) => {
                let value = self.fresh_internal_param();
                let candidate = relation_from_args(
                    self,
                    "has_total_derivative_at",
                    vec![
                        function,
                        point,
                        n.clone(),
                        x.output_dimension.clone(),
                        identifier(&value),
                    ],
                );
                vec![exists(
                    self,
                    value,
                    matrix_space(real(), x.output_dimension.clone(), n),
                    vec![candidate],
                )]
            }
            PartialDerivativeAt(x) => {
                let h = self.fresh_internal_param();
                let h_obj = identifier(&h);
                let path = self.multivariable_coordinate_path(
                    point.clone(),
                    n.clone(),
                    x.coordinate.clone(),
                    h_obj.clone(),
                );
                let path_in_domain = member(self, path.clone(), domain.clone());
                let section_domain = build_set(h.clone(), real(), vec![path_in_domain]);
                let radius = self.fresh_internal_param();
                let t = self.fresh_internal_param();
                let near = less(self, absolute(identifier(&t)), identifier(&radius));
                let interval = build_set(t, real(), vec![near]);
                let inclusion = subset(self, interval, section_domain.clone());
                let interior = exists(self, radius, positive_real(), vec![inclusion]);
                let nonzero = nonzero(self, h_obj.clone());
                let in_domain = member(self, path.clone(), domain);
                let body = div_objs(
                    sub_objs(apply(&function, vec![path]), apply(&function, vec![point])),
                    h_obj,
                );
                let quotient = Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
                    body: FnSet {
                        set_bound_parameters: SetBoundParameterList {
                            groups: vec![SetBoundParameterGroup {
                                params: vec![h],
                                param_type: Box::new(real()),
                            }],
                        },
                        dom_facts: vec![fact_to_guard(nonzero), fact_to_guard(in_domain)],
                        ret_set: Box::new(real()),
                    },
                    equal_to: Box::new(body),
                }));
                let limit = HasFunctionLimitFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    function: quotient,
                    approach: LimitApproach::AtPoint(Box::new(number(0))),
                    value: x.value.clone(),
                    line_file: None,
                }
                .into();
                vec![interior, limit]
            }
            ScalarDifferentialAt(x) => vec![
                self.multivariable_interior(domain.clone(), point.clone(), n.clone()),
                self.multivariable_remainder_control(
                    function,
                    domain,
                    point,
                    n,
                    None,
                    x.value.clone(),
                ),
            ],
            TotalDerivativeAt(x) => vec![
                self.multivariable_interior(domain.clone(), point.clone(), n.clone()),
                self.multivariable_remainder_control(
                    function,
                    domain,
                    point,
                    n,
                    Some(x.output_dimension.clone()),
                    x.value.clone(),
                ),
            ],
            GradientAt(x) => {
                let axis = self.fresh_internal_param();
                let k = identifier(&axis);
                let candidate = relation_from_args(
                    self,
                    "has_partial_derivative_at",
                    vec![
                        function,
                        point,
                        n.clone(),
                        k.clone(),
                        apply(&x.value, vec![k]),
                    ],
                );
                vec![quantified(self, axis, indices(n), vec![], vec![candidate])]
            }
            JacobianAt(x) => {
                let row = self.fresh_internal_param();
                let col = self.fresh_internal_param();
                let r = identifier(&row);
                let c = identifier(&col);
                let component = self.multivariable_component_function(function, domain, r.clone());
                let candidate = relation_from_args(
                    self,
                    "has_partial_derivative_at",
                    vec![
                        component,
                        point,
                        n.clone(),
                        c.clone(),
                        apply(&x.value, vec![r, c]),
                    ],
                );
                let inner = quantified(self, col, indices(n), vec![], vec![candidate]);
                vec![quantified(
                    self,
                    row,
                    indices(x.output_dimension.clone()),
                    vec![],
                    vec![inner],
                )]
            }
            HessianAt(x) => {
                let row = self.fresh_internal_param();
                let col = self.fresh_internal_param();
                let r = identifier(&row);
                let c = identifier(&col);
                let candidate = relation_from_args(
                    self,
                    "has_second_partial_derivative_at",
                    vec![
                        function,
                        point,
                        n.clone(),
                        r.clone(),
                        c.clone(),
                        apply(&x.value, vec![r, c]),
                    ],
                );
                let inner = quantified(self, col, indices(n.clone()), vec![], vec![candidate]);
                vec![quantified(self, row, indices(n), vec![], vec![inner])]
            }
            DivergenceAt(x) => vec![self.multivariable_diagonal_sum_definition(
                function,
                domain,
                point,
                n,
                x.value.clone(),
                false,
            )],
            LaplacianAt(x) => vec![self.multivariable_diagonal_sum_definition(
                function,
                domain,
                point,
                n,
                x.value.clone(),
                true,
            )],
            CurlAt(x) => {
                let values = self.fresh_internal_param();
                let v = identifier(&values);
                let mut body = Vec::new();
                for (slot, component, axis) in [
                    (1, 3, 2),
                    (2, 2, 3),
                    (3, 1, 3),
                    (4, 3, 1),
                    (5, 2, 1),
                    (6, 1, 2),
                ] {
                    let scalar = self.multivariable_component_function(
                        function.clone(),
                        domain.clone(),
                        number(component),
                    );
                    body.push(relation_from_args(
                        self,
                        "has_partial_derivative_at",
                        vec![
                            scalar,
                            point.clone(),
                            number(3),
                            number(axis),
                            apply(&v, vec![number(slot)]),
                        ],
                    ));
                }
                for (axis, left, right) in [(1, 1, 2), (2, 3, 4), (3, 5, 6)] {
                    body.push(equal(
                        self,
                        apply(&x.value, vec![number(axis)]),
                        sub_objs(
                            apply(&v, vec![number(left)]),
                            apply(&v, vec![number(right)]),
                        ),
                    ));
                }
                vec![exists(self, values, vector(number(6)), body)]
            }
            SecondPartialDerivativeAt(x) => {
                let local = self.fresh_internal_param();
                let local_set = identifier(&local);
                let first = self.fresh_internal_param();
                let first_function = identifier(&first);
                let q = self.fresh_internal_param();
                let q_obj = identifier(&q);
                let first_candidate = relation_from_args(
                    self,
                    "has_partial_derivative_at",
                    vec![
                        function,
                        q_obj.clone(),
                        n.clone(),
                        x.first_coordinate.clone(),
                        apply(&first_function, vec![q_obj]),
                    ],
                );
                let good_points = build_set(q, local_set.clone(), vec![first_candidate]);
                let mut body = vec![
                    subset(self, local_set.clone(), domain),
                    member(self, point.clone(), local_set.clone()),
                    subset(self, local_set.clone(), good_points),
                ];
                body.push(relation_from_args(
                    self,
                    "has_partial_derivative_at",
                    vec![
                        first_function,
                        point,
                        n.clone(),
                        x.second_coordinate.clone(),
                        x.value.clone(),
                    ],
                ));
                let local_type = Obj::SetOperator(SetOperator::PowerSet(PowerSet {
                    set: Box::new(vector(n)),
                }));
                let input = self.fresh_internal_param();
                let function_type = function_space(input, local_set, real());
                vec![exists_many(
                    self,
                    vec![(local, local_type), (first, function_type)],
                    body,
                )]
            }
        };
        Ok(Some(clauses))
    }
    pub(crate) fn multivariable_accumulation(&mut self, domain: Obj, point: Obj, n: Obj) -> Fact {
        let radius = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let d = self.multivariable_distance(identifier(&x), point, n);
        let lower = less(self, number(0), d.clone());
        let upper = less(self, d, identifier(&radius));
        let witness = exists(self, x, domain, vec![lower, upper]);
        quantified(self, radius, positive_real(), vec![], vec![witness])
    }
    pub(crate) fn multivariable_interior(&mut self, domain: Obj, point: Obj, n: Obj) -> Fact {
        let radius = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let distance = self.multivariable_distance(identifier(&x), point, n.clone());
        let near = less(self, distance, identifier(&radius));
        let ball = build_set(x, vector(n), vec![near]);
        let inclusion = subset(self, ball, domain);
        exists(self, radius, positive_real(), vec![inclusion])
    }
    fn multivariable_epsilon_control(
        &mut self,
        function: Obj,
        domain: Obj,
        point: Obj,
        n: Obj,
        m: Option<Obj>,
        target: Obj,
        continuous: bool,
    ) -> Fact {
        let epsilon = self.fresh_internal_param();
        let delta = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let x_obj = identifier(&x);
        let distance = self.multivariable_distance(x_obj.clone(), point.clone(), n.clone());
        let mut guards = vec![];
        if !continuous {
            guards.push(less(self, number(0), distance.clone()));
        }
        guards.push(less(self, distance, identifier(&delta)));
        let near = build_set(x, domain.clone(), guards);
        let y = self.fresh_internal_param();
        let output = apply(&function, vec![identifier(&y)]);
        let error = match m {
            Some(m) => self.multivariable_distance(output, target, m),
            None => absolute(sub_objs(output, target)),
        };
        let within = less(self, error, identifier(&epsilon));
        let good = build_set(y, domain, vec![within]);
        let inclusion = subset(self, near, good);
        let radius = exists(self, delta, positive_real(), vec![inclusion]);
        quantified(self, epsilon, positive_real(), vec![], vec![radius])
    }
    fn multivariable_remainder_control(
        &mut self,
        function: Obj,
        domain: Obj,
        point: Obj,
        n: Obj,
        m: Option<Obj>,
        matrix: Obj,
    ) -> Fact {
        let epsilon = self.fresh_internal_param();
        let delta = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let x_obj = identifier(&x);
        let distance = self.multivariable_distance(x_obj.clone(), point.clone(), n.clone());
        let lower = less(self, number(0), distance.clone());
        let upper = less(self, distance, identifier(&delta));
        let near = build_set(x, domain.clone(), vec![lower, upper]);
        let y = self.fresh_internal_param();
        let y_obj = identifier(&y);
        let difference = self.multivariable_difference(y_obj.clone(), point.clone(), n.clone());
        let output_dimension = m.clone().unwrap_or(number(1));
        let linear: Obj = Obj::MatrixOperator(MatrixOperator::Apply(MatrixApply {
            matrix: Box::new(matrix),
            vector: Box::new(difference),
            rows: Box::new(output_dimension.clone()),
            cols: Box::new(n.clone()),
        }));
        let at_point = apply(&function, vec![point.clone()]);
        let at_y = apply(&function, vec![y_obj.clone()]);
        let error = match m {
            Some(m) => {
                let r = self.fresh_internal_param();
                let index = identifier(&r);
                let body = sub_objs(
                    sub_objs(
                        apply(&at_y, vec![index.clone()]),
                        apply(&at_point, vec![index.clone()]),
                    ),
                    apply(&linear, vec![index]),
                );
                norm(anonymous(vec![(r, indices(m.clone()))], real(), body), m)
            }
            None => absolute(sub_objs(
                sub_objs(at_y, at_point),
                apply(&linear, vec![number(1)]),
            )),
        };
        let distance = self.multivariable_distance(y_obj, point, n);
        let bound = mul_objs(identifier(&epsilon), distance);
        let within = less(self, error, bound);
        let good = build_set(y, domain, vec![within]);
        let inclusion = subset(self, near, good);
        let radius = exists(self, delta, positive_real(), vec![inclusion]);
        quantified(self, epsilon, positive_real(), vec![], vec![radius])
    }
    fn multivariable_diagonal_sum_definition(
        &mut self,
        function: Obj,
        domain: Obj,
        point: Obj,
        n: Obj,
        target: Obj,
        second: bool,
    ) -> Fact {
        let values = self.fresh_internal_param();
        let v = identifier(&values);
        let k = self.fresh_internal_param();
        let index = identifier(&k);
        let entry = apply(&v, vec![index.clone()]);
        let candidate = if second {
            relation_from_args(
                self,
                "has_second_partial_derivative_at",
                vec![
                    function,
                    point,
                    n.clone(),
                    index.clone(),
                    index.clone(),
                    entry,
                ],
            )
        } else {
            let component = self.multivariable_component_function(function, domain, index.clone());
            relation_from_args(
                self,
                "has_partial_derivative_at",
                vec![component, point, n.clone(), index.clone(), entry],
            )
        };
        let good = build_set(k, indices(n.clone()), vec![candidate]);
        let all = subset(self, indices(n.clone()), good);
        let sum = self.multivariable_finite_sum(n.clone(), v);
        let equation = equal(self, sum, target);
        exists(self, values, vector(n), vec![all, equation])
    }
}
fn fact_to_guard(fact: Fact) -> QuantifierFreeFact {
    let Fact::AtomicFact(atom) = fact else {
        unreachable!("atomic guard")
    };
    QuantifierFreeFact::AtomicFact(atom)
}

pub enum MultivariableDefinitionProof {
    ScalarLimit(ScalarMultivariableLimitRelationDefinitionProof),
    VectorLimit(VectorMultivariableLimitRelationDefinitionProof),
    ScalarContinuousAt(ScalarMultivariableContinuousAtRelationDefinitionProof),
    VectorContinuousAt(VectorMultivariableContinuousAtRelationDefinitionProof),
    PartialDerivativeAt(PartialDerivativeAtRelationDefinitionProof),
    SecondPartialDerivativeAt(SecondPartialDerivativeAtRelationDefinitionProof),
    ScalarDifferentialAt(ScalarDifferentialAtRelationDefinitionProof),
    TotalDerivativeAt(TotalDerivativeAtRelationDefinitionProof),
    ScalarDifferentiableAt(ScalarMultivariableDifferentiableAtRelationDefinitionProof),
    TotalDifferentiableAt(VectorMultivariableDifferentiableAtRelationDefinitionProof),
    GradientAt(GradientAtRelationDefinitionProof),
    JacobianAt(JacobianAtRelationDefinitionProof),
    HessianAt(HessianAtRelationDefinitionProof),
    DivergenceAt(DivergenceAtRelationDefinitionProof),
    CurlAt(CurlAtRelationDefinitionProof),
    LaplacianAt(LaplacianAtRelationDefinitionProof),
}
pub struct ScalarMultivariableLimitRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct VectorMultivariableLimitRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct ScalarMultivariableContinuousAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct VectorMultivariableContinuousAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct PartialDerivativeAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct SecondPartialDerivativeAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct ScalarDifferentialAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct TotalDerivativeAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct ScalarMultivariableDifferentiableAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct VectorMultivariableDifferentiableAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct GradientAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct JacobianAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct HessianAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct DivergenceAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct CurlAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub struct LaplacianAtRelationDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
pub(crate) fn definition_proof(
    relation: &MultivariableAnalysisRelation,
    requirement_facts: Vec<Fact>,
    proof_of_requirement_facts: Vec<VerifyFactResult>,
) -> MultivariableDefinitionProof {
    match relation {
        MultivariableAnalysisRelation::ScalarLimit(_) => MultivariableDefinitionProof::ScalarLimit(
            ScalarMultivariableLimitRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        ),
        MultivariableAnalysisRelation::VectorLimit(_) => MultivariableDefinitionProof::VectorLimit(
            VectorMultivariableLimitRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        ),
        MultivariableAnalysisRelation::ScalarContinuousAt(_) => {
            MultivariableDefinitionProof::ScalarContinuousAt(
                ScalarMultivariableContinuousAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::VectorContinuousAt(_) => {
            MultivariableDefinitionProof::VectorContinuousAt(
                VectorMultivariableContinuousAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::PartialDerivativeAt(_) => {
            MultivariableDefinitionProof::PartialDerivativeAt(
                PartialDerivativeAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::SecondPartialDerivativeAt(_) => {
            MultivariableDefinitionProof::SecondPartialDerivativeAt(
                SecondPartialDerivativeAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::ScalarDifferentialAt(_) => {
            MultivariableDefinitionProof::ScalarDifferentialAt(
                ScalarDifferentialAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::TotalDerivativeAt(_) => {
            MultivariableDefinitionProof::TotalDerivativeAt(
                TotalDerivativeAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::ScalarDifferentiableAt(_) => {
            MultivariableDefinitionProof::ScalarDifferentiableAt(
                ScalarMultivariableDifferentiableAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::TotalDifferentiableAt(_) => {
            MultivariableDefinitionProof::TotalDifferentiableAt(
                VectorMultivariableDifferentiableAtRelationDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            )
        }
        MultivariableAnalysisRelation::GradientAt(_) => {
            MultivariableDefinitionProof::GradientAt(GradientAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
        MultivariableAnalysisRelation::JacobianAt(_) => {
            MultivariableDefinitionProof::JacobianAt(JacobianAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
        MultivariableAnalysisRelation::HessianAt(_) => {
            MultivariableDefinitionProof::HessianAt(HessianAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
        MultivariableAnalysisRelation::DivergenceAt(_) => {
            MultivariableDefinitionProof::DivergenceAt(DivergenceAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
        MultivariableAnalysisRelation::CurlAt(_) => {
            MultivariableDefinitionProof::CurlAt(CurlAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
        MultivariableAnalysisRelation::LaplacianAt(_) => {
            MultivariableDefinitionProof::LaplacianAt(LaplacianAtRelationDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            })
        }
    }
}
impl MultivariableDefinitionProof {
    pub fn requirements(&self) -> (&Vec<Fact>, &Vec<VerifyFactResult>) {
        match self {
            Self::ScalarLimit(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::VectorLimit(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::ScalarContinuousAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::VectorContinuousAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::PartialDerivativeAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::SecondPartialDerivativeAt(p) => {
                (&p.requirement_facts, &p.proof_of_requirement_facts)
            }
            Self::ScalarDifferentialAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::TotalDerivativeAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::ScalarDifferentiableAt(p) => {
                (&p.requirement_facts, &p.proof_of_requirement_facts)
            }
            Self::TotalDifferentiableAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::GradientAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::JacobianAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::HessianAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::DivergenceAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::CurlAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
            Self::LaplacianAt(p) => (&p.requirement_facts, &p.proof_of_requirement_facts),
        }
    }
}
