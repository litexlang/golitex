use super::super::matrix_operations::{anonymous, finite_sum};
use super::super::native_matrix::{matrix_call, matrix_number, matrix_space};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, mul_objs, sub_objs};

pub(crate) fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
pub(crate) fn positive_real() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
pub(crate) fn positive_natural() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
pub(crate) fn number(value: i64) -> Obj {
    matrix_number(value)
}
pub(crate) fn identifier(name: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(name))
}
pub(crate) fn vector(dimension: Obj) -> Obj {
    Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(real()),
        n: Box::new(dimension),
    }))
}
pub(crate) fn indices(dimension: Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(number(1)),
        end: Box::new(dimension),
    }))
}
pub(crate) fn apply(function: &Obj, args: Vec<Obj>) -> Obj {
    matrix_call(function, args)
}
pub(crate) fn norm(value: Obj, dimension: Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::EuclideanNorm(EuclideanNorm {
        vector: Box::new(value),
        dimension: Box::new(dimension),
    }))
}
pub(crate) fn absolute(value: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(value),
    }))
}
pub(crate) fn negate(value: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
        arg: Box::new(value),
    }))
}
pub(crate) fn member(rt: &mut Runtime, element: Obj, set: Obj) -> Fact {
    InFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        element,
        set,
        line_file: None,
    }
    .into()
}
pub(crate) fn subset(rt: &mut Runtime, left: Obj, right: Obj) -> Fact {
    SubsetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn equal(rt: &mut Runtime, left: Obj, right: Obj) -> Fact {
    EqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn less(rt: &mut Runtime, left: Obj, right: Obj) -> Fact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn nonzero(rt: &mut Runtime, value: Obj) -> Fact {
    NotEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left: value,
        right: number(0),
        line_file: None,
    }
    .into()
}
pub(crate) fn quantified(
    rt: &mut Runtime,
    param: BoundName,
    set: Obj,
    dom_facts: Vec<Fact>,
    then_facts: Vec<Fact>,
) -> Fact {
    let group = TypedParameterGroup {
        params: vec![param],
        param_type: ParamType::Obj(set),
    };
    if then_facts.len() == 1 {
        if let Fact::ForallFact(inner) = &then_facts[0] {
            let mut inner = inner.clone();
            inner.fact_id = rt.global_ids.allocate_fact_id();
            inner.typed_parameters.groups.insert(0, group);
            let mut domains = dom_facts;
            domains.extend(inner.dom_facts);
            inner.dom_facts = domains;
            return Fact::ForallFact(inner);
        }
    }
    let then_facts = then_facts
        .into_iter()
        .map(|f| match f {
            Fact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            Fact::ExistFact(e) => ExistOrAndChainAtomicFact::ExistFact(e),
            _ => unreachable!("nested universal flattened before construction"),
        })
        .collect();
    Fact::ForallFact(ForallFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![group],
        },
        dom_facts,
        then_facts,
        line_file: None,
    })
}
pub(crate) fn exists(rt: &mut Runtime, param: BoundName, set: Obj, body: Vec<Fact>) -> Fact {
    let facts = body
        .into_iter()
        .map(|f| match f {
            Fact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
            Fact::AndFact(a) => QuantifierFreeFact::AndFact(a),
            _ => unreachable!("existential guards are quantifier-free"),
        })
        .collect();
    Fact::ExistFact(PlainExistFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![param],
                param_type: ParamType::Obj(set),
            }],
        },
        facts,
        line_file: None,
    })
}
pub(crate) fn build_set(param: BoundName, set: Obj, facts: Vec<Fact>) -> Obj {
    Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
        param_binding: param,
        param_set: Box::new(set),
        facts: facts
            .into_iter()
            .map(|f| {
                let Fact::AtomicFact(atom) = f else {
                    unreachable!("Euclidean set guards are atomic")
                };
                QuantifierFreeFact::AtomicFact(atom)
            })
            .collect(),
    }))
}
pub(crate) fn actual_domain(signature: &FnSet) -> Option<Obj> {
    let params: Vec<_> = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect();
    if params.len() != 1 {
        return None;
    }
    Some(if signature.dom_facts.is_empty() {
        params[0].1.clone()
    } else {
        Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: params[0].0.clone(),
            param_set: Box::new(params[0].1.clone()),
            facts: signature.dom_facts.clone(),
        }))
    })
}
pub(crate) fn input_dimension(relation: &MultivariableAnalysisRelation) -> Obj {
    match relation {
        MultivariableAnalysisRelation::CurlAt(_) => number(3),
        _ => relation.argument_refs()[2].clone(),
    }
}
pub(crate) fn function_output_dimension(relation: &MultivariableAnalysisRelation) -> Option<Obj> {
    use MultivariableAnalysisRelation::*;
    match relation {
        VectorLimit(_)
        | VectorContinuousAt(_)
        | TotalDerivativeAt(_)
        | TotalDifferentiableAt(_)
        | JacobianAt(_) => Some(relation.argument_refs()[3].clone()),
        DivergenceAt(x) => Some(x.dimension.clone()),
        CurlAt(_) => Some(number(3)),
        ScalarLimit(_)
        | ScalarContinuousAt(_)
        | PartialDerivativeAt(_)
        | SecondPartialDerivativeAt(_)
        | ScalarDifferentialAt(_)
        | ScalarDifferentiableAt(_)
        | GradientAt(_)
        | HessianAt(_)
        | LaplacianAt(_) => None,
    }
}
pub(crate) fn value(relation: &MultivariableAnalysisRelation) -> Option<&Obj> {
    use MultivariableAnalysisRelation::*;
    match relation {
        ScalarContinuousAt(_)
        | VectorContinuousAt(_)
        | ScalarDifferentiableAt(_)
        | TotalDifferentiableAt(_) => None,
        _ => relation.argument_refs().last().copied(),
    }
}
pub(crate) fn value_carrier(relation: &MultivariableAnalysisRelation) -> Obj {
    use MultivariableAnalysisRelation::*;
    let n = input_dimension(relation);
    match relation {
        VectorLimit(x) => vector(x.output_dimension.clone()),
        GradientAt(_) => vector(n),
        CurlAt(_) => vector(number(3)),
        ScalarDifferentialAt(_) => matrix_space(real(), number(1), n.clone()),
        TotalDerivativeAt(x) => matrix_space(real(), x.output_dimension.clone(), n),
        JacobianAt(x) => matrix_space(real(), x.output_dimension.clone(), n),
        HessianAt(_) => matrix_space(real(), n.clone(), n),
        ScalarLimit(_)
        | ScalarContinuousAt(_)
        | VectorContinuousAt(_)
        | PartialDerivativeAt(_)
        | SecondPartialDerivativeAt(_)
        | ScalarDifferentiableAt(_)
        | TotalDifferentiableAt(_)
        | DivergenceAt(_)
        | LaplacianAt(_) => real(),
    }
}
pub(crate) fn selector_relation(
    obj: &Obj,
    candidate: Obj,
) -> Option<MultivariableAnalysisRelation> {
    let name = match obj.multivariable_selector_name()? {
        "lim_multi_at" => "has_multi_limit_at",
        "lim_vector_at" => "has_vector_limit_at",
        "partial_derivative" => "has_partial_derivative_at",
        "scalar_differential" => "has_scalar_differential_at",
        "differential" => "has_total_derivative_at",
        "gradient_at" => "has_gradient_at",
        "jacobian" => "has_jacobian_at",
        "hessian" => "has_hessian_at",
        "divergence" => "has_divergence_at",
        "curl" => "has_curl_at",
        "laplacian" => "has_laplacian_at",
        _ => unreachable!("closed selector name table"),
    };
    let mut args: Vec<_> = obj
        .multivariable_selector_args()?
        .into_iter()
        .cloned()
        .collect();
    args.push(candidate);
    MultivariableAnalysisRelation::from_name(name, &args)
}
pub(crate) fn relation_fact(rt: &mut Runtime, relation: MultivariableAnalysisRelation) -> Fact {
    MultivariableAnalysisFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        relation,
        line_file: None,
    }
    .into()
}
pub(crate) fn relation_from_args(rt: &mut Runtime, name: &str, args: Vec<Obj>) -> Fact {
    relation_fact(
        rt,
        MultivariableAnalysisRelation::from_name(name, &args)
            .expect("fixed multivariable predicate arity"),
    )
}
pub(crate) fn is_limit(relation: &MultivariableAnalysisRelation) -> bool {
    matches!(
        relation,
        MultivariableAnalysisRelation::ScalarLimit(_)
            | MultivariableAnalysisRelation::VectorLimit(_)
    )
}
impl Runtime {
    pub(crate) fn multivariable_difference(&mut self, left: Obj, right: Obj, n: Obj) -> Obj {
        let k = self.fresh_internal_param();
        let index = identifier(&k);
        anonymous(
            vec![(k, indices(n))],
            real(),
            sub_objs(
                apply(&left, vec![index.clone()]),
                apply(&right, vec![index]),
            ),
        )
    }
    pub(crate) fn multivariable_distance(&mut self, left: Obj, right: Obj, n: Obj) -> Obj {
        let difference = self.multivariable_difference(left, right, n.clone());
        norm(difference, n)
    }
    pub(crate) fn multivariable_coordinate_path(
        &mut self,
        p: Obj,
        n: Obj,
        axis: Obj,
        displacement: Obj,
    ) -> Obj {
        let k = self.fresh_internal_param();
        let index = identifier(&k);
        let basis = apply(
            &Obj::MatrixOperator(MatrixOperator::IdentityMatrix(IdentityMatrix {
                order: Box::new(n.clone()),
            })),
            vec![index.clone(), axis],
        );
        anonymous(
            vec![(k, indices(n))],
            real(),
            add_objs(apply(&p, vec![index]), mul_objs(displacement, basis)),
        )
    }
    pub(crate) fn multivariable_component_function(
        &mut self,
        function: Obj,
        domain: Obj,
        component: Obj,
    ) -> Obj {
        let x = self.fresh_internal_param();
        let input = identifier(&x);
        anonymous(
            vec![(x, domain)],
            real(),
            apply(&apply(&function, vec![input]), vec![component]),
        )
    }
    pub(crate) fn multivariable_finite_sum(&mut self, n: Obj, function: Obj) -> Obj {
        finite_sum(indices(n), function)
    }
}

pub(crate) fn exists_many(
    rt: &mut Runtime,
    parameters: Vec<(BoundName, Obj)>,
    body: Vec<Fact>,
) -> Fact {
    let groups = parameters
        .into_iter()
        .map(|(param, set)| TypedParameterGroup {
            params: vec![param],
            param_type: ParamType::Obj(set),
        })
        .collect();
    let facts = body
        .into_iter()
        .map(|f| match f {
            Fact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
            _ => unreachable!("existential guards are atomic"),
        })
        .collect();
    Fact::ExistFact(PlainExistFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList { groups },
        facts,
        line_file: None,
    })
}
pub(crate) fn function_space(param: BoundName, domain: Obj, ret: Obj) -> Obj {
    Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
        set_bound_parameters: SetBoundParameterList {
            groups: vec![SetBoundParameterGroup {
                params: vec![param],
                param_type: Box::new(domain),
            }],
        },
        dom_facts: vec![],
        ret_set: Box::new(ret),
    }))
}

pub(crate) const CANDIDATE_NAMES: &[&str] = &[
    "has_multi_limit_at",
    "has_vector_limit_at",
    "has_partial_derivative_at",
    "has_second_partial_derivative_at",
    "has_scalar_differential_at",
    "has_total_derivative_at",
    "has_gradient_at",
    "has_jacobian_at",
    "has_hessian_at",
    "has_divergence_at",
    "has_curl_at",
    "has_laplacian_at",
];
