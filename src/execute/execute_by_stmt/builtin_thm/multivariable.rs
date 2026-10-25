//! Explicit Euclidean calculus theorems. Constructing a schema proves nothing.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainProof,
};
use crate::execute::execute_fact_stmt::matrix_operations::anonymous;
use crate::execute::execute_fact_stmt::multivariable::helper::*;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};

fn relation(name: &str, args: &[Obj]) -> MultivariableAnalysisRelation {
    MultivariableAnalysisRelation::from_name(name, args).expect("fixed Euclidean theorem schema")
}
fn schema(id: BuiltinTheoremId) -> Option<(&'static str, &'static str, Option<&'static str>)> {
    use BuiltinTheoremId::*;
    Some(match id {
        MultiLimitAtFromDefinition => {
            ("has_multi_limit_at", "FromDefinition", Some("lim_multi_at"))
        }
        MultiLimitAtToDefinition => ("has_multi_limit_at", "ToDefinition", Some("lim_multi_at")),
        MultiLimitAtUnique => ("has_multi_limit_at", "Unique", Some("lim_multi_at")),
        MultiLimitAtExists => ("has_multi_limit_at", "Exists", Some("lim_multi_at")),
        MultiLimitAtSelected => ("has_multi_limit_at", "Selected", Some("lim_multi_at")),
        VectorLimitAtFromDefinition => (
            "has_vector_limit_at",
            "FromDefinition",
            Some("lim_vector_at"),
        ),
        VectorLimitAtToDefinition => ("has_vector_limit_at", "ToDefinition", Some("lim_vector_at")),
        VectorLimitAtUnique => ("has_vector_limit_at", "Unique", Some("lim_vector_at")),
        VectorLimitAtExists => ("has_vector_limit_at", "Exists", Some("lim_vector_at")),
        VectorLimitAtSelected => ("has_vector_limit_at", "Selected", Some("lim_vector_at")),
        PartialAtFromDefinition => (
            "has_partial_derivative_at",
            "FromDefinition",
            Some("partial_derivative"),
        ),
        PartialAtToDefinition => (
            "has_partial_derivative_at",
            "ToDefinition",
            Some("partial_derivative"),
        ),
        PartialAtUnique => (
            "has_partial_derivative_at",
            "Unique",
            Some("partial_derivative"),
        ),
        PartialAtExists => (
            "has_partial_derivative_at",
            "Exists",
            Some("partial_derivative"),
        ),
        PartialAtSelected => (
            "has_partial_derivative_at",
            "Selected",
            Some("partial_derivative"),
        ),
        SecondPartialAtFromDefinition => {
            ("has_second_partial_derivative_at", "FromDefinition", None)
        }
        SecondPartialAtToDefinition => ("has_second_partial_derivative_at", "ToDefinition", None),
        SecondPartialAtUnique => ("has_second_partial_derivative_at", "Unique", None),
        SecondPartialAtExists => ("has_second_partial_derivative_at", "Exists", None),
        ScalarDifferentialAtFromDefinition => (
            "has_scalar_differential_at",
            "FromDefinition",
            Some("scalar_differential"),
        ),
        ScalarDifferentialAtToDefinition => (
            "has_scalar_differential_at",
            "ToDefinition",
            Some("scalar_differential"),
        ),
        ScalarDifferentialAtUnique => (
            "has_scalar_differential_at",
            "Unique",
            Some("scalar_differential"),
        ),
        ScalarDifferentialAtExists => (
            "has_scalar_differential_at",
            "Exists",
            Some("scalar_differential"),
        ),
        ScalarDifferentialAtSelected => (
            "has_scalar_differential_at",
            "Selected",
            Some("scalar_differential"),
        ),
        TotalDerivativeAtFromDefinition => (
            "has_total_derivative_at",
            "FromDefinition",
            Some("differential"),
        ),
        TotalDerivativeAtToDefinition => (
            "has_total_derivative_at",
            "ToDefinition",
            Some("differential"),
        ),
        TotalDerivativeAtUnique => ("has_total_derivative_at", "Unique", Some("differential")),
        TotalDerivativeAtExists => ("has_total_derivative_at", "Exists", Some("differential")),
        TotalDerivativeAtSelected => ("has_total_derivative_at", "Selected", Some("differential")),
        GradientAtFromDefinition => ("has_gradient_at", "FromDefinition", Some("gradient_at")),
        GradientAtToDefinition => ("has_gradient_at", "ToDefinition", Some("gradient_at")),
        GradientAtUnique => ("has_gradient_at", "Unique", Some("gradient_at")),
        GradientAtExists => ("has_gradient_at", "Exists", Some("gradient_at")),
        GradientAtSelected => ("has_gradient_at", "Selected", Some("gradient_at")),
        JacobianAtFromDefinition => ("has_jacobian_at", "FromDefinition", Some("jacobian")),
        JacobianAtToDefinition => ("has_jacobian_at", "ToDefinition", Some("jacobian")),
        JacobianAtUnique => ("has_jacobian_at", "Unique", Some("jacobian")),
        JacobianAtExists => ("has_jacobian_at", "Exists", Some("jacobian")),
        JacobianAtSelected => ("has_jacobian_at", "Selected", Some("jacobian")),
        HessianAtFromDefinition => ("has_hessian_at", "FromDefinition", Some("hessian")),
        HessianAtToDefinition => ("has_hessian_at", "ToDefinition", Some("hessian")),
        HessianAtUnique => ("has_hessian_at", "Unique", Some("hessian")),
        HessianAtExists => ("has_hessian_at", "Exists", Some("hessian")),
        HessianAtSelected => ("has_hessian_at", "Selected", Some("hessian")),
        DivergenceAtFromDefinition => ("has_divergence_at", "FromDefinition", Some("divergence")),
        DivergenceAtToDefinition => ("has_divergence_at", "ToDefinition", Some("divergence")),
        DivergenceAtUnique => ("has_divergence_at", "Unique", Some("divergence")),
        DivergenceAtExists => ("has_divergence_at", "Exists", Some("divergence")),
        DivergenceAtSelected => ("has_divergence_at", "Selected", Some("divergence")),
        CurlAtFromDefinition => ("has_curl_at", "FromDefinition", Some("curl")),
        CurlAtToDefinition => ("has_curl_at", "ToDefinition", Some("curl")),
        CurlAtUnique => ("has_curl_at", "Unique", Some("curl")),
        CurlAtExists => ("has_curl_at", "Exists", Some("curl")),
        CurlAtSelected => ("has_curl_at", "Selected", Some("curl")),
        LaplacianAtFromDefinition => ("has_laplacian_at", "FromDefinition", Some("laplacian")),
        LaplacianAtToDefinition => ("has_laplacian_at", "ToDefinition", Some("laplacian")),
        LaplacianAtUnique => ("has_laplacian_at", "Unique", Some("laplacian")),
        LaplacianAtExists => ("has_laplacian_at", "Exists", Some("laplacian")),
        LaplacianAtSelected => ("has_laplacian_at", "Selected", Some("laplacian")),
        MultiContinuousAtFromDefinition => ("is_multi_continuous_at", "FromDefinition", None),
        MultiContinuousAtToDefinition => ("is_multi_continuous_at", "ToDefinition", None),
        VectorContinuousAtFromDefinition => ("is_vector_continuous_at", "FromDefinition", None),
        VectorContinuousAtToDefinition => ("is_vector_continuous_at", "ToDefinition", None),
        MultiDifferentiableAtFromDefinition => {
            ("is_multi_differentiable_at", "FromDefinition", None)
        }
        MultiDifferentiableAtToDefinition => ("is_multi_differentiable_at", "ToDefinition", None),
        VectorDifferentiableAtFromDefinition => {
            ("is_vector_differentiable_at", "FromDefinition", None)
        }
        VectorDifferentiableAtToDefinition => ("is_vector_differentiable_at", "ToDefinition", None),
        _ => return None,
    })
}
fn context(
    rt: &mut Runtime,
    r: &MultivariableAnalysisRelation,
) -> RuntimeResult<Option<(CompleteFunctionDomainProof, Vec<Fact>)>> {
    rt.multivariable_signature_requirements(r, VerifyState::new(VerifyStateLevel::BuiltinRule))
}
fn same_domain(
    rt: &mut Runtime,
    req: &mut Vec<Fact>,
    source: &CompleteFunctionDomainProof,
    other: &Obj,
    prototype: &MultivariableAnalysisRelation,
) -> RuntimeResult<bool> {
    let mut args: Vec<_> = prototype.argument_refs().into_iter().cloned().collect();
    args[0] = other.clone();
    let Some((other, more)) = context(rt, &prototype.with_arguments(&args))? else {
        return Ok(false);
    };
    if !function_domains_alpha_equal(&source.signature, &other.signature) {
        return Ok(false);
    }
    req.extend(more);
    Ok(true)
}
fn function_equation(
    rt: &mut Runtime,
    output: &Obj,
    domain: Obj,
    body: Obj,
    parameter: BoundName,
) -> Fact {
    let equation = equal(rt, apply(output, vec![identifier(&parameter)]), body);
    quantified(rt, parameter, domain, vec![], vec![equation])
}
fn matrix_entries(
    rt: &mut Runtime,
    rows: Obj,
    cols: Obj,
    a: &Obj,
    b: &Obj,
    op: &str,
    fa: Obj,
    fb: Obj,
) -> Obj {
    let r = rt.fresh_internal_param();
    let c = rt.fresh_internal_param();
    let ij = vec![identifier(&r), identifier(&c)];
    let da = apply(a, ij.clone());
    let db = apply(b, ij);
    let body = match op {
        "Add" => add_objs(da, db),
        "Subtract" => sub_objs(da, db),
        "Multiply" => add_objs(mul_objs(da, fb), mul_objs(fa, db)),
        "Divide" => div_objs(
            div_objs(
                sub_objs(mul_objs(da, fb.clone()), mul_objs(fa, db)),
                fb.clone(),
            ),
            fb,
        ),
        _ => unreachable!(),
    };
    anonymous(vec![(r, indices(rows)), (c, indices(cols))], real(), body)
}
fn vector_entries(rt: &mut Runtime, n: Obj, a: &Obj, b: &Obj, subtract: bool) -> Obj {
    let k = rt.fresh_internal_param();
    let i = identifier(&k);
    let a = apply(a, vec![i.clone()]);
    let b = apply(b, vec![i]);
    anonymous(
        vec![(k, indices(n))],
        real(),
        if subtract {
            sub_objs(a, b)
        } else {
            add_objs(a, b)
        },
    )
}

pub(super) fn prepare(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    if matches!(
        id,
        MultiContinuousAtCompose
            | VectorContinuousAtCompose
            | MultiLimitAtCompose
            | VectorLimitAtCompose
    ) {
        return continuous_composition(rt, id, args);
    }
    if matches!(
        id,
        SecondPartialAtToFunction | CurlGradientAtSymmetric | DivergenceCurlAtSymmetric
    ) {
        return vector_identity(rt, id, args);
    }
    if let Some((name, action, selector)) = schema(id) {
        let mut candidate_args = args.to_vec();
        if action == "Unique" {
            candidate_args.pop();
        }
        if action == "Selected" {
            candidate_args.push(number(0));
        }
        let r = relation(name, &candidate_args);
        let Some((_, mut req)) = context(rt, &r)? else {
            return Ok(Err(
                "requires a complete real Euclidean function and exact declared dimensions".into(),
            ));
        };
        let candidate = relation_fact(rt, r.clone());
        let output = match action {
            "FromDefinition" => {
                req.extend(
                    rt.multivariable_defining_clauses(
                        &r,
                        VerifyState::new(VerifyStateLevel::BuiltinRule),
                    )?
                    .unwrap(),
                );
                vec![candidate]
            }
            "ToDefinition" => {
                req.push(candidate);
                rt.multivariable_defining_clauses(
                    &r,
                    VerifyState::new(VerifyStateLevel::BuiltinRule),
                )?
                .unwrap()
            }
            "Unique" => {
                req.push(candidate);
                let mut other = candidate_args.clone();
                *other.last_mut().unwrap() = args.last().unwrap().clone();
                req.push(relation_from_args(rt, name, other));
                vec![equal(
                    rt,
                    candidate_args.last().unwrap().clone(),
                    args.last().unwrap().clone(),
                )]
            }
            "Exists" => {
                req.push(candidate);
                vec![rt.multivariable_candidate_existence(&r)]
            }
            "Selected" => {
                req.push(rt.multivariable_candidate_existence(&r));
                let selected = Obj::from_multivariable_selector(selector.unwrap(), args)
                    .expect("fixed selector signature");
                *candidate_args.last_mut().unwrap() = selected;
                vec![relation_from_args(rt, name, candidate_args)]
            }
            _ => unreachable!(),
        };
        return Ok(Ok((req, output)));
    }
    match id {
        MultiLimitAtAdd => return scalar_algebra(rt, args, "has_multi_limit_at", "Add"),
        MultiLimitAtSubtract => return scalar_algebra(rt, args, "has_multi_limit_at", "Subtract"),
        MultiLimitAtMultiply => return scalar_algebra(rt, args, "has_multi_limit_at", "Multiply"),
        MultiLimitAtDivide => return scalar_algebra(rt, args, "has_multi_limit_at", "Divide"),
        MultiContinuousAtAdd => return scalar_algebra(rt, args, "is_multi_continuous_at", "Add"),
        MultiContinuousAtSubtract => {
            return scalar_algebra(rt, args, "is_multi_continuous_at", "Subtract")
        }
        MultiContinuousAtMultiply => {
            return scalar_algebra(rt, args, "is_multi_continuous_at", "Multiply")
        }
        MultiContinuousAtDivide => {
            return scalar_algebra(rt, args, "is_multi_continuous_at", "Divide")
        }
        PartialAtAdd => return scalar_algebra(rt, args, "has_partial_derivative_at", "Add"),
        PartialAtSubtract => {
            return scalar_algebra(rt, args, "has_partial_derivative_at", "Subtract")
        }
        PartialAtMultiply => {
            return scalar_algebra(rt, args, "has_partial_derivative_at", "Multiply")
        }
        PartialAtDivide => return scalar_algebra(rt, args, "has_partial_derivative_at", "Divide"),
        ScalarDifferentialAtAdd => {
            return scalar_algebra(rt, args, "has_scalar_differential_at", "Add")
        }
        ScalarDifferentialAtSubtract => {
            return scalar_algebra(rt, args, "has_scalar_differential_at", "Subtract")
        }
        ScalarDifferentialAtMultiply => {
            return scalar_algebra(rt, args, "has_scalar_differential_at", "Multiply")
        }
        ScalarDifferentialAtDivide => {
            return scalar_algebra(rt, args, "has_scalar_differential_at", "Divide")
        }
        VectorLimitAtAdd
        | VectorLimitAtSubtract
        | TotalDerivativeAtAdd
        | TotalDerivativeAtSubtract
        | VectorContinuousAtAdd
        | VectorContinuousAtSubtract => return vector_algebra(rt, id, args),
        TotalDerivativeAtCompose | ScalarDifferentialAtCompose => return composition(rt, id, args),
        SecondPartialAtFromFunction | SecondPartialAtSwapContinuous => {
            return second_partial(rt, id, args)
        }
        _ => {}
    }
    let f = args[0].clone();
    let p = args[1].clone();
    let n = if id == JacobianAtCurl {
        number(3)
    } else {
        args[2].clone()
    };
    let (source_name, source_args) = match id {
        ScalarDifferentialAtContinuous
        | ScalarDifferentialAtGradient
        | ScalarDifferentialAtPartial => ("has_scalar_differential_at", args[..4].to_vec()),
        TotalDerivativeAtContinuous | TotalDerivativeAtJacobian => {
            ("has_total_derivative_at", args.to_vec())
        }
        JacobianAtDivergence => (
            "has_jacobian_at",
            vec![f.clone(), p.clone(), n.clone(), n.clone(), args[3].clone()],
        ),
        JacobianAtCurl => (
            "has_jacobian_at",
            vec![f.clone(), p.clone(), number(3), number(3), args[2].clone()],
        ),
        HessianAtLaplacian => ("has_hessian_at", args.to_vec()),
        MultiContinuousAtLimit => ("is_multi_continuous_at", args.to_vec()),
        MultiLimitAtContinuous => ("has_multi_limit_at", args.to_vec()),
        VectorContinuousAtLimit => ("is_vector_continuous_at", args.to_vec()),
        VectorLimitAtContinuous => ("has_vector_limit_at", args.to_vec()),
        _ => unreachable!("closed Euclidean bridge table"),
    };
    let r = relation(source_name, &source_args);
    let Some((source, mut req)) = context(rt, &r)? else {
        return Ok(Err(
            "requires an unambiguous real Euclidean function domain".into(),
        ));
    };
    req.push(relation_fact(rt, r.clone()));
    let result = match id {
        ScalarDifferentialAtContinuous => {
            relation_from_args(rt, "is_multi_continuous_at", vec![f, p, n])
        }
        TotalDerivativeAtContinuous => relation_from_args(
            rt,
            "is_vector_continuous_at",
            vec![f, p, n, args[3].clone()],
        ),
        ScalarDifferentialAtGradient => {
            let k = rt.fresh_internal_param();
            let row = apply(&args[3], vec![number(1), identifier(&k)]);
            let gradient = anonymous(vec![(k, indices(n.clone()))], real(), row);
            relation_from_args(rt, "has_gradient_at", vec![f, p, n, gradient])
        }
        ScalarDifferentialAtPartial => {
            let axis = args[4].clone();
            relation_from_args(
                rt,
                "has_partial_derivative_at",
                vec![
                    f,
                    p,
                    n,
                    axis.clone(),
                    apply(&args[3], vec![number(1), axis]),
                ],
            )
        }
        TotalDerivativeAtJacobian => relation_from_args(rt, "has_jacobian_at", args.to_vec()),
        JacobianAtDivergence => {
            let trace = Obj::MatrixOperator(MatrixOperator::Trace(MatrixTrace {
                matrix: Box::new(args[3].clone()),
                order: Box::new(n.clone()),
            }));
            relation_from_args(rt, "has_divergence_at", vec![f, p, n, trace])
        }
        HessianAtLaplacian => {
            let trace = Obj::MatrixOperator(MatrixOperator::Trace(MatrixTrace {
                matrix: Box::new(args[3].clone()),
                order: Box::new(n.clone()),
            }));
            relation_from_args(rt, "has_laplacian_at", vec![f, p, n, trace])
        }
        JacobianAtCurl => {
            let j = &args[2];
            let v = Obj::ProductShape(ProductShape::Tuple(Tuple {
                args: vec![
                    sub_objs(
                        apply(j, vec![number(3), number(2)]),
                        apply(j, vec![number(2), number(3)]),
                    ),
                    sub_objs(
                        apply(j, vec![number(1), number(3)]),
                        apply(j, vec![number(3), number(1)]),
                    ),
                    sub_objs(
                        apply(j, vec![number(2), number(1)]),
                        apply(j, vec![number(1), number(2)]),
                    ),
                ]
                .into_iter()
                .map(Box::new)
                .collect(),
            }));
            relation_from_args(rt, "has_curl_at", vec![f, p, v])
        }
        MultiContinuousAtLimit | VectorContinuousAtLimit => {
            let domain = actual_domain(&source.signature).unwrap();
            req.push(rt.multivariable_accumulation(domain, p.clone(), n.clone()));
            let mut args = args.to_vec();
            args.push(apply(&f, vec![p]));
            relation_from_args(
                rt,
                if id == MultiContinuousAtLimit {
                    "has_multi_limit_at"
                } else {
                    "has_vector_limit_at"
                },
                args,
            )
        }
        MultiLimitAtContinuous | VectorLimitAtContinuous => {
            let domain = actual_domain(&source.signature).unwrap();
            req.push(member(rt, p.clone(), domain));
            req.push(equal(
                rt,
                apply(&f, vec![p.clone()]),
                args.last().unwrap().clone(),
            ));
            let mut result = args.to_vec();
            result.pop();
            relation_from_args(
                rt,
                if id == MultiLimitAtContinuous {
                    "is_multi_continuous_at"
                } else {
                    "is_vector_continuous_at"
                },
                result,
            )
        }
        _ => unreachable!(),
    };
    Ok(Ok((req, vec![result])))
}
fn scalar_algebra(
    rt: &mut Runtime,
    args: &[Obj],
    name: &str,
    op: &str,
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    let f = args[0].clone();
    let g = args[1].clone();
    let h = args[2].clone();
    let p = args[3].clone();
    let n = args[4].clone();
    let continuous = name == "is_multi_continuous_at";
    let partial = name == "has_partial_derivative_at";
    let differential = name == "has_scalar_differential_at";
    let mut first = vec![f.clone(), p.clone(), n.clone()];
    if partial {
        first.push(args[5].clone());
    }
    if !continuous {
        first.push(args[if partial { 6 } else { 5 }].clone());
    }
    let r = relation(name, &first);
    let Some((source, mut req)) = context(rt, &r)? else {
        return Ok(Err("requires a scalar Euclidean function".into()));
    };
    if !same_domain(rt, &mut req, &source, &g, &r)? || !same_domain(rt, &mut req, &source, &h, &r)?
    {
        return Ok(Err(
            "operands and result must have the same complete actual domain".into(),
        ));
    }
    req.push(relation_fact(rt, r.clone()));
    let mut second = first.clone();
    second[0] = g.clone();
    if !continuous {
        *second.last_mut().unwrap() = args.last().unwrap().clone();
    }
    req.push(relation_from_args(rt, name, second));
    let domain = actual_domain(&source.signature).unwrap();
    let x = rt.fresh_internal_param();
    let input = identifier(&x);
    let fx = apply(&f, vec![input.clone()]);
    let gx = apply(&g, vec![input]);
    let operation = |a: Obj, b: Obj| match op {
        "Add" => add_objs(a, b),
        "Subtract" => sub_objs(a, b),
        "Multiply" => mul_objs(a, b),
        "Divide" => div_objs(a, b),
        _ => unreachable!(),
    };
    req.push(function_equation(rt, &h, domain, operation(fx, gx), x));
    let fp = apply(&f, vec![p.clone()]);
    let gp = apply(&g, vec![p.clone()]);
    let limit = name == "has_multi_limit_at";
    if op == "Divide" {
        req.push(nonzero(
            rt,
            if limit { args[6].clone() } else { gp.clone() },
        ));
    }
    let mut result = vec![h, p, n.clone()];
    if partial {
        result.push(args[5].clone());
    }
    if !continuous {
        let a = first.last().unwrap().clone();
        let b = args.last().unwrap().clone();
        let value = if limit {
            operation(a, b)
        } else if differential {
            matrix_entries(rt, number(1), n, &a, &b, op, fp, gp)
        } else {
            match op {
                "Add" => add_objs(a, b),
                "Subtract" => sub_objs(a, b),
                "Multiply" => add_objs(mul_objs(a, gp), mul_objs(fp, b)),
                "Divide" => div_objs(
                    div_objs(
                        sub_objs(mul_objs(a, gp.clone()), mul_objs(fp, b)),
                        gp.clone(),
                    ),
                    gp,
                ),
                _ => unreachable!(),
            }
        };
        result.push(value);
    }
    Ok(Ok((req, vec![relation_from_args(rt, name, result)])))
}
fn vector_algebra(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let continuous = matches!(id, VectorContinuousAtAdd | VectorContinuousAtSubtract);
    let derivative = matches!(id, TotalDerivativeAtAdd | TotalDerivativeAtSubtract);
    let subtract = matches!(
        id,
        VectorLimitAtSubtract | TotalDerivativeAtSubtract | VectorContinuousAtSubtract
    );
    let name = if continuous {
        "is_vector_continuous_at"
    } else if derivative {
        "has_total_derivative_at"
    } else {
        "has_vector_limit_at"
    };
    let (f, g, h, p, n, m) = (&args[0], &args[1], &args[2], &args[3], &args[4], &args[5]);
    let mut first = vec![f.clone(), p.clone(), n.clone(), m.clone()];
    if !continuous {
        first.push(args[6].clone());
    }
    let r = relation(name, &first);
    let Some((source, mut req)) = context(rt, &r)? else {
        return Ok(Err("requires vector Euclidean functions".into()));
    };
    if !same_domain(rt, &mut req, &source, g, &r)? || !same_domain(rt, &mut req, &source, h, &r)? {
        return Ok(Err("requires the same complete actual domain".into()));
    }
    req.push(relation_fact(rt, r.clone()));
    let mut other = first;
    other[0] = g.clone();
    if !continuous {
        *other.last_mut().unwrap() = args[7].clone();
    }
    req.push(relation_from_args(rt, name, other));
    let x = rt.fresh_internal_param();
    let input = identifier(&x);
    let body = vector_entries(
        rt,
        m.clone(),
        &apply(f, vec![input.clone()]),
        &apply(g, vec![input]),
        subtract,
    );
    let domain = actual_domain(&source.signature).unwrap();
    req.push(function_equation(rt, h, domain, body, x));
    let mut result = vec![h.clone(), p.clone(), n.clone(), m.clone()];
    if !continuous {
        result.push(if derivative {
            matrix_entries(
                rt,
                m.clone(),
                n.clone(),
                &args[6],
                &args[7],
                if subtract { "Subtract" } else { "Add" },
                number(0),
                number(0),
            )
        } else {
            vector_entries(rt, m.clone(), &args[6], &args[7], subtract)
        });
    }
    Ok(Ok((req, vec![relation_from_args(rt, name, result)])))
}
fn composition(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let scalar = id == ScalarDifferentialAtCompose;
    let (f, g, h, p, n) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
    let fp = apply(f, vec![p.clone()]);
    let first = if scalar {
        relation(
            "has_scalar_differential_at",
            &[f.clone(), p.clone(), n.clone(), args[5].clone()],
        )
    } else {
        relation(
            "has_total_derivative_at",
            &[
                f.clone(),
                p.clone(),
                n.clone(),
                args[5].clone(),
                args[7].clone(),
            ],
        )
    };
    let Some((source, mut req)) = context(rt, &first)? else {
        return Ok(Err("requires the inner complete Euclidean domain".into()));
    };
    let result_prototype = if scalar {
        first.clone()
    } else {
        relation(
            "has_total_derivative_at",
            &[
                h.clone(),
                p.clone(),
                n.clone(),
                args[6].clone(),
                args[8].clone(),
            ],
        )
    };
    if !same_domain(rt, &mut req, &source, h, &result_prototype)? {
        return Ok(Err(
            "composition result must have the inner actual domain".into()
        ));
    }
    req.push(relation_fact(rt, first));
    let outer_domain = if scalar {
        let Some(outer) = rt.checked_real_function_limit_domain(
            g,
            VerifyState::new(VerifyStateLevel::BuiltinRule),
        )?
        else {
            return Ok(Err("requires a unary real outer function".into()));
        };
        let derivative = rt.derivative_candidate(g.clone(), fp.clone(), args[6].clone());
        req.push(derivative.into());
        outer.domain
    } else {
        let outer = relation(
            "has_total_derivative_at",
            &[
                g.clone(),
                fp.clone(),
                args[5].clone(),
                args[6].clone(),
                args[8].clone(),
            ],
        );
        let Some((domain, more)) = context(rt, &outer)? else {
            return Ok(Err("requires a complete outer Euclidean function".into()));
        };
        req.extend(more);
        req.push(relation_fact(rt, outer));
        actual_domain(&domain.signature).unwrap()
    };
    let domain = actual_domain(&source.signature).unwrap();
    let x = rt.fresh_internal_param();
    let fx = apply(f, vec![identifier(&x)]);
    let image_member = member(rt, fx.clone(), outer_domain);
    req.push(quantified(
        rt,
        x.clone(),
        domain.clone(),
        vec![],
        vec![image_member],
    ));
    req.push(function_equation(rt, h, domain, apply(g, vec![fx]), x));
    let result = if scalar {
        let row = Obj::MatrixOperator(MatrixOperator::Scale(MatrixScale {
            scalar: Box::new(args[6].clone()),
            matrix: Box::new(args[5].clone()),
            rows: Box::new(number(1)),
            cols: Box::new(n.clone()),
        }));
        relation_from_args(
            rt,
            "has_scalar_differential_at",
            vec![h.clone(), p.clone(), n.clone(), row],
        )
    } else {
        let matrix = Obj::MatrixOperator(MatrixOperator::Multiply(MatrixMultiply {
            left: Box::new(args[8].clone()),
            right: Box::new(args[7].clone()),
            rows: Box::new(args[6].clone()),
            inner: Box::new(args[5].clone()),
            cols: Box::new(n.clone()),
        }));
        relation_from_args(
            rt,
            "has_total_derivative_at",
            vec![h.clone(), p.clone(), n.clone(), args[6].clone(), matrix],
        )
    };
    Ok(Ok((req, vec![result])))
}
fn second_partial(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    if id == SecondPartialAtFromFunction {
        let (f, g, p, n, i, j, l) = (
            &args[0], &args[1], &args[2], &args[3], &args[4], &args[5], &args[6],
        );
        let r = relation(
            "has_second_partial_derivative_at",
            &[
                f.clone(),
                p.clone(),
                n.clone(),
                i.clone(),
                j.clone(),
                l.clone(),
            ],
        );
        let Some((source, mut req)) = context(rt, &r)? else {
            return Ok(Err("requires a scalar Euclidean function".into()));
        };
        if !same_domain(rt, &mut req, &source, g, &r)? {
            return Ok(Err(
                "the first derivative function must use the same actual domain".into(),
            ));
        }
        let domain = actual_domain(&source.signature).unwrap();
        let q = rt.fresh_internal_param();
        let qo = identifier(&q);
        let candidate = relation_from_args(
            rt,
            "has_partial_derivative_at",
            vec![
                f.clone(),
                qo.clone(),
                n.clone(),
                i.clone(),
                apply(g, vec![qo]),
            ],
        );
        req.push(quantified(rt, q, domain, vec![], vec![candidate]));
        req.push(relation_from_args(
            rt,
            "has_partial_derivative_at",
            vec![g.clone(), p.clone(), n.clone(), j.clone(), l.clone()],
        ));
        return Ok(Ok((req, vec![relation_fact(rt, r)])));
    }
    // Schwarz: mixed partials exist on a full neighbourhood and are continuous at p.
    let (f, a, b, p, n, i, j, u) = (
        &args[0], &args[1], &args[2], &args[3], &args[4], &args[5], &args[6], &args[7],
    );
    let r = relation(
        "has_second_partial_derivative_at",
        &[
            f.clone(),
            p.clone(),
            n.clone(),
            i.clone(),
            j.clone(),
            number(0),
        ],
    );
    let Some((source, mut req)) = context(rt, &r)? else {
        return Ok(Err("requires a scalar Euclidean function".into()));
    };
    req.push(subset(
        rt,
        u.clone(),
        actual_domain(&source.signature).unwrap(),
    ));
    req.push(rt.multivariable_interior(u.clone(), p.clone(), n.clone()));
    req.push(member(rt, p.clone(), u.clone()));
    for (derivative, first, second) in [(a, i, j), (b, j, i)] {
        let c = relation(
            "is_multi_continuous_at",
            &[derivative.clone(), p.clone(), n.clone()],
        );
        let Some((d, more)) = context(rt, &c)? else {
            return Ok(Err("requires actual mixed derivative functions".into()));
        };
        req.extend(more);
        req.push(equal(rt, actual_domain(&d.signature).unwrap(), u.clone()));
        req.push(relation_fact(rt, c));
        let q = rt.fresh_internal_param();
        let qo = identifier(&q);
        let v = apply(derivative, vec![qo.clone()]);
        let mixed = relation_from_args(
            rt,
            "has_second_partial_derivative_at",
            vec![f.clone(), qo, n.clone(), first.clone(), second.clone(), v],
        );
        req.push(quantified(rt, q, u.clone(), vec![], vec![mixed]));
    }
    Ok(Ok((
        req,
        vec![equal(
            rt,
            apply(a, vec![p.clone()]),
            apply(b, vec![p.clone()]),
        )],
    )))
}

fn symmetric(rt: &mut Runtime, a: &Obj) -> Fact {
    let transpose = Obj::MatrixOperator(MatrixOperator::Transpose(MatrixTranspose {
        matrix: Box::new(a.clone()),
        rows: Box::new(number(3)),
        cols: Box::new(number(3)),
    }));
    equal(rt, a.clone(), transpose)
}
fn vector_identity(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    if id == SecondPartialAtToFunction {
        let (f, g, p, n, i, j, l) = (
            &args[0], &args[1], &args[2], &args[3], &args[4], &args[5], &args[6],
        );
        let r = relation(
            "has_second_partial_derivative_at",
            &[
                f.clone(),
                p.clone(),
                n.clone(),
                i.clone(),
                j.clone(),
                l.clone(),
            ],
        );
        let Some((source, mut req)) = context(rt, &r)? else {
            return Ok(Err("requires a scalar Euclidean function".into()));
        };
        if !same_domain(rt, &mut req, &source, g, &r)? {
            return Ok(Err(
                "requires the same complete domain for the first derivative function".into(),
            ));
        }
        req.push(relation_fact(rt, r));
        let q = rt.fresh_internal_param();
        let input = identifier(&q);
        let first = relation_from_args(
            rt,
            "has_partial_derivative_at",
            vec![
                f.clone(),
                input.clone(),
                n.clone(),
                i.clone(),
                apply(g, vec![input]),
            ],
        );
        req.push(quantified(
            rt,
            q,
            actual_domain(&source.signature).unwrap(),
            vec![],
            vec![first],
        ));
        return Ok(Ok((
            req,
            vec![relation_from_args(
                rt,
                "has_partial_derivative_at",
                vec![g.clone(), p.clone(), n.clone(), j.clone(), l.clone()],
            )],
        )));
    }
    let (f, g, p) = (&args[0], &args[1], &args[2]);
    let zero = Obj::ProductShape(ProductShape::Tuple(Tuple {
        args: vec![
            Box::new(number(0)),
            Box::new(number(0)),
            Box::new(number(0)),
        ],
    }));
    let source_relation = if id == CurlGradientAtSymmetric {
        relation(
            "has_hessian_at",
            &[f.clone(), p.clone(), number(3), args[3].clone()],
        )
    } else {
        relation("has_curl_at", &[f.clone(), p.clone(), zero.clone()])
    };
    let Some((source, mut req)) = context(rt, &source_relation)? else {
        return Ok(Err(
            "requires a complete three-dimensional source domain".into()
        ));
    };
    let target_relation = relation("has_curl_at", &[g.clone(), p.clone(), zero.clone()]);
    let Some((target, more)) = context(rt, &target_relation)? else {
        return Ok(Err("requires a three-component target function".into()));
    };
    req.extend(more);
    if !function_domains_alpha_equal(&source.signature, &target.signature) {
        return Ok(Err(
            "source and field must have the same complete actual input domain".into(),
        ));
    }
    let domain = actual_domain(&source.signature).unwrap();
    if id == CurlGradientAtSymmetric {
        req.push(relation_fact(rt, source_relation));
        req.push(symmetric(rt, &args[3]));
    } else {
        for (row, h) in args[3..].iter().enumerate() {
            let component = rt.multivariable_component_function(
                f.clone(),
                domain.clone(),
                number(row as i64 + 1),
            );
            req.push(relation_from_args(
                rt,
                "has_hessian_at",
                vec![component, p.clone(), number(3), h.clone()],
            ));
            req.push(symmetric(rt, h));
        }
    }
    let q = rt.fresh_internal_param();
    let input = identifier(&q);
    let candidate = if id == CurlGradientAtSymmetric {
        relation_from_args(
            rt,
            "has_gradient_at",
            vec![f.clone(), input.clone(), number(3), apply(g, vec![input])],
        )
    } else {
        relation_from_args(
            rt,
            "has_curl_at",
            vec![f.clone(), input.clone(), apply(g, vec![input])],
        )
    };
    req.push(quantified(rt, q, domain, vec![], vec![candidate]));
    let result = if id == CurlGradientAtSymmetric {
        relation_from_args(rt, "has_curl_at", vec![g.clone(), p.clone(), zero])
    } else {
        relation_from_args(
            rt,
            "has_divergence_at",
            vec![g.clone(), p.clone(), number(3), number(0)],
        )
    };
    Ok(Ok((req, vec![result])))
}

fn continuous_composition(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let scalar = matches!(id, MultiContinuousAtCompose | MultiLimitAtCompose);
    let limit = matches!(id, MultiLimitAtCompose | VectorLimitAtCompose);
    let (f, g, h, p, n) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
    let at = if limit {
        args.last().unwrap().clone()
    } else {
        apply(f, vec![p.clone()])
    };
    let mut input_args = vec![f.clone(), p.clone(), n.clone()];
    if !scalar {
        input_args.push(args[5].clone());
    }
    if limit {
        input_args.push(at.clone());
    }
    let input_name = match (scalar, limit) {
        (true, true) => "has_multi_limit_at",
        (true, false) => "is_multi_continuous_at",
        (false, true) => "has_vector_limit_at",
        (false, false) => "is_vector_continuous_at",
    };
    let input = relation(input_name, &input_args);
    let Some((source, mut req)) = context(rt, &input)? else {
        return Ok(Err(
            "requires the exact complete inner Euclidean function".into()
        ));
    };
    req.push(relation_fact(rt, input));
    let domain = actual_domain(&source.signature).unwrap();
    let outer_domain = if scalar {
        let Some(outer) = rt.checked_real_function_limit_domain(
            g,
            VerifyState::new(VerifyStateLevel::BuiltinRule),
        )?
        else {
            return Ok(Err("requires a complete unary real outer function".into()));
        };
        req.push(member(rt, at.clone(), outer.domain.clone()));
        req.push(
            FunctionContinuousAtFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                function: g.clone(),
                point: at.clone(),
                side: RealApproachSide::Both,
                line_file: None,
            }
            .into(),
        );
        outer.domain
    } else {
        let outer = relation(
            "is_vector_continuous_at",
            &[g.clone(), at.clone(), args[5].clone(), args[6].clone()],
        );
        let Some((outer_domain, more)) = context(rt, &outer)? else {
            return Ok(Err(
                "requires a complete continuous outer vector function".into()
            ));
        };
        req.extend(more);
        req.push(relation_fact(rt, outer));
        actual_domain(&outer_domain.signature).unwrap()
    };
    let mut target_args = vec![h.clone(), p.clone(), n.clone()];
    if !scalar {
        target_args.push(args[6].clone());
    }
    if limit {
        target_args.push(apply(g, vec![at]));
    }
    let result = relation(input_name, &target_args);
    if !same_domain(rt, &mut req, &source, h, &result)? {
        return Ok(Err(
            "composition must retain the complete inner actual domain".into(),
        ));
    }
    let q = rt.fresh_internal_param();
    let input = identifier(&q);
    let inner = apply(f, vec![input]);
    let admissible = member(rt, inner.clone(), outer_domain);
    req.push(quantified(
        rt,
        q.clone(),
        domain.clone(),
        vec![],
        vec![admissible],
    ));
    req.push(function_equation(rt, h, domain, apply(g, vec![inner]), q));
    Ok(Ok((req, vec![relation_fact(rt, result)])))
}
