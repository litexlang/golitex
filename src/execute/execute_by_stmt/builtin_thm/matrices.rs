//! Explicit finite linear algebra contracts. All actual domains and premises
//! are verified by the ordinary theorem invocation pipeline.
use super::helper::{atomic_in, equal, identifier, le, number};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::matrix_operations::{
    self as formulas, add, anonymous, conjugate, determinant, identity, index_set, matrix_multiply,
    modulus, mul, pow, vector_space,
};
use crate::execute::execute_fact_stmt::native_matrix::{matrix_call, matrix_space};
use crate::prelude::*;

pub(super) fn prepare_matrices(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let mut req = Vec::new();
    let mut out = Vec::new();
    match id {
        MatrixApplyIdentity => {
            let [v, n] = args else { unreachable!() };
            vector(rt, &mut req, v, n);
            out.push(equal(rt, apply(&identity(n.clone()), v, n, n), v.clone()).into());
        }
        MatrixInnerProductAdjoint => {
            let [a, u, v, m, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, n)]);
            vector(rt, &mut req, u, n);
            vector(rt, &mut req, v, m);
            out.push(
                equal(
                    rt,
                    inner(&apply(a, u, m, n), v, m),
                    inner(u, &apply(&transpose(a, m, n, true), v, n, m), n),
                )
                .into(),
            );
        }
        MatrixRankFactorizationExists => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            let k = rank(a, m, n);
            let u = rt.fresh_internal_param();
            let v = rt.fresh_internal_param();
            let l = rt.fresh_internal_param();
            let r = rt.fresh_internal_param();
            let (ui, vi, li, ri) = (
                identifier(&u),
                identifier(&v),
                identifier(&l),
                identifier(&r),
            );
            let params = TypedParameterList {
                groups: vec![
                    (u, m.clone(), k.clone()),
                    (v, k.clone(), n.clone()),
                    (l, k.clone(), m.clone()),
                    (r, n.clone(), k.clone()),
                ]
                .into_iter()
                .map(|(name, rows, cols)| TypedParameterGroup {
                    params: vec![name],
                    param_type: ParamType::Obj(matrix_space(
                        Obj::StandardSet(StandardSet::C),
                        rows,
                        cols,
                    )),
                })
                .collect(),
            };
            let body = vec![
                equal(rt, a.clone(), mmul(&ui, &vi, m, &k, n)),
                equal(rt, mmul(&li, &ui, &k, m, &k), identity(k.clone())),
                equal(rt, mmul(&vi, &ri, &k, n, &k), identity(k)),
            ];
            out.push(super::helper::exist(rt, params, body, false));
        }
        MatrixMulAssociative => {
            let [a, b, c, m, k, p, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, k, p), (c, p, n)]);
            out.push(
                equal(
                    rt,
                    mmul(&mmul(a, b, m, k, p), c, m, p, n),
                    mmul(a, &mmul(b, c, k, p, n), m, k, n),
                )
                .into(),
            );
        }
        MatrixMulDistributiveLeft => {
            let [a, b, c, m, k, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, k, n), (c, k, n)]);
            out.push(
                equal(
                    rt,
                    mmul(a, &madd(b, c, k, n), m, k, n),
                    madd(&mmul(a, b, m, k, n), &mmul(a, c, m, k, n), m, n),
                )
                .into(),
            );
        }
        MatrixMulDistributiveRight => {
            let [a, b, c, m, k, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, m, k), (c, k, n)]);
            out.push(
                equal(
                    rt,
                    mmul(&madd(a, b, m, k), c, m, k, n),
                    madd(&mmul(a, c, m, k, n), &mmul(b, c, m, k, n), m, n),
                )
                .into(),
            );
        }
        MatrixMulIdentity => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            out.extend([
                equal(rt, mmul(&identity(m.clone()), a, m, m, n), a.clone()).into(),
                equal(rt, mmul(a, &identity(n.clone()), m, n, n), a.clone()).into(),
            ]);
        }
        MatrixMulZero => {
            let [a, m, n, p] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            nat(rt, &mut req, p);
            out.extend([
                equal(rt, mmul(a, &zero(n, p), m, n, p), zero(m, p)).into(),
                equal(rt, mmul(&zero(p, m), a, p, m, n), zero(p, n)).into(),
            ]);
        }
        MatrixApplyCompose => {
            let [a, b, v, m, k, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, k, n)]);
            vector(rt, &mut req, v, n);
            out.push(
                equal(
                    rt,
                    apply(&mmul(a, b, m, k, n), v, m, n),
                    apply(a, &apply(b, v, k, n), m, k),
                )
                .into(),
            );
        }
        MatrixTransposeMul | MatrixAdjointMul => {
            let [a, b, m, k, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, k, n)]);
            let adjoint = id == MatrixAdjointMul;
            out.push(
                equal(
                    rt,
                    transpose(&mmul(a, b, m, k, n), m, n, adjoint),
                    mmul(
                        &transpose(b, k, n, adjoint),
                        &transpose(a, m, k, adjoint),
                        n,
                        k,
                        m,
                    ),
                )
                .into(),
            );
        }
        MatrixTraceLinearity => {
            let [a, b, z, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n), (b, n, n)]);
            scalar(rt, &mut req, z);
            out.extend([
                equal(
                    rt,
                    trace(&madd(a, b, n, n), n),
                    add(trace(a, n), trace(b, n)),
                )
                .into(),
                equal(
                    rt,
                    trace(&scale(z, a, n, n), n),
                    mul(z.clone(), trace(a, n)),
                )
                .into(),
            ]);
        }
        MatrixTraceCyclic => {
            let [a, b, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n), (b, n, m)]);
            out.push(
                equal(
                    rt,
                    trace(&mmul(a, b, m, n, m), m),
                    trace(&mmul(b, a, n, m, n), n),
                )
                .into(),
            );
        }
        MatrixPowerZero => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            out.push(equal(rt, mpower(a, n, &number("0")), identity(n.clone())).into());
        }
        MatrixPowerSuccessor => {
            let [a, n, p] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            nat(rt, &mut req, p);
            out.push(
                equal(
                    rt,
                    mpower(a, n, &add(p.clone(), number("1"))),
                    mmul(&mpower(a, n, p), a, n, n, n),
                )
                .into(),
            );
        }
        MatrixPowerAdd => {
            let [a, n, p, q] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            nat(rt, &mut req, p);
            nat(rt, &mut req, q);
            out.push(
                equal(
                    rt,
                    mpower(a, n, &add(p.clone(), q.clone())),
                    mmul(&mpower(a, n, p), &mpower(a, n, q), n, n, n),
                )
                .into(),
            );
        }
        MatrixDetIdentity
        | MatrixDetTranspose
        | MatrixDetAdjoint
        | MatrixDetMul
        | MatrixDetLaplaceRow
        | MatrixDetLaplaceColumn
        | MatrixDetUpperTriangular
        | MatrixDetLowerTriangular
        | MatrixAdjugateIdentity
        | MatrixInvertibleFromCandidate
        | MatrixInverseFromCandidate
        | MatrixInverseLaws => return prepare_determinants(rt, id, args),
        MatrixRankBounds
        | MatrixRankZero
        | MatrixRankIdentity
        | MatrixRankFromFactorization
        | MatrixRankTranspose
        | MatrixRankAdjoint
        | MatrixRankProduct
        | MatrixRankInvertible
        | InnerProductConjugateSymmetry
        | InnerProductLinearRight
        | InnerProductPositive
        | InnerProductCauchySchwarz
        | EuclideanNormSquare
        | EuclideanNormZero
        | EuclideanNormScale
        | EuclideanNormTriangle
        | FrobeniusNormSquare
        | FrobeniusNormZero
        | FrobeniusNormScale
        | FrobeniusNormTriangle => return prepare_rank_norm(rt, id, args),
        _ => unreachable!("matrix dispatcher receives matrix theorem IDs only"),
    }
    Ok(Ok((req, out)))
}

fn prepare_determinants(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let mut req = Vec::new();
    let mut out = Vec::new();
    match id {
        MatrixDetIdentity => {
            let [n] = args else { unreachable!() };
            nat(rt, &mut req, n);
            out.push(equal(rt, det(&identity(n.clone()), n), number("1")).into());
        }
        MatrixDetTranspose | MatrixDetAdjoint => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            let adj = id == MatrixDetAdjoint;
            let result = if adj { conjugate(det(a, n)) } else { det(a, n) };
            out.push(equal(rt, det(&transpose(a, n, n, adj), n), result).into());
        }
        MatrixDetMul => {
            let [a, b, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n), (b, n, n)]);
            out.push(equal(rt, det(&mmul(a, b, n, n, n), n), mul(det(a, n), det(b, n))).into());
        }
        MatrixDetLaplaceRow | MatrixDetLaplaceColumn => {
            let [a, n, i] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            req.push(atomic_in(rt, n.clone(), Obj::StandardSet(StandardSet::NPos)).into());
            req.push(atomic_in(rt, i.clone(), index_set(n)).into());
            let j = rt.fresh_internal_param();
            let index = identifier(&j);
            let row = id == MatrixDetLaplaceRow;
            let (r, c) = if row {
                (i.clone(), index)
            } else {
                (index, i.clone())
            };
            let body = mul(
                matrix_call(a, vec![r.clone(), c.clone()]),
                cofactor(a, n, &r, &c),
            );
            let formula = formulas::finite_sum(
                index_set(n),
                anonymous(
                    vec![(j, index_set(n))],
                    Obj::StandardSet(StandardSet::C),
                    body,
                ),
            );
            out.push(equal(rt, det(a, n), formula).into());
        }
        MatrixDetUpperTriangular | MatrixDetLowerTriangular => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            let r = rt.fresh_internal_param();
            let c = rt.fresh_internal_param();
            let ri = identifier(&r);
            let ci = identifier(&c);
            let condition = if id == MatrixDetUpperTriangular {
                lt(rt, ci.clone(), ri.clone())
            } else {
                lt(rt, ri.clone(), ci.clone())
            };
            let body = equal(rt, matrix_call(a, vec![ri, ci]), number("0"));
            req.push(quantified(
                rt,
                vec![(r, index_set(n)), (c, index_set(n))],
                vec![condition.into()],
                vec![body],
            ));
            let k = rt.fresh_internal_param();
            let j = identifier(&k);
            let callback = anonymous(
                vec![(k, index_set(n))],
                Obj::StandardSet(StandardSet::C),
                matrix_call(a, vec![j.clone(), j]),
            );
            let product =
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(ProductOfFiniteSet {
                    set: Box::new(index_set(n)),
                    func: Box::new(callback),
                }));
            out.push(equal(rt, det(a, n), product).into());
        }
        MatrixAdjugateIdentity => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            let adj = adjugate(a, n);
            let value = scale(&det(a, n), &identity(n.clone()), n, n);
            out.extend([
                equal(rt, mmul(a, &adj, n, n, n), value.clone()).into(),
                equal(rt, mmul(&adj, a, n, n, n), value).into(),
            ]);
        }
        MatrixInvertibleFromCandidate | MatrixInverseFromCandidate => {
            let [a, b, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n), (b, n, n)]);
            req.extend([
                equal(rt, mmul(a, b, n, n, n), identity(n.clone())).into(),
                equal(rt, mmul(b, a, n, n, n), identity(n.clone())).into(),
            ]);
            if id == MatrixInvertibleFromCandidate {
                out.push(ne(rt, det(a, n), number("0")).into());
            } else {
                req.push(ne(rt, det(a, n), number("0")).into());
                out.push(equal(rt, inverse(a, n), b.clone()).into());
            }
        }
        MatrixInverseLaws => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            req.push(ne(rt, det(a, n), number("0")).into());
            let inv = inverse(a, n);
            out.extend([
                equal(rt, mmul(a, &inv, n, n, n), identity(n.clone())).into(),
                equal(rt, mmul(&inv, a, n, n, n), identity(n.clone())).into(),
            ]);
        }
        _ => unreachable!("determinant theorem dispatcher"),
    }
    Ok(Ok((req, out)))
}

fn prepare_rank_norm(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let mut req = Vec::new();
    let mut out = Vec::new();
    match id {
        MatrixRankBounds => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            out.extend([
                atomic_in(rt, rank(a, m, n), Obj::StandardSet(StandardSet::N)).into(),
                le(rt, rank(a, m, n), m.clone()).into(),
                le(rt, rank(a, m, n), n.clone()).into(),
            ]);
        }
        MatrixRankZero => {
            let [m, n] = args else { unreachable!() };
            nat(rt, &mut req, m);
            nat(rt, &mut req, n);
            out.push(equal(rt, rank(&zero(m, n), m, n), number("0")).into());
        }
        MatrixRankIdentity => {
            let [n] = args else { unreachable!() };
            nat(rt, &mut req, n);
            out.push(equal(rt, rank(&identity(n.clone()), n, n), n.clone()).into());
        }
        MatrixRankFromFactorization => {
            let [a, u, v, l, r, m, k, n] = args else {
                unreachable!()
            };
            matrices(
                rt,
                &mut req,
                &[(a, m, n), (u, m, k), (v, k, n), (l, k, m), (r, n, k)],
            );
            req.extend([
                le(rt, k.clone(), m.clone()).into(),
                le(rt, k.clone(), n.clone()).into(),
                equal(rt, a.clone(), mmul(u, v, m, k, n)).into(),
                equal(rt, mmul(l, u, k, m, k), identity(k.clone())).into(),
                equal(rt, mmul(v, r, k, n, k), identity(k.clone())).into(),
            ]);
            out.push(equal(rt, rank(a, m, n), k.clone()).into());
        }
        MatrixRankTranspose | MatrixRankAdjoint => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            out.push(
                equal(
                    rt,
                    rank(&transpose(a, m, n, id == MatrixRankAdjoint), n, m),
                    rank(a, m, n),
                )
                .into(),
            );
        }
        MatrixRankProduct => {
            let [a, b, m, k, n] = args else {
                unreachable!()
            };
            matrices(rt, &mut req, &[(a, m, k), (b, k, n)]);
            let product = rank(&mmul(a, b, m, k, n), m, n);
            out.extend([
                le(rt, product.clone(), rank(a, m, k)).into(),
                le(rt, product, rank(b, k, n)).into(),
            ]);
        }
        MatrixRankInvertible => {
            let [a, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, n, n)]);
            req.push(ne(rt, det(a, n), number("0")).into());
            out.push(equal(rt, rank(a, n, n), n.clone()).into());
        }
        InnerProductConjugateSymmetry => {
            let [u, v, n] = args else { unreachable!() };
            vector(rt, &mut req, u, n);
            vector(rt, &mut req, v, n);
            out.push(equal(rt, inner(u, v, n), conjugate(inner(v, u, n))).into());
        }
        InnerProductLinearRight => {
            let [u, v, w, a, b, n] = args else {
                unreachable!()
            };
            for x in [u, v, w] {
                vector(rt, &mut req, x, n)
            }
            for x in [a, b] {
                scalar(rt, &mut req, x)
            }
            let value = vector_combination(rt, v, w, a, b, n);
            out.push(
                equal(
                    rt,
                    inner(u, &value, n),
                    add(
                        mul(a.clone(), inner(u, v, n)),
                        mul(b.clone(), inner(u, w, n)),
                    ),
                )
                .into(),
            );
        }
        InnerProductPositive => {
            let [v, n] = args else { unreachable!() };
            vector(rt, &mut req, v, n);
            let value = inner(v, v, n);
            out.extend([
                atomic_in(rt, value.clone(), Obj::StandardSet(StandardSet::R)).into(),
                le(rt, number("0"), real(value.clone())).into(),
                equal(rt, imaginary(value), number("0")).into(),
            ]);
        }
        InnerProductCauchySchwarz => {
            let [u, v, n] = args else { unreachable!() };
            vector(rt, &mut req, u, n);
            vector(rt, &mut req, v, n);
            out.push(le(rt, modulus(inner(u, v, n)), mul(norm(u, n), norm(v, n))).into());
        }
        EuclideanNormSquare => {
            let [v, n] = args else { unreachable!() };
            vector(rt, &mut req, v, n);
            let object = norm(v, n);
            let Some(Obj::ExpLogOperator(ExpLogOperator::Sqrt(formula))) = rt
                .extended_matrix_scalar_definition(match &object {
                    Obj::MatrixOperator(x) => x,
                    _ => unreachable!(),
                })
            else {
                unreachable!()
            };
            out.extend([
                equal(
                    rt,
                    pow(object.clone(), number("2")),
                    formula.arg.as_ref().clone(),
                )
                .into(),
                equal(rt, pow(object.clone(), number("2")), inner(v, v, n)).into(),
                le(rt, number("0"), object).into(),
            ]);
        }
        EuclideanNormZero => {
            let [v, n] = args else { unreachable!() };
            vector(rt, &mut req, v, n);
            let zero = vector_zero(rt, n);
            let norm_zero = equal(rt, norm(v, n), number("0"));
            let vector_zero = equal(rt, v.clone(), zero);
            out.extend([
                conditional(
                    rt,
                    vec![norm_zero.clone().into()],
                    vec![vector_zero.clone()],
                ),
                conditional(rt, vec![vector_zero.into()], vec![norm_zero]),
            ]);
        }
        EuclideanNormScale => {
            let [a, v, n] = args else { unreachable!() };
            scalar(rt, &mut req, a);
            vector(rt, &mut req, v, n);
            let scaled = vector_scale(rt, a, v, n);
            out.push(equal(rt, norm(&scaled, n), mul(modulus(a.clone()), norm(v, n))).into());
        }
        EuclideanNormTriangle => {
            let [u, v, n] = args else { unreachable!() };
            vector(rt, &mut req, u, n);
            vector(rt, &mut req, v, n);
            let sum = vector_combination(rt, u, v, &number("1"), &number("1"), n);
            out.push(le(rt, norm(&sum, n), add(norm(u, n), norm(v, n))).into());
        }
        FrobeniusNormSquare => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            let object = frobenius(a, m, n);
            let Some(Obj::ExpLogOperator(ExpLogOperator::Sqrt(formula))) = rt
                .extended_matrix_scalar_definition(match &object {
                    Obj::MatrixOperator(x) => x,
                    _ => unreachable!(),
                })
            else {
                unreachable!()
            };
            out.extend([
                equal(
                    rt,
                    pow(object.clone(), number("2")),
                    formula.arg.as_ref().clone(),
                )
                .into(),
                le(rt, number("0"), object).into(),
            ]);
        }
        FrobeniusNormZero => {
            let [a, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n)]);
            let norm_zero = equal(rt, frobenius(a, m, n), number("0"));
            let matrix_zero = equal(rt, a.clone(), zero(m, n));
            out.extend([
                conditional(
                    rt,
                    vec![norm_zero.clone().into()],
                    vec![matrix_zero.clone()],
                ),
                conditional(rt, vec![matrix_zero.into()], vec![norm_zero]),
            ]);
        }
        FrobeniusNormScale => {
            let [z, a, m, n] = args else { unreachable!() };
            scalar(rt, &mut req, z);
            matrices(rt, &mut req, &[(a, m, n)]);
            out.push(
                equal(
                    rt,
                    frobenius(&scale(z, a, m, n), m, n),
                    mul(modulus(z.clone()), frobenius(a, m, n)),
                )
                .into(),
            );
        }
        FrobeniusNormTriangle => {
            let [a, b, m, n] = args else { unreachable!() };
            matrices(rt, &mut req, &[(a, m, n), (b, m, n)]);
            out.push(
                le(
                    rt,
                    frobenius(&madd(a, b, m, n), m, n),
                    add(frobenius(a, m, n), frobenius(b, m, n)),
                )
                .into(),
            );
        }
        _ => unreachable!("rank and norm theorem dispatcher"),
    }
    Ok(Ok((req, out)))
}

fn matrices(rt: &mut Runtime, req: &mut Vec<Fact>, values: &[(&Obj, &Obj, &Obj)]) {
    for (a, m, n) in values {
        nat(rt, req, m);
        nat(rt, req, n);
        req.push(
            atomic_in(
                rt,
                (*a).clone(),
                matrix_space(Obj::StandardSet(StandardSet::C), (*m).clone(), (*n).clone()),
            )
            .into(),
        );
    }
}
fn vector(rt: &mut Runtime, req: &mut Vec<Fact>, v: &Obj, n: &Obj) {
    nat(rt, req, n);
    req.push(atomic_in(rt, v.clone(), vector_space(StandardSet::C, n.clone())).into());
}
fn scalar(rt: &mut Runtime, req: &mut Vec<Fact>, z: &Obj) {
    req.push(atomic_in(rt, z.clone(), Obj::StandardSet(StandardSet::C)).into());
}
fn nat(rt: &mut Runtime, req: &mut Vec<Fact>, n: &Obj) {
    req.push(atomic_in(rt, n.clone(), Obj::StandardSet(StandardSet::N)).into());
}
fn ne(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    AtomicFact::NotEqualFact(NotEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    })
}
fn lt(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    AtomicFact::LessFact(LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    })
}
fn conditional(rt: &mut Runtime, dom: Vec<Fact>, body: Vec<AtomicFact>) -> Fact {
    quantified(rt, vec![], dom, body)
}
fn quantified(
    rt: &mut Runtime,
    params: Vec<(BoundName, Obj)>,
    dom: Vec<Fact>,
    body: Vec<AtomicFact>,
) -> Fact {
    Fact::ForallFact(ForallFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: params
                .into_iter()
                .map(|(name, set)| TypedParameterGroup {
                    params: vec![name],
                    param_type: ParamType::Obj(set),
                })
                .collect(),
        },
        dom_facts: dom,
        then_facts: body
            .into_iter()
            .map(ExistOrAndChainAtomicFact::AtomicFact)
            .collect(),
        line_file: None,
    })
}
fn madd(a: &Obj, b: &Obj, m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Add(MatrixAdd {
        left: Box::new(a.clone()),
        right: Box::new(b.clone()),
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn scale(z: &Obj, a: &Obj, m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Scale(MatrixScale {
        scalar: Box::new(z.clone()),
        matrix: Box::new(a.clone()),
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn mmul(a: &Obj, b: &Obj, m: &Obj, k: &Obj, n: &Obj) -> Obj {
    matrix_multiply(a.clone(), b.clone(), m.clone(), k.clone(), n.clone())
}
fn apply(a: &Obj, v: &Obj, m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Apply(MatrixApply {
        matrix: Box::new(a.clone()),
        vector: Box::new(v.clone()),
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn zero(m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::ZeroMatrix(ZeroMatrix {
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn transpose(a: &Obj, m: &Obj, n: &Obj, adjoint: bool) -> Obj {
    Obj::MatrixOperator(if adjoint {
        MatrixOperator::ConjugateTranspose(MatrixConjugateTranspose {
            matrix: Box::new(a.clone()),
            rows: Box::new(m.clone()),
            cols: Box::new(n.clone()),
        })
    } else {
        MatrixOperator::Transpose(MatrixTranspose {
            matrix: Box::new(a.clone()),
            rows: Box::new(m.clone()),
            cols: Box::new(n.clone()),
        })
    })
}
fn trace(a: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Trace(MatrixTrace {
        matrix: Box::new(a.clone()),
        order: Box::new(n.clone()),
    }))
}
fn mpower(a: &Obj, n: &Obj, p: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Power(MatrixPower {
        matrix: Box::new(a.clone()),
        order: Box::new(n.clone()),
        exponent: Box::new(p.clone()),
    }))
}
fn det(a: &Obj, n: &Obj) -> Obj {
    determinant(a.clone(), n.clone())
}
fn cofactor(a: &Obj, n: &Obj, r: &Obj, c: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Cofactor(MatrixCofactor {
        matrix: Box::new(a.clone()),
        order: Box::new(n.clone()),
        row: Box::new(r.clone()),
        col: Box::new(c.clone()),
    }))
}
fn adjugate(a: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Adjugate(MatrixAdjugate {
        matrix: Box::new(a.clone()),
        order: Box::new(n.clone()),
    }))
}
fn inverse(a: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Inverse(MatrixInverse {
        matrix: Box::new(a.clone()),
        order: Box::new(n.clone()),
    }))
}
fn rank(a: &Obj, m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Rank(MatrixRank {
        matrix: Box::new(a.clone()),
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn inner(u: &Obj, v: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::InnerProduct(FiniteInnerProduct {
        left: Box::new(u.clone()),
        right: Box::new(v.clone()),
        dimension: Box::new(n.clone()),
    }))
}
fn norm(v: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::EuclideanNorm(EuclideanNorm {
        vector: Box::new(v.clone()),
        dimension: Box::new(n.clone()),
    }))
}
fn frobenius(a: &Obj, m: &Obj, n: &Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(MatrixFrobeniusNorm {
        matrix: Box::new(a.clone()),
        rows: Box::new(m.clone()),
        cols: Box::new(n.clone()),
    }))
}
fn real(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg: Box::new(arg) }))
}
fn imaginary(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart {
        arg: Box::new(arg),
    }))
}
fn vector_zero(rt: &mut Runtime, n: &Obj) -> Obj {
    let k = rt.fresh_internal_param();
    anonymous(
        vec![(k, index_set(n))],
        Obj::StandardSet(StandardSet::C),
        number("0"),
    )
}
fn vector_scale(rt: &mut Runtime, z: &Obj, v: &Obj, n: &Obj) -> Obj {
    let k = rt.fresh_internal_param();
    let body = mul(z.clone(), matrix_call(v, vec![identifier(&k)]));
    anonymous(
        vec![(k, index_set(n))],
        Obj::StandardSet(StandardSet::C),
        body,
    )
}
fn vector_combination(rt: &mut Runtime, u: &Obj, v: &Obj, a: &Obj, b: &Obj, n: &Obj) -> Obj {
    let k = rt.fresh_internal_param();
    let x = identifier(&k);
    let body = add(
        mul(a.clone(), matrix_call(u, vec![x.clone()])),
        mul(b.clone(), matrix_call(v, vec![x])),
    );
    anonymous(
        vec![(k, index_set(n))],
        Obj::StandardSet(StandardSet::C),
        body,
    )
}
