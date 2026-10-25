//! Formula-defined finite linear algebra. Values remain ordinary functions.
pub(crate) mod real_signature;
use super::native_matrix::*;
use crate::prelude::*;

impl Runtime {
    pub(crate) fn extended_matrix_scalar_membership(
        &mut self,
        operator: &MatrixOperator,
        target: StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<Option<ExtendedMatrixScalarMembershipProof>> {
        let mut real_domains = Vec::new();
        let scalar = match operator {
            MatrixOperator::Rank(_) => StandardSet::N,
            MatrixOperator::EuclideanNorm(_) | MatrixOperator::FrobeniusNorm(_) => StandardSet::R,
            MatrixOperator::Cofactor(x) => {
                real_domains.push(real_matrix(&x.matrix, &x.order, &x.order));
                StandardSet::C
            }
            MatrixOperator::InnerProduct(x) => {
                real_domains.extend([
                    real_vector(&x.left, &x.dimension),
                    real_vector(&x.right, &x.dimension),
                ]);
                StandardSet::C
            }
            MatrixOperator::Determinant(_)
            | MatrixOperator::ZeroMatrix(_)
            | MatrixOperator::IdentityMatrix(_)
            | MatrixOperator::Transpose(_)
            | MatrixOperator::ConjugateTranspose(_)
            | MatrixOperator::Trace(_)
            | MatrixOperator::Add(_)
            | MatrixOperator::Subtract(_)
            | MatrixOperator::Scale(_)
            | MatrixOperator::Multiply(_)
            | MatrixOperator::Apply(_)
            | MatrixOperator::Power(_)
            | MatrixOperator::Inverse(_)
            | MatrixOperator::Minor(_)
            | MatrixOperator::Adjugate(_)
            | MatrixOperator::Diagonal(_)
            | MatrixOperator::OuterProduct(_) => return Ok(None),
        };
        let carrier=if super::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq(&scalar,&target) {
            MatrixScalarCarrierProof::StandardSubset
        } else if scalar==StandardSet::C && target==StandardSet::R {
            let mut proofs=Vec::new();
            for (element,set) in real_domains {
                let Some(proof)=self.matrix_real_operand(&element,&set,state)? else {return Ok(None)};
                proofs.push(proof);
            }
            MatrixScalarCarrierProof::RealInputs(proofs)
        } else {return Ok(None)};
        Ok(Some(match operator {
            MatrixOperator::Rank(_) => {
                ExtendedMatrixScalarMembershipProof::Rank(MatrixRankScalarProof { target })
            }
            MatrixOperator::EuclideanNorm(_) => {
                ExtendedMatrixScalarMembershipProof::EuclideanNorm(EuclideanNormScalarProof {
                    target,
                })
            }
            MatrixOperator::FrobeniusNorm(_) => {
                ExtendedMatrixScalarMembershipProof::FrobeniusNorm(MatrixFrobeniusNormScalarProof {
                    target,
                })
            }
            MatrixOperator::Cofactor(_) => {
                ExtendedMatrixScalarMembershipProof::Cofactor(MatrixCofactorScalarProof { carrier })
            }
            MatrixOperator::InnerProduct(_) => {
                ExtendedMatrixScalarMembershipProof::InnerProduct(FiniteInnerProductScalarProof {
                    carrier,
                })
            }
            MatrixOperator::Determinant(_)
            | MatrixOperator::ZeroMatrix(_)
            | MatrixOperator::IdentityMatrix(_)
            | MatrixOperator::Transpose(_)
            | MatrixOperator::ConjugateTranspose(_)
            | MatrixOperator::Trace(_)
            | MatrixOperator::Add(_)
            | MatrixOperator::Subtract(_)
            | MatrixOperator::Scale(_)
            | MatrixOperator::Multiply(_)
            | MatrixOperator::Apply(_)
            | MatrixOperator::Power(_)
            | MatrixOperator::Inverse(_)
            | MatrixOperator::Minor(_)
            | MatrixOperator::Adjugate(_)
            | MatrixOperator::Diagonal(_)
            | MatrixOperator::OuterProduct(_) => unreachable!(),
        }))
    }
    pub(crate) fn extended_matrix_callable(
        &mut self,
        operator: &MatrixOperator,
        path: KnownEqualityPathProof,
        state: VerifyState,
        parent_atomic: bool,
    ) -> RuntimeResult<Option<MatrixCallableProof>> {
        let Some(layout) = real_signature::extended_layout(operator) else {
            return Ok(None);
        };
        let real_domains = layout.real_domains;
        let rows = layout.rows;
        let cols = layout.cols;
        let vector = layout.vector;
        let root = Obj::MatrixOperator(operator.clone());
        let well_defined = if parent_atomic {
            MatrixCallableWellDefinedProof::ParentAtomic
        } else {
            let VerifyObjWellDefinedResult::Success(proof) =
                self.verify_obj_well_definedness(&root, state)?
            else {
                return Ok(None);
            };
            MatrixCallableWellDefinedProof::Checked(Box::new(proof))
        };
        let mut real_proofs = Vec::new();
        let mut all_real = true;
        for (element, set) in real_domains {
            let Some(proof) = self.matrix_real_operand(&element, &set, state)? else {
                all_real = false;
                break;
            };
            real_proofs.push(proof);
        }
        let scalar = if all_real {
            StandardSet::R
        } else {
            StandardSet::C
        };
        let signature = if vector {
            self.finite_vector_signature(scalar.clone(), &rows)
        } else {
            self.matrix_fn_signature(&Obj::StandardSet(scalar.clone()), &rows, &cols)
        };
        let r = matrix_identifier(&signature.set_bound_parameters.groups[0].params[0]);
        let c = if vector {
            matrix_number(0)
        } else {
            matrix_identifier(&signature.set_bound_parameters.groups[1].params[0])
        };
        let body = match operator {
            MatrixOperator::Add(x) => add(
                matrix_call(&x.left, vec![r.clone(), c.clone()]),
                matrix_call(&x.right, vec![r, c]),
            ),
            MatrixOperator::Subtract(x) => sub(
                matrix_call(&x.left, vec![r.clone(), c.clone()]),
                matrix_call(&x.right, vec![r, c]),
            ),
            MatrixOperator::Scale(x) => mul(
                x.scalar.as_ref().clone(),
                matrix_call(&x.matrix, vec![r, c]),
            ),
            MatrixOperator::Multiply(x) => {
                self.matrix_product_entry(&x.left, &x.right, &x.inner, r, c)
            }
            MatrixOperator::Apply(x) => {
                let k = self.fresh_internal_param();
                let j = matrix_identifier(&k);
                let term = mul(
                    matrix_call(&x.matrix, vec![r, j.clone()]),
                    matrix_call(&x.vector, vec![j]),
                );
                finite_sum(
                    index_set(&x.cols),
                    anonymous(
                        vec![(k, index_set(&x.cols))],
                        Obj::StandardSet(StandardSet::C),
                        term,
                    ),
                )
            }
            MatrixOperator::Power(x) => {
                match natural_literal(&x.exponent) {
                    Some(0) => matrix_call(&identity(x.order.as_ref().clone()), vec![r, c]),
                    Some(p) => {
                        let previous = Obj::MatrixOperator(MatrixOperator::Power(MatrixPower {
                            matrix: x.matrix.clone(),
                            order: x.order.clone(),
                            exponent: Box::new(matrix_number(p - 1)),
                        }));
                        self.matrix_product_entry(&previous, &x.matrix, &x.order, r, c)
                    }
                    None => {
                        // The symbolic natural power is an ordered fold in the
                        // existing matrix function space; no fictitious beta body.
                        let carrier = matrix_space(
                            Obj::StandardSet(StandardSet::C),
                            x.order.as_ref().clone(),
                            x.order.as_ref().clone(),
                        );
                        let k = self.fresh_internal_param();
                        let a = self.fresh_internal_param();
                        let b = self.fresh_internal_param();
                        let op = matrix_multiply(
                            matrix_identifier(&a),
                            matrix_identifier(&b),
                            x.order.as_ref().clone(),
                            x.order.as_ref().clone(),
                            x.order.as_ref().clone(),
                        );
                        let fold = Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                            start: Box::new(matrix_number(1)),
                            end: x.exponent.clone(),
                            func: Box::new(anonymous(
                                vec![(k, Obj::StandardSet(StandardSet::Z))],
                                carrier.clone(),
                                x.matrix.as_ref().clone(),
                            )),
                            op: Box::new(anonymous(
                                vec![(a, carrier.clone()), (b, carrier.clone())],
                                carrier,
                                op,
                            )),
                            seed: Box::new(identity(x.order.as_ref().clone())),
                        }));
                        matrix_call(&fold, vec![r, c])
                    }
                }
            }
            MatrixOperator::Inverse(x) => div(
                Obj::MatrixOperator(MatrixOperator::Cofactor(MatrixCofactor {
                    matrix: x.matrix.clone(),
                    order: x.order.clone(),
                    row: Box::new(c),
                    col: Box::new(r),
                })),
                determinant(x.matrix.as_ref().clone(), x.order.as_ref().clone()),
            ),
            MatrixOperator::Minor(x) => {
                let row = skip_index(r, &x.row, &x.order);
                let col = skip_index(c, &x.col, &x.order);
                matrix_call(&x.matrix, vec![row, col])
            }
            MatrixOperator::Adjugate(x) => {
                Obj::MatrixOperator(MatrixOperator::Cofactor(MatrixCofactor {
                    matrix: x.matrix.clone(),
                    order: x.order.clone(),
                    row: Box::new(c),
                    col: Box::new(r),
                }))
            }
            MatrixOperator::Diagonal(x) => {
                mul(delta(r.clone(), c), matrix_call(&x.vector, vec![r]))
            }
            MatrixOperator::OuterProduct(x) => mul(
                matrix_call(&x.left, vec![r]),
                matrix_call(&x.right, vec![c]),
            ),
            MatrixOperator::Determinant(_)
            | MatrixOperator::ZeroMatrix(_)
            | MatrixOperator::IdentityMatrix(_)
            | MatrixOperator::Transpose(_)
            | MatrixOperator::ConjugateTranspose(_)
            | MatrixOperator::Trace(_)
            | MatrixOperator::Rank(_)
            | MatrixOperator::Cofactor(_)
            | MatrixOperator::InnerProduct(_)
            | MatrixOperator::EuclideanNorm(_)
            | MatrixOperator::FrobeniusNorm(_) => {
                unreachable!("scalar/foundation operation has no extended callable")
            }
        };
        Ok(Some(MatrixCallableProof {
            operator: operator.clone(),
            function_equal: path,
            well_defined,
            scalar_carrier: if all_real {
                MatrixFunctionScalarCarrierProof::RealOperands(real_proofs)
            } else {
                MatrixFunctionScalarCarrierProof::ComplexInput
            },
            function: AnonymousFn {
                body: signature,
                equal_to: Box::new(body),
            },
        }))
    }

    pub(crate) fn finite_vector_signature(&mut self, scalar: StandardSet, n: &Obj) -> FnSet {
        let k = self.fresh_internal_param();
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![k],
                    param_type: Box::new(index_set(n)),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(Obj::StandardSet(scalar)),
        }
    }

    fn matrix_real_operand(
        &mut self,
        element: &Obj,
        set: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixRealOperandProof>> {
        let signature = self.function_space_signature(set);
        let canonical = signature
            .as_ref()
            .map(|s| Obj::FunctionSpace(FunctionSpace::FnSet(s.clone())))
            .unwrap_or_else(|| set.clone());
        let fact: Fact = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: canonical,
            line_file: None,
        })
        .into();
        let proof = self.verify_fact(&fact, state)?;
        if !proof.is_failed() {
            return Ok(Some(MatrixRealOperandProof::Membership(Box::new(proof))));
        }
        let Some(signature) = signature else {
            return Ok(None);
        };
        if !signature.dom_facts.is_empty() || signature.set_bound_parameters.groups.len() != 1 {
            return Ok(None);
        }
        let group = &signature.set_bound_parameters.groups[0];
        if group.params.len() != 1 {
            return Ok(None);
        }
        let Obj::SetFormer(SetFormer::ClosedRange(domain)) = group.param_type.as_ref() else {
            return Ok(None);
        };
        if natural_literal(&domain.start) != Some(1) {
            return Ok(None);
        }
        let Some(n) = natural_literal(&domain.end) else {
            return Ok(None);
        };
        for source in self.known_literal_tuple_candidates(element) {
            if source.value.args.len() as i64 != n {
                continue;
            }
            let mut coordinates = Vec::new();
            let mut all_real = true;
            for value in &source.value.args {
                let fact: Fact = AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: value.as_ref().clone(),
                    set: Obj::StandardSet(StandardSet::R),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&fact, state)?;
                if proof.is_failed() {
                    all_real = false;
                    break;
                }
                coordinates.push(proof);
            }
            if all_real {
                return Ok(Some(MatrixRealOperandProof::FiniteCoordinates(
                    MatrixRealCoordinatesProof {
                        source,
                        coordinates,
                    },
                )));
            }
        }
        Ok(None)
    }

    pub(crate) fn matrix_product_entry(
        &mut self,
        left: &Obj,
        right: &Obj,
        inner: &Obj,
        row: Obj,
        col: Obj,
    ) -> Obj {
        let k = self.fresh_internal_param();
        let j = matrix_identifier(&k);
        let term = mul(
            matrix_call(left, vec![row, j.clone()]),
            matrix_call(right, vec![j, col]),
        );
        finite_sum(
            index_set(inner),
            anonymous(
                vec![(k, index_set(inner))],
                Obj::StandardSet(StandardSet::C),
                term,
            ),
        )
    }

    pub(crate) fn extended_matrix_scalar_definition(
        &mut self,
        operator: &MatrixOperator,
    ) -> Option<Obj> {
        match operator {
            MatrixOperator::Cofactor(x) => {
                if let (Some(n), Some(row), Some(col)) = (
                    natural_literal(&x.order),
                    natural_literal(&x.row),
                    natural_literal(&x.col),
                ) {
                    if n > 0
                        && row > 0
                        && row <= n
                        && col > 0
                        && col <= n
                        && n <= crate::execute::execute_eval_stmt::helper::MAX_AGGREGATE_TERMS
                            as i64
                    {
                        let rows: Vec<_> = (1..=n).filter(|r| *r != row).collect();
                        let cols: Vec<_> = (1..=n).filter(|c| *c != col).collect();
                        let mut budget =
                            crate::execute::execute_eval_stmt::helper::MAX_AGGREGATE_TERMS;
                        let value = determinant_formula(&x.matrix, &rows, &cols, &mut budget)?;
                        return Some(if (row + col) % 2 == 0 {
                            value
                        } else {
                            neg(value)
                        });
                    }
                }
                Some(mul(
                    pow(
                        matrix_number(-1),
                        add(x.row.as_ref().clone(), x.col.as_ref().clone()),
                    ),
                    determinant(
                        Obj::MatrixOperator(MatrixOperator::Minor(MatrixMinor {
                            matrix: x.matrix.clone(),
                            order: x.order.clone(),
                            row: x.row.clone(),
                            col: x.col.clone(),
                        })),
                        sub(x.order.as_ref().clone(), matrix_number(1)),
                    ),
                ))
            }
            MatrixOperator::InnerProduct(x) => {
                let k = self.fresh_internal_param();
                let j = matrix_identifier(&k);
                let body = mul(
                    conjugate(matrix_call(&x.left, vec![j.clone()])),
                    matrix_call(&x.right, vec![j]),
                );
                Some(finite_sum(
                    index_set(&x.dimension),
                    anonymous(
                        vec![(k, index_set(&x.dimension))],
                        Obj::StandardSet(StandardSet::C),
                        body,
                    ),
                ))
            }
            MatrixOperator::EuclideanNorm(x) => {
                let k = self.fresh_internal_param();
                let j = matrix_identifier(&k);
                let body = pow(modulus(matrix_call(&x.vector, vec![j])), matrix_number(2));
                Some(sqrt(finite_sum(
                    index_set(&x.dimension),
                    anonymous(
                        vec![(k, index_set(&x.dimension))],
                        Obj::StandardSet(StandardSet::R),
                        body,
                    ),
                )))
            }
            MatrixOperator::FrobeniusNorm(x) => {
                let r = self.fresh_internal_param();
                let c = self.fresh_internal_param();
                let entry = matrix_call(
                    &x.matrix,
                    vec![matrix_identifier(&r), matrix_identifier(&c)],
                );
                let inner = finite_sum(
                    index_set(&x.cols),
                    anonymous(
                        vec![(c, index_set(&x.cols))],
                        Obj::StandardSet(StandardSet::R),
                        pow(modulus(entry), matrix_number(2)),
                    ),
                );
                Some(sqrt(finite_sum(
                    index_set(&x.rows),
                    anonymous(
                        vec![(r, index_set(&x.rows))],
                        Obj::StandardSet(StandardSet::R),
                        inner,
                    ),
                )))
            }
            MatrixOperator::Determinant(_)
            | MatrixOperator::ZeroMatrix(_)
            | MatrixOperator::IdentityMatrix(_)
            | MatrixOperator::Transpose(_)
            | MatrixOperator::ConjugateTranspose(_)
            | MatrixOperator::Trace(_)
            | MatrixOperator::Add(_)
            | MatrixOperator::Subtract(_)
            | MatrixOperator::Scale(_)
            | MatrixOperator::Multiply(_)
            | MatrixOperator::Apply(_)
            | MatrixOperator::Power(_)
            | MatrixOperator::Inverse(_)
            | MatrixOperator::Rank(_)
            | MatrixOperator::Minor(_)
            | MatrixOperator::Adjugate(_)
            | MatrixOperator::Diagonal(_)
            | MatrixOperator::OuterProduct(_) => None,
        }
    }
}

pub enum ExtendedMatrixScalarMembershipProof {
    Rank(MatrixRankScalarProof),
    Cofactor(MatrixCofactorScalarProof),
    InnerProduct(FiniteInnerProductScalarProof),
    EuclideanNorm(EuclideanNormScalarProof),
    FrobeniusNorm(MatrixFrobeniusNormScalarProof),
}
pub struct MatrixRankScalarProof {
    pub target: StandardSet,
}
pub struct MatrixCofactorScalarProof {
    pub carrier: MatrixScalarCarrierProof,
}
pub struct FiniteInnerProductScalarProof {
    pub carrier: MatrixScalarCarrierProof,
}
pub struct EuclideanNormScalarProof {
    pub target: StandardSet,
}
pub struct MatrixFrobeniusNormScalarProof {
    pub target: StandardSet,
}
pub enum MatrixScalarCarrierProof {
    StandardSubset,
    RealInputs(Vec<MatrixRealOperandProof>),
}

pub enum MatrixRealOperandProof {
    Membership(Box<VerifyFactResult>),
    FiniteCoordinates(MatrixRealCoordinatesProof),
}
pub struct MatrixRealCoordinatesProof {
    pub source: super::known_tuple::KnownTupleValueProof,
    pub coordinates: Vec<VerifyFactResult>,
}

pub(crate) fn index_set(n: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(matrix_number(1)),
        end: Box::new(n.clone()),
    }))
}
pub(crate) fn vector_space(scalar: StandardSet, n: Obj) -> Obj {
    Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(Obj::StandardSet(scalar)),
        n: Box::new(n),
    }))
}
fn real_matrix(a: &Obj, m: &Obj, n: &Obj) -> (Obj, Obj) {
    (
        a.clone(),
        matrix_space(Obj::StandardSet(StandardSet::R), m.clone(), n.clone()),
    )
}
fn real_vector(v: &Obj, n: &Obj) -> (Obj, Obj) {
    (v.clone(), vector_space(StandardSet::R, n.clone()))
}
pub(crate) fn anonymous(params: Vec<(BoundName, Obj)>, ret: Obj, body: Obj) -> Obj {
    Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        body: FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: params
                    .into_iter()
                    .map(|(name, set)| SetBoundParameterGroup {
                        params: vec![name],
                        param_type: Box::new(set),
                    })
                    .collect(),
            },
            dom_facts: vec![],
            ret_set: Box::new(ret),
        },
        equal_to: Box::new(body),
    }))
}
pub(crate) fn add(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
pub(crate) fn sub(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
pub(crate) fn mul(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
pub(crate) fn div(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
pub(crate) fn pow(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(exponent),
    }))
}
pub(crate) fn neg(arg: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) }))
}
pub(crate) fn sqrt(arg: Obj) -> Obj {
    Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: Box::new(arg) }))
}
pub(crate) fn conjugate(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate { arg: Box::new(arg) }))
}
pub(crate) fn modulus(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs {
        arg: Box::new(arg),
    }))
}
pub(crate) fn determinant(matrix: Obj, order: Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Determinant(Determinant {
        matrix: Box::new(matrix),
        order: Box::new(order),
    }))
}
pub(crate) fn identity(order: Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::IdentityMatrix(IdentityMatrix {
        order: Box::new(order),
    }))
}
pub(crate) fn matrix_multiply(left: Obj, right: Obj, rows: Obj, inner: Obj, cols: Obj) -> Obj {
    Obj::MatrixOperator(MatrixOperator::Multiply(MatrixMultiply {
        left: Box::new(left),
        right: Box::new(right),
        rows: Box::new(rows),
        inner: Box::new(inner),
        cols: Box::new(cols),
    }))
}
pub(crate) fn finite_sum(set: Obj, func: Obj) -> Obj {
    Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(SumOfFiniteSet {
        set: Box::new(set),
        func: Box::new(func),
    }))
}
fn delta(r: Obj, c: Obj) -> Obj {
    Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
        set: Box::new(Obj::SetOperator(SetOperator::Intersect(Intersect {
            left: Box::new(singleton(r)),
            right: Box::new(singleton(c)),
        }))),
    }))
}
fn singleton(value: Obj) -> Obj {
    Obj::SetFormer(SetFormer::ListSet(ListSet {
        list: vec![Box::new(value)],
    }))
}
fn skip_index(index: Obj, deleted: &Obj, n: &Obj) -> Obj {
    // For 1<=index<n and 1<=deleted<=n, this floor is exactly
    // the indicator index>=deleted. Minor WD already requires n>0.
    let indicator = Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
        arg: Box::new(div(
            sub(add(index.clone(), n.clone()), deleted.clone()),
            n.clone(),
        )),
    }));
    add(index, indicator)
}
pub(crate) fn natural_literal(value: &Obj) -> Option<i64> {
    let value = crate::rational_expression::exact_rational::EvalRational::from_obj(value)?
        .to_i128_if_integer()?;
    if value < 0 {
        return None;
    }
    i64::try_from(value).ok()
}
pub(crate) fn determinant_formula(
    matrix: &Obj,
    rows: &[i64],
    cols: &[i64],
    budget: &mut usize,
) -> Option<Obj> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    if rows.is_empty() {
        return Some(matrix_number(1));
    }
    if rows.len() == 1 {
        return Some(matrix_call(
            matrix,
            vec![matrix_number(rows[0]), matrix_number(cols[0])],
        ));
    }
    let mut result = None;
    for (i, col) in cols.iter().enumerate() {
        let remaining: Vec<_> = cols
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, c)| *c)
            .collect();
        let term = mul(
            matrix_call(matrix, vec![matrix_number(rows[0]), matrix_number(*col)]),
            determinant_formula(matrix, &rows[1..], &remaining, budget)?,
        );
        result = Some(match result {
            None => term,
            Some(previous) => {
                if i % 2 == 0 {
                    add(previous, term)
                } else {
                    sub(previous, term)
                }
            }
        });
    }
    result
}
