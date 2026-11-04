//! Bounded, goal-shaped consequences of the existing finite matrix contracts.
//! No theorem execution, witness search, fact publication or permission reset.
use super::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::prepare_matrices;
use crate::prelude::*;

impl Runtime {
    // Examples: rank(A)<=m; 0<=norm(v); a known inverse candidate selects inv(A).
    // The owning fact dispatcher has checked goal WD and lowered child permissions.
    pub(crate) fn search_native_matrix_property(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<NativeMatrixPropertyProof>> {
        for (kind, arguments) in matrix_property_candidates(goal) {
            let Ok((mut requirements, conclusions)) =
                prepare_matrices(self, kind.theorem(), &arguments)?
            else {
                continue;
            };
            let Some(schema) = conclusions.get(kind.conclusion_index()) else {
                continue;
            };
            let mut conclusion = match schema {
                Fact::AtomicFact(atomic) => atomic.clone(),
                Fact::ForallFact(conditional)
                    if conditional.typed_parameters.groups.is_empty()
                        && conditional.dom_facts.len() == 1
                        && conditional.then_facts.len() == 1 =>
                {
                    let ExistOrAndChainAtomicFact::AtomicFact(atomic) = &conditional.then_facts[0]
                    else {
                        continue;
                    };
                    requirements.extend(conditional.dom_facts.iter().cloned());
                    atomic.clone()
                }
                _ => continue,
            };
            // The triangle rule also accepts the natural unweighted sum. Its
            // complete binder/domain and two coefficient-one terms are checked
            // against the original schema before replacing the representation.
            let mut sum_form = MatrixPropertySumForm::Original;
            if kind == MatrixPropertyKind::EuclideanTriangle {
                if let (AtomicFact::LessEqualFact(wanted), AtomicFact::LessEqualFact(produced)) =
                    (goal, &mut conclusion)
                {
                    if let (
                        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(wanted_norm)),
                        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(produced_norm)),
                    ) = (&wanted.left, &mut produced.left)
                    {
                        if matrix_property_natural_sum_matches(
                            &produced_norm.vector,
                            &wanted_norm.vector,
                            &arguments,
                        ) {
                            sum_form = MatrixPropertySumForm::Natural {
                                original: (*produced_norm.vector).clone(),
                                natural: (*wanted_norm.vector).clone(),
                            };
                            produced_norm.vector = wanted_norm.vector.clone();
                        }
                    }
                }
            }
            let Some(matching) = self.match_matrix_property_goal(&conclusion, goal) else {
                continue;
            };
            let mut requirement_proofs = Vec::new();
            for requirement in &requirements {
                let checked = self.verify_builtin_rule_premise(requirement, state)?;
                if !checked.is_failed() {
                    requirement_proofs.push(MatrixPropertyRequirementProof::Verified(checked));
                    continue;
                }
                // A stored v=zero(k) may need a final structural alpha step to
                // the contract's fresh zero(j). Keep both proofs; do not scan
                // arbitrary graph endpoints or reopen Strategy in this child.
                if kind == MatrixPropertyKind::EuclideanZeroIntro {
                    if let Some(proof) = self.matrix_zero_alpha_requirement(requirement, state)? {
                        requirement_proofs.push(proof);
                        continue;
                    }
                }
                break;
            }
            if requirement_proofs.len() != requirements.len() {
                continue;
            }
            let application = MatrixPropertyApplicationProof {
                arguments,
                schema: schema.clone(),
                sum_form,
                conclusion,
                matching,
                requirements,
                requirement_proofs,
            };
            return Ok(Some(kind.proof(application)));
        }
        Ok(None)
    }

    fn match_matrix_property_goal(
        &mut self,
        source: &AtomicFact,
        goal: &AtomicFact,
    ) -> Option<MatrixPropertyGoalMatchProof> {
        let equal = matches!(
            (source, goal),
            (AtomicFact::EqualFact(_), AtomicFact::EqualFact(_))
        );
        if std::mem::discriminant(source) != std::mem::discriminant(goal) {
            return None;
        }
        let source_args = crate::ast::fact::atomic_fact_args_ref(source);
        let goal_args = crate::ast::fact::atomic_fact_args_ref(goal);
        if source_args.len() != goal_args.len() {
            return None;
        }
        for reversed in [false, true] {
            if reversed && !equal {
                break;
            }
            let mut comparisons = Vec::new();
            for (index, wanted) in goal_args.iter().enumerate() {
                let supplied = source_args[if reversed { 1 - index } else { index }];
                let comparison = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: supplied.clone(),
                    right: (*wanted).clone(),
                    line_file: None,
                };
                let Some(proof) = self.search_equal_fact_proof_directly(&comparison) else {
                    break;
                };
                comparisons.push(proof);
            }
            if comparisons.len() == goal_args.len() {
                return Some(MatrixPropertyGoalMatchProof {
                    reversed,
                    comparisons,
                });
            }
        }
        None
    }

    fn matrix_zero_alpha_requirement(
        &mut self,
        requirement: &Fact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixPropertyRequirementProof>> {
        let Fact::AtomicFact(AtomicFact::EqualFact(target)) = requirement else {
            return Ok(None);
        };
        for (value, _) in self
            .exact_property_object_values(&target.left)
            .into_iter()
            .take(16)
        {
            let comparison = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: value.clone(),
                right: target.right.clone(),
                line_file: None,
            };
            let Some(alpha) = search_equal_fact_proof_by_they_are_the_same(&comparison) else {
                continue;
            };
            let source: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: target.left.clone(),
                right: value,
                line_file: None,
            }
            .into();
            let proof = self.verify_builtin_rule_premise(&source, state)?;
            if !proof.is_failed() {
                return Ok(Some(MatrixPropertyRequirementProof::ZeroVectorAlpha {
                    source: proof,
                    comparison,
                    alpha,
                }));
            }
        }
        Ok(None)
    }
}

pub struct MatrixPropertyApplicationProof {
    pub arguments: Vec<Obj>,
    pub schema: Fact,
    pub sum_form: MatrixPropertySumForm,
    pub conclusion: AtomicFact,
    pub matching: MatrixPropertyGoalMatchProof,
    pub requirements: Vec<Fact>,
    pub requirement_proofs: Vec<MatrixPropertyRequirementProof>,
}
pub enum MatrixPropertySumForm {
    Original,
    Natural { original: Obj, natural: Obj },
}
pub struct MatrixPropertyGoalMatchProof {
    pub reversed: bool,
    pub comparisons: Vec<EqualFactSearchedProof>,
}
pub enum MatrixPropertyRequirementProof {
    Verified(VerifyFactResult),
    ZeroVectorAlpha {
        source: VerifyFactResult,
        comparison: EqualFact,
        alpha: TheyAreTheSameProof,
    },
}

// The fixed root and its immediate children select at most five contracts.
fn matrix_property_candidates(goal: &AtomicFact) -> Vec<(MatrixPropertyKind, Vec<Obj>)> {
    use MatrixOperator as M;
    use MatrixPropertyKind as K;
    let mut out = Vec::new();
    let (left, right) = match goal {
        AtomicFact::InFact(f) => {
            if let Some(M::InnerProduct(p)) = matrix_operator(&f.element) {
                out.push((
                    K::InnerSelfReal,
                    vec![(*p.left).clone(), (*p.dimension).clone()],
                ));
            }
            return out;
        }
        AtomicFact::LessEqualFact(f) => {
            if let Some(M::Rank(p)) = matrix_operator(&f.left) {
                let args = vec![(*p.matrix).clone(), (*p.rows).clone(), (*p.cols).clone()];
                out.push((K::RankRows, args.clone()));
                out.push((K::RankCols, args));
                if let Some(M::Multiply(m)) = matrix_operator(&p.matrix) {
                    let args = vec![
                        (*m.left).clone(),
                        (*m.right).clone(),
                        (*m.rows).clone(),
                        (*m.inner).clone(),
                        (*m.cols).clone(),
                    ];
                    out.push((K::RankProductLeft, args.clone()));
                    out.push((K::RankProductRight, args));
                }
            }
            if let Obj::ComplexOperator(ComplexOperator::RealPart(p)) = &f.right {
                if let Some(M::InnerProduct(i)) = matrix_operator(&p.arg) {
                    out.push((
                        K::InnerSelfNonnegative,
                        vec![(*i.left).clone(), (*i.dimension).clone()],
                    ));
                }
            }
            match matrix_operator(&f.right) {
                Some(M::EuclideanNorm(p)) => out.push((
                    K::EuclideanNonnegative,
                    vec![(*p.vector).clone(), (*p.dimension).clone()],
                )),
                Some(M::FrobeniusNorm(p)) => out.push((
                    K::FrobeniusNonnegative,
                    vec![(*p.matrix).clone(), (*p.rows).clone(), (*p.cols).clone()],
                )),
                _ => {}
            }
            if let Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) = &f.left {
                if let Some(M::InnerProduct(i)) = matrix_operator(&p.arg) {
                    out.push((
                        K::CauchySchwarz,
                        vec![
                            (*i.left).clone(),
                            (*i.right).clone(),
                            (*i.dimension).clone(),
                        ],
                    ));
                }
            }
            match matrix_operator(&f.left) {
                Some(M::EuclideanNorm(p)) => {
                    if let Some((a, b)) = vector_sum_form(&p.vector, false)
                        .or_else(|| vector_sum_form(&p.vector, true))
                    {
                        out.push((K::EuclideanTriangle, vec![a, b, (*p.dimension).clone()]));
                    }
                }
                Some(M::FrobeniusNorm(p)) => {
                    if let Some(M::Add(a)) = matrix_operator(&p.matrix) {
                        out.push((
                            K::FrobeniusTriangle,
                            vec![
                                (*a.left).clone(),
                                (*a.right).clone(),
                                (*p.rows).clone(),
                                (*p.cols).clone(),
                            ],
                        ));
                    }
                }
                _ => {}
            }
            return out;
        }
        AtomicFact::EqualFact(f) => (&f.left, &f.right),
        _ => return out,
    };
    for (root, other) in [(left, right), (right, left)] {
        if let Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) = root {
            if let Some(M::InnerProduct(i)) = matrix_operator(&p.arg) {
                out.push((
                    K::InnerSelfImaginary,
                    vec![(*i.left).clone(), (*i.dimension).clone()],
                ));
            }
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = root {
            match matrix_operator(&p.base) {
                Some(M::EuclideanNorm(n)) => out.push((
                    K::EuclideanSquareSum,
                    vec![(*n.vector).clone(), (*n.dimension).clone()],
                )),
                Some(M::FrobeniusNorm(n)) => out.push((
                    K::FrobeniusSquareSum,
                    vec![(*n.matrix).clone(), (*n.rows).clone(), (*n.cols).clone()],
                )),
                _ => {}
            }
        }
        if let Some(n) = zero_vector_dimension(root) {
            out.push((K::EuclideanZeroElim, vec![other.clone(), n]));
        }
        match matrix_operator(root) {
            Some(M::InnerProduct(p)) => {
                if let Some(M::Apply(a)) = matrix_operator(&p.left) {
                    out.push((
                        K::ApplyAdjoint,
                        vec![
                            (*a.matrix).clone(),
                            (*a.vector).clone(),
                            (*p.right).clone(),
                            (*a.rows).clone(),
                            (*a.cols).clone(),
                        ],
                    ));
                }
                if let Some((a, v, b, w)) = vector_combination_form(&p.right) {
                    out.push((
                        K::InnerLinearRight,
                        vec![(*p.left).clone(), v, w, a, b, (*p.dimension).clone()],
                    ));
                }
            }
            Some(M::EuclideanNorm(p)) => {
                out.push((
                    K::EuclideanZeroIntro,
                    vec![(*p.vector).clone(), (*p.dimension).clone()],
                ));
                if let Some((z, v)) = vector_scale_form(&p.vector) {
                    out.push((K::EuclideanScale, vec![z, v, (*p.dimension).clone()]));
                }
            }
            Some(M::FrobeniusNorm(p)) => out.push((
                K::FrobeniusZeroIntro,
                vec![(*p.matrix).clone(), (*p.rows).clone(), (*p.cols).clone()],
            )),
            Some(M::ZeroMatrix(p)) => out.push((
                K::FrobeniusZeroElim,
                vec![other.clone(), (*p.rows).clone(), (*p.cols).clone()],
            )),
            Some(M::Determinant(p)) => match other {
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => {
                    let args = vec![(*p.matrix).clone(), (*p.order).clone()];
                    out.push((K::DetUpperTriangular, args.clone()));
                    out.push((K::DetLowerTriangular, args));
                }
                Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) => {
                    if let Some(callback) = anonymous_vector(&sum.func) {
                        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(term)) =
                            callback.equal_to.as_ref()
                        {
                            if let Some(M::Cofactor(c)) = matrix_operator(&term.right) {
                                let binder =
                                    callback.body.set_bound_parameters.groups[0].params[0].id;
                                let bound = |o: &Obj| matches!(o, Obj::Identifier(IdentifierObj::Plain {id,..}) if *id==binder);
                                if bound(&c.col) && !bound(&c.row) {
                                    out.push((
                                        K::DetLaplaceRow,
                                        vec![
                                            (*p.matrix).clone(),
                                            (*p.order).clone(),
                                            (*c.row).clone(),
                                        ],
                                    ));
                                }
                                if bound(&c.row) && !bound(&c.col) {
                                    out.push((
                                        K::DetLaplaceColumn,
                                        vec![
                                            (*p.matrix).clone(),
                                            (*p.order).clone(),
                                            (*c.col).clone(),
                                        ],
                                    ));
                                }
                            }
                        }
                    }
                }
                _ => {}
            },
            Some(M::Inverse(p)) => out.push((
                K::InverseFromCandidate,
                vec![(*p.matrix).clone(), other.clone(), (*p.order).clone()],
            )),
            _ => {}
        }
    }
    out
}

// Replay validates a recorded selection; this pure check performs no searches,
// state mutation, premise verification or alternate proof selection.
pub(crate) fn matrix_property_selection_matches(
    kind: MatrixPropertyKind,
    arguments: &[Obj],
    conclusion: &AtomicFact,
) -> bool {
    matrix_property_candidates(conclusion)
        .iter()
        .any(|(selected, actual)| *selected == kind && actual == arguments)
}

pub(crate) fn matrix_property_natural_sum_matches(
    original: &Obj,
    natural: &Obj,
    arguments: &[Obj],
) -> bool {
    let [a, b, _] = arguments else {
        return false;
    };
    let (Some((old_a, old_b)), Some((new_a, new_b))) = (
        vector_sum_form(original, true),
        vector_sum_form(natural, false),
    ) else {
        return false;
    };
    old_a == *a
        && old_b == *b
        && new_a == *a
        && new_b == *b
        && same_vector_signature(original, natural)
}

fn matrix_operator(object: &Obj) -> Option<&MatrixOperator> {
    if let Obj::MatrixOperator(operator) = object {
        Some(operator)
    } else {
        None
    }
}
fn anonymous_vector(object: &Obj) -> Option<&AnonymousFn> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = object else {
        return None;
    };
    let [group] = f.body.set_bound_parameters.groups.as_slice() else {
        return None;
    };
    if group.params.len() != 1
        || !f.body.dom_facts.is_empty()
        || *f.body.ret_set != Obj::StandardSet(StandardSet::C)
    {
        return None;
    }
    Some(f)
}
fn same_vector_signature(left: &Obj, right: &Obj) -> bool {
    let (Some(l), Some(r)) = (anonymous_vector(left), anonymous_vector(right)) else {
        return false;
    };
    crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
        &l.body, &r.body,
    )
}
fn called_vector(object: &Obj, binder: &crate::ast::names::BoundName) -> Option<Obj> {
    let Obj::FnObj(call) = object else {
        return None;
    };
    let [args] = call.body.as_slice() else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    if !matches!(arg.as_ref(),Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==binder.id) {
        return None;
    }
    Some(match call.head.as_ref() {
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(f) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
        }
        FnObjHead::FieldAccess(f) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(f.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(f) => Obj::InstantiatedTemplateObj(f.clone()),
        FnObjHead::Object(object) => (*object.as_ref()).clone(),
    })
}
fn vector_scale_form(object: &Obj) -> Option<(Obj, Obj)> {
    let f = anonymous_vector(object)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = f.equal_to.as_ref() else {
        return None;
    };
    Some((
        (*product.left).clone(),
        called_vector(
            &product.right,
            &f.body.set_bound_parameters.groups[0].params[0],
        )?,
    ))
}
fn vector_combination_form(object: &Obj) -> Option<(Obj, Obj, Obj, Obj)> {
    let f = anonymous_vector(object)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = f.equal_to.as_ref() else {
        return None;
    };
    let (
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(l)),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(r)),
    ) = (sum.left.as_ref(), sum.right.as_ref())
    else {
        return None;
    };
    let binder = &f.body.set_bound_parameters.groups[0].params[0];
    Some((
        (*l.left).clone(),
        called_vector(&l.right, binder)?,
        (*r.left).clone(),
        called_vector(&r.right, binder)?,
    ))
}
fn vector_sum_form(object: &Obj, weighted: bool) -> Option<(Obj, Obj)> {
    if weighted {
        let (a, u, b, v) = vector_combination_form(object)?;
        if a.ir()
            != Obj::Literal(Literal::Number(Number {
                normalized_value: "1".into(),
            }))
            .ir()
            || a.ir() != b.ir()
        {
            return None;
        }
        return Some((u, v));
    }
    let f = anonymous_vector(object)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = f.equal_to.as_ref() else {
        return None;
    };
    let binder = &f.body.set_bound_parameters.groups[0].params[0];
    Some((
        called_vector(&sum.left, binder)?,
        called_vector(&sum.right, binder)?,
    ))
}
fn zero_vector_dimension(object: &Obj) -> Option<Obj> {
    let f = anonymous_vector(object)?;
    if !matches!(f.equal_to.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="0") {
        return None;
    }
    let Obj::SetFormer(SetFormer::ClosedRange(range)) =
        f.body.set_bound_parameters.groups[0].param_type.as_ref()
    else {
        return None;
    };
    if !matches!(range.start.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="1") {
        return None;
    }
    Some((*range.end).clone())
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MatrixPropertyKind {
    RankRows,
    RankCols,
    RankProductLeft,
    RankProductRight,
    InnerSelfReal,
    InnerSelfNonnegative,
    InnerSelfImaginary,
    EuclideanNonnegative,
    FrobeniusNonnegative,
    CauchySchwarz,
    EuclideanScale,
    EuclideanTriangle,
    InnerLinearRight,
    FrobeniusTriangle,
    EuclideanZeroElim,
    EuclideanZeroIntro,
    FrobeniusZeroElim,
    FrobeniusZeroIntro,
    EuclideanSquareSum,
    FrobeniusSquareSum,
    ApplyAdjoint,
    InverseFromCandidate,
    DetLowerTriangular,
    DetUpperTriangular,
    DetLaplaceColumn,
    DetLaplaceRow,
}

pub enum NativeMatrixPropertyProof {
    RankRows(RankRowsMatrixPropertyProof),
    RankCols(RankColsMatrixPropertyProof),
    RankProductLeft(RankProductLeftMatrixPropertyProof),
    RankProductRight(RankProductRightMatrixPropertyProof),
    InnerSelfReal(InnerSelfRealMatrixPropertyProof),
    InnerSelfNonnegative(InnerSelfNonnegativeMatrixPropertyProof),
    InnerSelfImaginary(InnerSelfImaginaryMatrixPropertyProof),
    EuclideanNonnegative(EuclideanNonnegativeMatrixPropertyProof),
    FrobeniusNonnegative(FrobeniusNonnegativeMatrixPropertyProof),
    CauchySchwarz(CauchySchwarzMatrixPropertyProof),
    EuclideanScale(EuclideanScaleMatrixPropertyProof),
    EuclideanTriangle(EuclideanTriangleMatrixPropertyProof),
    InnerLinearRight(InnerLinearRightMatrixPropertyProof),
    FrobeniusTriangle(FrobeniusTriangleMatrixPropertyProof),
    EuclideanZeroElim(EuclideanZeroElimMatrixPropertyProof),
    EuclideanZeroIntro(EuclideanZeroIntroMatrixPropertyProof),
    FrobeniusZeroElim(FrobeniusZeroElimMatrixPropertyProof),
    FrobeniusZeroIntro(FrobeniusZeroIntroMatrixPropertyProof),
    EuclideanSquareSum(EuclideanSquareSumMatrixPropertyProof),
    FrobeniusSquareSum(FrobeniusSquareSumMatrixPropertyProof),
    ApplyAdjoint(ApplyAdjointMatrixPropertyProof),
    InverseFromCandidate(InverseFromCandidateMatrixPropertyProof),
    DetLowerTriangular(DetLowerTriangularMatrixPropertyProof),
    DetUpperTriangular(DetUpperTriangularMatrixPropertyProof),
    DetLaplaceColumn(DetLaplaceColumnMatrixPropertyProof),
    DetLaplaceRow(DetLaplaceRowMatrixPropertyProof),
}
pub struct RankRowsMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct RankColsMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct RankProductLeftMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct RankProductRightMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct InnerSelfRealMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct InnerSelfNonnegativeMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct InnerSelfImaginaryMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanNonnegativeMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct FrobeniusNonnegativeMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct CauchySchwarzMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanScaleMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanTriangleMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct InnerLinearRightMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct FrobeniusTriangleMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanZeroElimMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanZeroIntroMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct FrobeniusZeroElimMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct FrobeniusZeroIntroMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct EuclideanSquareSumMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct FrobeniusSquareSumMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct ApplyAdjointMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct InverseFromCandidateMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct DetLaplaceRowMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct DetLaplaceColumnMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct DetUpperTriangularMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
pub struct DetLowerTriangularMatrixPropertyProof {
    pub application: MatrixPropertyApplicationProof,
}
impl MatrixPropertyKind {
    pub fn theorem(self) -> BuiltinTheoremId {
        match self {
            Self::DetLaplaceRow => BuiltinTheoremId::MatrixDetLaplaceRow,
            Self::DetLaplaceColumn => BuiltinTheoremId::MatrixDetLaplaceColumn,
            Self::DetUpperTriangular => BuiltinTheoremId::MatrixDetUpperTriangular,
            Self::DetLowerTriangular => BuiltinTheoremId::MatrixDetLowerTriangular,
            Self::RankRows => BuiltinTheoremId::MatrixRankBounds,
            Self::RankCols => BuiltinTheoremId::MatrixRankBounds,
            Self::RankProductLeft => BuiltinTheoremId::MatrixRankProduct,
            Self::RankProductRight => BuiltinTheoremId::MatrixRankProduct,
            Self::InnerSelfReal => BuiltinTheoremId::InnerProductPositive,
            Self::InnerSelfNonnegative => BuiltinTheoremId::InnerProductPositive,
            Self::InnerSelfImaginary => BuiltinTheoremId::InnerProductPositive,
            Self::EuclideanNonnegative => BuiltinTheoremId::EuclideanNormSquare,
            Self::FrobeniusNonnegative => BuiltinTheoremId::FrobeniusNormSquare,
            Self::CauchySchwarz => BuiltinTheoremId::InnerProductCauchySchwarz,
            Self::EuclideanScale => BuiltinTheoremId::EuclideanNormScale,
            Self::EuclideanTriangle => BuiltinTheoremId::EuclideanNormTriangle,
            Self::InnerLinearRight => BuiltinTheoremId::InnerProductLinearRight,
            Self::FrobeniusTriangle => BuiltinTheoremId::FrobeniusNormTriangle,
            Self::EuclideanZeroElim => BuiltinTheoremId::EuclideanNormZero,
            Self::EuclideanZeroIntro => BuiltinTheoremId::EuclideanNormZero,
            Self::FrobeniusZeroElim => BuiltinTheoremId::FrobeniusNormZero,
            Self::FrobeniusZeroIntro => BuiltinTheoremId::FrobeniusNormZero,
            Self::EuclideanSquareSum => BuiltinTheoremId::EuclideanNormSquare,
            Self::FrobeniusSquareSum => BuiltinTheoremId::FrobeniusNormSquare,
            Self::ApplyAdjoint => BuiltinTheoremId::MatrixInnerProductAdjoint,
            Self::InverseFromCandidate => BuiltinTheoremId::MatrixInverseFromCandidate,
        }
    }
    pub fn conclusion_index(self) -> usize {
        match self {
            Self::DetLaplaceRow => 0,
            Self::DetLaplaceColumn => 0,
            Self::DetUpperTriangular => 0,
            Self::DetLowerTriangular => 0,
            Self::RankRows => 1,
            Self::RankCols => 2,
            Self::RankProductLeft => 0,
            Self::RankProductRight => 1,
            Self::InnerSelfReal => 0,
            Self::InnerSelfNonnegative => 1,
            Self::InnerSelfImaginary => 2,
            Self::EuclideanNonnegative => 2,
            Self::FrobeniusNonnegative => 1,
            Self::CauchySchwarz => 0,
            Self::EuclideanScale => 0,
            Self::EuclideanTriangle => 0,
            Self::InnerLinearRight => 0,
            Self::FrobeniusTriangle => 0,
            Self::EuclideanZeroElim => 0,
            Self::EuclideanZeroIntro => 1,
            Self::FrobeniusZeroElim => 0,
            Self::FrobeniusZeroIntro => 1,
            Self::EuclideanSquareSum => 0,
            Self::FrobeniusSquareSum => 0,
            Self::ApplyAdjoint => 0,
            Self::InverseFromCandidate => 0,
        }
    }
    fn proof(self, application: MatrixPropertyApplicationProof) -> NativeMatrixPropertyProof {
        match self {
            Self::DetLaplaceRow => {
                NativeMatrixPropertyProof::DetLaplaceRow(DetLaplaceRowMatrixPropertyProof {
                    application,
                })
            }
            Self::DetLaplaceColumn => {
                NativeMatrixPropertyProof::DetLaplaceColumn(DetLaplaceColumnMatrixPropertyProof {
                    application,
                })
            }
            Self::DetUpperTriangular => NativeMatrixPropertyProof::DetUpperTriangular(
                DetUpperTriangularMatrixPropertyProof { application },
            ),
            Self::DetLowerTriangular => NativeMatrixPropertyProof::DetLowerTriangular(
                DetLowerTriangularMatrixPropertyProof { application },
            ),
            Self::RankRows => {
                NativeMatrixPropertyProof::RankRows(RankRowsMatrixPropertyProof { application })
            }
            Self::RankCols => {
                NativeMatrixPropertyProof::RankCols(RankColsMatrixPropertyProof { application })
            }
            Self::RankProductLeft => {
                NativeMatrixPropertyProof::RankProductLeft(RankProductLeftMatrixPropertyProof {
                    application,
                })
            }
            Self::RankProductRight => {
                NativeMatrixPropertyProof::RankProductRight(RankProductRightMatrixPropertyProof {
                    application,
                })
            }
            Self::InnerSelfReal => {
                NativeMatrixPropertyProof::InnerSelfReal(InnerSelfRealMatrixPropertyProof {
                    application,
                })
            }
            Self::InnerSelfNonnegative => NativeMatrixPropertyProof::InnerSelfNonnegative(
                InnerSelfNonnegativeMatrixPropertyProof { application },
            ),
            Self::InnerSelfImaginary => NativeMatrixPropertyProof::InnerSelfImaginary(
                InnerSelfImaginaryMatrixPropertyProof { application },
            ),
            Self::EuclideanNonnegative => NativeMatrixPropertyProof::EuclideanNonnegative(
                EuclideanNonnegativeMatrixPropertyProof { application },
            ),
            Self::FrobeniusNonnegative => NativeMatrixPropertyProof::FrobeniusNonnegative(
                FrobeniusNonnegativeMatrixPropertyProof { application },
            ),
            Self::CauchySchwarz => {
                NativeMatrixPropertyProof::CauchySchwarz(CauchySchwarzMatrixPropertyProof {
                    application,
                })
            }
            Self::EuclideanScale => {
                NativeMatrixPropertyProof::EuclideanScale(EuclideanScaleMatrixPropertyProof {
                    application,
                })
            }
            Self::EuclideanTriangle => {
                NativeMatrixPropertyProof::EuclideanTriangle(EuclideanTriangleMatrixPropertyProof {
                    application,
                })
            }
            Self::InnerLinearRight => {
                NativeMatrixPropertyProof::InnerLinearRight(InnerLinearRightMatrixPropertyProof {
                    application,
                })
            }
            Self::FrobeniusTriangle => {
                NativeMatrixPropertyProof::FrobeniusTriangle(FrobeniusTriangleMatrixPropertyProof {
                    application,
                })
            }
            Self::EuclideanZeroElim => {
                NativeMatrixPropertyProof::EuclideanZeroElim(EuclideanZeroElimMatrixPropertyProof {
                    application,
                })
            }
            Self::EuclideanZeroIntro => NativeMatrixPropertyProof::EuclideanZeroIntro(
                EuclideanZeroIntroMatrixPropertyProof { application },
            ),
            Self::FrobeniusZeroElim => {
                NativeMatrixPropertyProof::FrobeniusZeroElim(FrobeniusZeroElimMatrixPropertyProof {
                    application,
                })
            }
            Self::FrobeniusZeroIntro => NativeMatrixPropertyProof::FrobeniusZeroIntro(
                FrobeniusZeroIntroMatrixPropertyProof { application },
            ),
            Self::EuclideanSquareSum => NativeMatrixPropertyProof::EuclideanSquareSum(
                EuclideanSquareSumMatrixPropertyProof { application },
            ),
            Self::FrobeniusSquareSum => NativeMatrixPropertyProof::FrobeniusSquareSum(
                FrobeniusSquareSumMatrixPropertyProof { application },
            ),
            Self::ApplyAdjoint => {
                NativeMatrixPropertyProof::ApplyAdjoint(ApplyAdjointMatrixPropertyProof {
                    application,
                })
            }
            Self::InverseFromCandidate => NativeMatrixPropertyProof::InverseFromCandidate(
                InverseFromCandidateMatrixPropertyProof { application },
            ),
        }
    }
}
impl NativeMatrixPropertyProof {
    pub fn kind(&self) -> MatrixPropertyKind {
        match self {
            Self::DetLaplaceRow(_) => MatrixPropertyKind::DetLaplaceRow,
            Self::DetLaplaceColumn(_) => MatrixPropertyKind::DetLaplaceColumn,
            Self::DetUpperTriangular(_) => MatrixPropertyKind::DetUpperTriangular,
            Self::DetLowerTriangular(_) => MatrixPropertyKind::DetLowerTriangular,
            Self::RankRows(_) => MatrixPropertyKind::RankRows,
            Self::RankCols(_) => MatrixPropertyKind::RankCols,
            Self::RankProductLeft(_) => MatrixPropertyKind::RankProductLeft,
            Self::RankProductRight(_) => MatrixPropertyKind::RankProductRight,
            Self::InnerSelfReal(_) => MatrixPropertyKind::InnerSelfReal,
            Self::InnerSelfNonnegative(_) => MatrixPropertyKind::InnerSelfNonnegative,
            Self::InnerSelfImaginary(_) => MatrixPropertyKind::InnerSelfImaginary,
            Self::EuclideanNonnegative(_) => MatrixPropertyKind::EuclideanNonnegative,
            Self::FrobeniusNonnegative(_) => MatrixPropertyKind::FrobeniusNonnegative,
            Self::CauchySchwarz(_) => MatrixPropertyKind::CauchySchwarz,
            Self::EuclideanScale(_) => MatrixPropertyKind::EuclideanScale,
            Self::EuclideanTriangle(_) => MatrixPropertyKind::EuclideanTriangle,
            Self::InnerLinearRight(_) => MatrixPropertyKind::InnerLinearRight,
            Self::FrobeniusTriangle(_) => MatrixPropertyKind::FrobeniusTriangle,
            Self::EuclideanZeroElim(_) => MatrixPropertyKind::EuclideanZeroElim,
            Self::EuclideanZeroIntro(_) => MatrixPropertyKind::EuclideanZeroIntro,
            Self::FrobeniusZeroElim(_) => MatrixPropertyKind::FrobeniusZeroElim,
            Self::FrobeniusZeroIntro(_) => MatrixPropertyKind::FrobeniusZeroIntro,
            Self::EuclideanSquareSum(_) => MatrixPropertyKind::EuclideanSquareSum,
            Self::FrobeniusSquareSum(_) => MatrixPropertyKind::FrobeniusSquareSum,
            Self::ApplyAdjoint(_) => MatrixPropertyKind::ApplyAdjoint,
            Self::InverseFromCandidate(_) => MatrixPropertyKind::InverseFromCandidate,
        }
    }
    pub fn rule_name(&self) -> &'static str {
        match self {
            Self::DetLaplaceRow(_) => "NativeMatrixDetLaplaceRow",
            Self::DetLaplaceColumn(_) => "NativeMatrixDetLaplaceColumn",
            Self::DetUpperTriangular(_) => "NativeMatrixDetUpperTriangular",
            Self::DetLowerTriangular(_) => "NativeMatrixDetLowerTriangular",
            Self::RankRows(_) => "NativeMatrixRankRows",
            Self::RankCols(_) => "NativeMatrixRankCols",
            Self::RankProductLeft(_) => "NativeMatrixRankProductLeft",
            Self::RankProductRight(_) => "NativeMatrixRankProductRight",
            Self::InnerSelfReal(_) => "NativeMatrixInnerSelfReal",
            Self::InnerSelfNonnegative(_) => "NativeMatrixInnerSelfNonnegative",
            Self::InnerSelfImaginary(_) => "NativeMatrixInnerSelfImaginary",
            Self::EuclideanNonnegative(_) => "NativeMatrixEuclideanNonnegative",
            Self::FrobeniusNonnegative(_) => "NativeMatrixFrobeniusNonnegative",
            Self::CauchySchwarz(_) => "NativeMatrixCauchySchwarz",
            Self::EuclideanScale(_) => "NativeMatrixEuclideanScale",
            Self::EuclideanTriangle(_) => "NativeMatrixEuclideanTriangle",
            Self::InnerLinearRight(_) => "NativeMatrixInnerLinearRight",
            Self::FrobeniusTriangle(_) => "NativeMatrixFrobeniusTriangle",
            Self::EuclideanZeroElim(_) => "NativeMatrixEuclideanZeroElim",
            Self::EuclideanZeroIntro(_) => "NativeMatrixEuclideanZeroIntro",
            Self::FrobeniusZeroElim(_) => "NativeMatrixFrobeniusZeroElim",
            Self::FrobeniusZeroIntro(_) => "NativeMatrixFrobeniusZeroIntro",
            Self::EuclideanSquareSum(_) => "NativeMatrixEuclideanSquareSum",
            Self::FrobeniusSquareSum(_) => "NativeMatrixFrobeniusSquareSum",
            Self::ApplyAdjoint(_) => "NativeMatrixApplyAdjoint",
            Self::InverseFromCandidate(_) => "NativeMatrixInverseFromCandidate",
        }
    }
    pub fn application(&self) -> &MatrixPropertyApplicationProof {
        match self {
            Self::DetLaplaceRow(proof) => &proof.application,
            Self::DetLaplaceColumn(proof) => &proof.application,
            Self::DetUpperTriangular(proof) => &proof.application,
            Self::DetLowerTriangular(proof) => &proof.application,
            Self::RankRows(proof) => &proof.application,
            Self::RankCols(proof) => &proof.application,
            Self::RankProductLeft(proof) => &proof.application,
            Self::RankProductRight(proof) => &proof.application,
            Self::InnerSelfReal(proof) => &proof.application,
            Self::InnerSelfNonnegative(proof) => &proof.application,
            Self::InnerSelfImaginary(proof) => &proof.application,
            Self::EuclideanNonnegative(proof) => &proof.application,
            Self::FrobeniusNonnegative(proof) => &proof.application,
            Self::CauchySchwarz(proof) => &proof.application,
            Self::EuclideanScale(proof) => &proof.application,
            Self::EuclideanTriangle(proof) => &proof.application,
            Self::InnerLinearRight(proof) => &proof.application,
            Self::FrobeniusTriangle(proof) => &proof.application,
            Self::EuclideanZeroElim(proof) => &proof.application,
            Self::EuclideanZeroIntro(proof) => &proof.application,
            Self::FrobeniusZeroElim(proof) => &proof.application,
            Self::FrobeniusZeroIntro(proof) => &proof.application,
            Self::EuclideanSquareSum(proof) => &proof.application,
            Self::FrobeniusSquareSum(proof) => &proof.application,
            Self::ApplyAdjoint(proof) => &proof.application,
            Self::InverseFromCandidate(proof) => &proof.application,
        }
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/execute/native_matrix/properties.rs"]
mod native_matrix_properties_tests;

#[cfg(test)]
#[path = "../../../../tests/unit/execute/native_matrix/determinant_formulas.rs"]
mod native_matrix_determinant_formulas_tests;
