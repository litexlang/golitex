//! Goal-shaped finite matrix laws. No statement execution, rewriting loop or
//! factorization search: at most four root candidates per equality endpoint.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    prepare_matrices, prepare_matrix_trace_add, prepare_matrix_trace_scale,
};
use crate::prelude::*;

impl Runtime {
    // Example: A in matrix(C,m,n) proves matrix_mul(identity_matrix(m),A,m,m,n)=A.
    // The caller has checked both complete objects' WD. Endpoints are matched
    // directly before any domain or nonsingularity premise is searched.
    pub(super) fn search_native_matrix_law(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<NativeMatrixLawProof>> {
        for root in [&fact.left, &fact.right] {
            for (law, arguments) in matrix_law_candidates(root) {
                let (requirements, conclusions) = match law {
                    NativeMatrixLawKind::TraceAdd => prepare_matrix_trace_add(self, &arguments),
                    NativeMatrixLawKind::TraceScale => prepare_matrix_trace_scale(self, &arguments),
                    _ => {
                        let theorem = law.theorem();
                        if arguments.len() != theorem.arity() {
                            continue;
                        }
                        let Ok(contract) = prepare_matrices(self, theorem, &arguments)? else {
                            continue;
                        };
                        contract
                    }
                };
                let Some(Fact::AtomicFact(AtomicFact::EqualFact(conclusion))) =
                    conclusions.get(law.conclusion_index())
                else {
                    continue;
                };
                for orientation in [MatrixLawOrientation::Forward, MatrixLawOrientation::Reverse] {
                    let (left, right) = match orientation {
                        MatrixLawOrientation::Forward => (&conclusion.left, &conclusion.right),
                        MatrixLawOrientation::Reverse => (&conclusion.right, &conclusion.left),
                    };
                    let left_comparison = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: left.clone(),
                        right: fact.left.clone(),
                        line_file: None,
                    };
                    let Some(left_equal) = self.search_equal_fact_proof_directly(&left_comparison)
                    else {
                        continue;
                    };
                    let right_comparison = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: right.clone(),
                        right: fact.right.clone(),
                        line_file: None,
                    };
                    let Some(right_equal) =
                        self.search_equal_fact_proof_directly(&right_comparison)
                    else {
                        continue;
                    };
                    let mut requirement_proofs = Vec::new();
                    for requirement in &requirements {
                        let proof = self.verify_builtin_rule_premise(requirement, state)?;
                        if proof.is_failed() {
                            break;
                        }
                        requirement_proofs.push(proof);
                    }
                    if requirement_proofs.len() != requirements.len() {
                        continue;
                    }
                    let application = MatrixLawApplicationProof {
                        arguments: arguments.clone(),
                        requirements: requirements.clone(),
                        conclusion: conclusion.clone(),
                        orientation,
                        left_equal: Box::new(left_equal),
                        right_equal: Box::new(right_equal),
                        requirement_proofs,
                    };
                    return Ok(Some(law.proof(application)));
                }
            }
        }
        Ok(None)
    }
}

// Reused schema-application pipeline. Each public rule below owns a distinct
// success struct; only the common checked stages are shared here.
pub struct MatrixLawApplicationProof {
    pub arguments: Vec<Obj>,
    pub requirements: Vec<Fact>,
    pub conclusion: EqualFact,
    pub orientation: MatrixLawOrientation,
    pub left_equal: Box<EqualFactSearchedProof>,
    pub right_equal: Box<EqualFactSearchedProof>,
    pub requirement_proofs: Vec<VerifyFactResult>,
}
#[derive(Clone, Copy)]
pub enum MatrixLawOrientation {
    Forward,
    Reverse,
}

pub enum NativeMatrixLawProof {
    MulAssociative(MulAssociativeBuiltinRuleProof),
    MulDistributiveLeft(MulDistributiveLeftBuiltinRuleProof),
    MulDistributiveRight(MulDistributiveRightBuiltinRuleProof),
    MulIdentityLeft(MulIdentityLeftBuiltinRuleProof),
    MulIdentityRight(MulIdentityRightBuiltinRuleProof),
    MulZeroRight(MulZeroRightBuiltinRuleProof),
    MulZeroLeft(MulZeroLeftBuiltinRuleProof),
    ApplyIdentity(ApplyIdentityBuiltinRuleProof),
    ApplyCompose(ApplyComposeBuiltinRuleProof),
    MatrixTransposeMul(MatrixTransposeMulBuiltinRuleProof),
    MatrixAdjointMul(MatrixAdjointMulBuiltinRuleProof),
    TraceAdd(TraceAddBuiltinRuleProof),
    TraceScale(TraceScaleBuiltinRuleProof),
    TraceCyclic(TraceCyclicBuiltinRuleProof),
    PowerZero(PowerZeroBuiltinRuleProof),
    PowerSuccessor(PowerSuccessorBuiltinRuleProof),
    PowerAdd(PowerAddBuiltinRuleProof),
    DetIdentity(DetIdentityBuiltinRuleProof),
    DetTranspose(DetTransposeBuiltinRuleProof),
    DetAdjoint(DetAdjointBuiltinRuleProof),
    DetMul(DetMulBuiltinRuleProof),
    AdjugateLeft(AdjugateLeftBuiltinRuleProof),
    InverseLeft(InverseLeftBuiltinRuleProof),
    AdjugateRight(AdjugateRightBuiltinRuleProof),
    InverseRight(InverseRightBuiltinRuleProof),
    RankZero(RankZeroBuiltinRuleProof),
    RankIdentity(RankIdentityBuiltinRuleProof),
    MatrixRankTranspose(MatrixRankTransposeBuiltinRuleProof),
    MatrixRankAdjoint(MatrixRankAdjointBuiltinRuleProof),
    RankInvertible(RankInvertibleBuiltinRuleProof),
    InnerConjugateSymmetry(InnerConjugateSymmetryBuiltinRuleProof),
    EuclideanNormSquare(EuclideanNormSquareBuiltinRuleProof),
    FrobeniusNormScale(FrobeniusNormScaleBuiltinRuleProof),
}
pub struct MulAssociativeBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulDistributiveLeftBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulDistributiveRightBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulIdentityLeftBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulIdentityRightBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulZeroRightBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MulZeroLeftBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct ApplyIdentityBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct ApplyComposeBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MatrixTransposeMulBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MatrixAdjointMulBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct TraceAddBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct TraceScaleBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct TraceCyclicBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct PowerZeroBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct PowerSuccessorBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct PowerAddBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct DetIdentityBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct DetTransposeBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct DetAdjointBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct DetMulBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct AdjugateLeftBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct InverseLeftBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct AdjugateRightBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct InverseRightBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct RankZeroBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct RankIdentityBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MatrixRankTransposeBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct MatrixRankAdjointBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct RankInvertibleBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct InnerConjugateSymmetryBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct EuclideanNormSquareBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
pub struct FrobeniusNormScaleBuiltinRuleProof {
    pub application: MatrixLawApplicationProof,
}
impl NativeMatrixLawProof {
    pub fn rule_name(&self) -> &'static str {
        match self {
            Self::MulAssociative(_) => "NativeMatrixMulAssociative",
            Self::MulDistributiveLeft(_) => "NativeMatrixMulDistributiveLeft",
            Self::MulDistributiveRight(_) => "NativeMatrixMulDistributiveRight",
            Self::MulIdentityLeft(_) => "NativeMatrixMulIdentityLeft",
            Self::MulIdentityRight(_) => "NativeMatrixMulIdentityRight",
            Self::MulZeroRight(_) => "NativeMatrixMulZeroRight",
            Self::MulZeroLeft(_) => "NativeMatrixMulZeroLeft",
            Self::ApplyIdentity(_) => "NativeMatrixApplyIdentity",
            Self::ApplyCompose(_) => "NativeMatrixApplyCompose",
            Self::MatrixTransposeMul(_) => "NativeMatrixMatrixTransposeMul",
            Self::MatrixAdjointMul(_) => "NativeMatrixMatrixAdjointMul",
            Self::TraceAdd(_) => "NativeMatrixTraceAdd",
            Self::TraceScale(_) => "NativeMatrixTraceScale",
            Self::TraceCyclic(_) => "NativeMatrixTraceCyclic",
            Self::PowerZero(_) => "NativeMatrixPowerZero",
            Self::PowerSuccessor(_) => "NativeMatrixPowerSuccessor",
            Self::PowerAdd(_) => "NativeMatrixPowerAdd",
            Self::DetIdentity(_) => "NativeMatrixDetIdentity",
            Self::DetTranspose(_) => "NativeMatrixDetTranspose",
            Self::DetAdjoint(_) => "NativeMatrixDetAdjoint",
            Self::DetMul(_) => "NativeMatrixDetMul",
            Self::AdjugateLeft(_) => "NativeMatrixAdjugateLeft",
            Self::InverseLeft(_) => "NativeMatrixInverseLeft",
            Self::AdjugateRight(_) => "NativeMatrixAdjugateRight",
            Self::InverseRight(_) => "NativeMatrixInverseRight",
            Self::RankZero(_) => "NativeMatrixRankZero",
            Self::RankIdentity(_) => "NativeMatrixRankIdentity",
            Self::MatrixRankTranspose(_) => "NativeMatrixMatrixRankTranspose",
            Self::MatrixRankAdjoint(_) => "NativeMatrixMatrixRankAdjoint",
            Self::RankInvertible(_) => "NativeMatrixRankInvertible",
            Self::InnerConjugateSymmetry(_) => "NativeMatrixInnerConjugateSymmetry",
            Self::EuclideanNormSquare(_) => "NativeMatrixEuclideanNormSquare",
            Self::FrobeniusNormScale(_) => "NativeMatrixFrobeniusNormScale",
        }
    }
    pub fn application(&self) -> &MatrixLawApplicationProof {
        match self {
            Self::MulAssociative(p) => &p.application,
            Self::MulDistributiveLeft(p) => &p.application,
            Self::MulDistributiveRight(p) => &p.application,
            Self::MulIdentityLeft(p) => &p.application,
            Self::MulIdentityRight(p) => &p.application,
            Self::MulZeroRight(p) => &p.application,
            Self::MulZeroLeft(p) => &p.application,
            Self::ApplyIdentity(p) => &p.application,
            Self::ApplyCompose(p) => &p.application,
            Self::MatrixTransposeMul(p) => &p.application,
            Self::MatrixAdjointMul(p) => &p.application,
            Self::TraceAdd(p) => &p.application,
            Self::TraceScale(p) => &p.application,
            Self::TraceCyclic(p) => &p.application,
            Self::PowerZero(p) => &p.application,
            Self::PowerSuccessor(p) => &p.application,
            Self::PowerAdd(p) => &p.application,
            Self::DetIdentity(p) => &p.application,
            Self::DetTranspose(p) => &p.application,
            Self::DetAdjoint(p) => &p.application,
            Self::DetMul(p) => &p.application,
            Self::AdjugateLeft(p) => &p.application,
            Self::InverseLeft(p) => &p.application,
            Self::AdjugateRight(p) => &p.application,
            Self::InverseRight(p) => &p.application,
            Self::RankZero(p) => &p.application,
            Self::RankIdentity(p) => &p.application,
            Self::MatrixRankTranspose(p) => &p.application,
            Self::MatrixRankAdjoint(p) => &p.application,
            Self::RankInvertible(p) => &p.application,
            Self::InnerConjugateSymmetry(p) => &p.application,
            Self::EuclideanNormSquare(p) => &p.application,
            Self::FrobeniusNormScale(p) => &p.application,
        }
    }
}
#[derive(Clone, Copy)]
enum NativeMatrixLawKind {
    MulAssociative,
    MulDistributiveLeft,
    MulDistributiveRight,
    MulIdentityLeft,
    MulIdentityRight,
    MulZeroRight,
    MulZeroLeft,
    ApplyIdentity,
    ApplyCompose,
    MatrixTransposeMul,
    MatrixAdjointMul,
    TraceAdd,
    TraceScale,
    TraceCyclic,
    PowerZero,
    PowerSuccessor,
    PowerAdd,
    DetIdentity,
    DetTranspose,
    DetAdjoint,
    DetMul,
    AdjugateLeft,
    InverseLeft,
    AdjugateRight,
    InverseRight,
    RankZero,
    RankIdentity,
    MatrixRankTranspose,
    MatrixRankAdjoint,
    RankInvertible,
    InnerConjugateSymmetry,
    EuclideanNormSquare,
    FrobeniusNormScale,
}
impl NativeMatrixLawKind {
    fn proof(self, application: MatrixLawApplicationProof) -> NativeMatrixLawProof {
        match self {
            Self::MulAssociative => {
                NativeMatrixLawProof::MulAssociative(MulAssociativeBuiltinRuleProof { application })
            }
            Self::MulDistributiveLeft => {
                NativeMatrixLawProof::MulDistributiveLeft(MulDistributiveLeftBuiltinRuleProof {
                    application,
                })
            }
            Self::MulDistributiveRight => {
                NativeMatrixLawProof::MulDistributiveRight(MulDistributiveRightBuiltinRuleProof {
                    application,
                })
            }
            Self::MulIdentityLeft => {
                NativeMatrixLawProof::MulIdentityLeft(MulIdentityLeftBuiltinRuleProof {
                    application,
                })
            }
            Self::MulIdentityRight => {
                NativeMatrixLawProof::MulIdentityRight(MulIdentityRightBuiltinRuleProof {
                    application,
                })
            }
            Self::MulZeroRight => {
                NativeMatrixLawProof::MulZeroRight(MulZeroRightBuiltinRuleProof { application })
            }
            Self::MulZeroLeft => {
                NativeMatrixLawProof::MulZeroLeft(MulZeroLeftBuiltinRuleProof { application })
            }
            Self::ApplyIdentity => {
                NativeMatrixLawProof::ApplyIdentity(ApplyIdentityBuiltinRuleProof { application })
            }
            Self::ApplyCompose => {
                NativeMatrixLawProof::ApplyCompose(ApplyComposeBuiltinRuleProof { application })
            }
            Self::MatrixTransposeMul => {
                NativeMatrixLawProof::MatrixTransposeMul(MatrixTransposeMulBuiltinRuleProof {
                    application,
                })
            }
            Self::MatrixAdjointMul => {
                NativeMatrixLawProof::MatrixAdjointMul(MatrixAdjointMulBuiltinRuleProof {
                    application,
                })
            }
            Self::TraceAdd => {
                NativeMatrixLawProof::TraceAdd(TraceAddBuiltinRuleProof { application })
            }
            Self::TraceScale => {
                NativeMatrixLawProof::TraceScale(TraceScaleBuiltinRuleProof { application })
            }
            Self::TraceCyclic => {
                NativeMatrixLawProof::TraceCyclic(TraceCyclicBuiltinRuleProof { application })
            }
            Self::PowerZero => {
                NativeMatrixLawProof::PowerZero(PowerZeroBuiltinRuleProof { application })
            }
            Self::PowerSuccessor => {
                NativeMatrixLawProof::PowerSuccessor(PowerSuccessorBuiltinRuleProof { application })
            }
            Self::PowerAdd => {
                NativeMatrixLawProof::PowerAdd(PowerAddBuiltinRuleProof { application })
            }
            Self::DetIdentity => {
                NativeMatrixLawProof::DetIdentity(DetIdentityBuiltinRuleProof { application })
            }
            Self::DetTranspose => {
                NativeMatrixLawProof::DetTranspose(DetTransposeBuiltinRuleProof { application })
            }
            Self::DetAdjoint => {
                NativeMatrixLawProof::DetAdjoint(DetAdjointBuiltinRuleProof { application })
            }
            Self::DetMul => NativeMatrixLawProof::DetMul(DetMulBuiltinRuleProof { application }),
            Self::AdjugateLeft => {
                NativeMatrixLawProof::AdjugateLeft(AdjugateLeftBuiltinRuleProof { application })
            }
            Self::InverseLeft => {
                NativeMatrixLawProof::InverseLeft(InverseLeftBuiltinRuleProof { application })
            }
            Self::AdjugateRight => {
                NativeMatrixLawProof::AdjugateRight(AdjugateRightBuiltinRuleProof { application })
            }
            Self::InverseRight => {
                NativeMatrixLawProof::InverseRight(InverseRightBuiltinRuleProof { application })
            }
            Self::RankZero => {
                NativeMatrixLawProof::RankZero(RankZeroBuiltinRuleProof { application })
            }
            Self::RankIdentity => {
                NativeMatrixLawProof::RankIdentity(RankIdentityBuiltinRuleProof { application })
            }
            Self::MatrixRankTranspose => {
                NativeMatrixLawProof::MatrixRankTranspose(MatrixRankTransposeBuiltinRuleProof {
                    application,
                })
            }
            Self::MatrixRankAdjoint => {
                NativeMatrixLawProof::MatrixRankAdjoint(MatrixRankAdjointBuiltinRuleProof {
                    application,
                })
            }
            Self::RankInvertible => {
                NativeMatrixLawProof::RankInvertible(RankInvertibleBuiltinRuleProof { application })
            }
            Self::InnerConjugateSymmetry => NativeMatrixLawProof::InnerConjugateSymmetry(
                InnerConjugateSymmetryBuiltinRuleProof { application },
            ),
            Self::EuclideanNormSquare => {
                NativeMatrixLawProof::EuclideanNormSquare(EuclideanNormSquareBuiltinRuleProof {
                    application,
                })
            }
            Self::FrobeniusNormScale => {
                NativeMatrixLawProof::FrobeniusNormScale(FrobeniusNormScaleBuiltinRuleProof {
                    application,
                })
            }
        }
    }
    fn theorem(self) -> BuiltinTheoremId {
        match self {
            Self::MulAssociative => BuiltinTheoremId::MatrixMulAssociative,
            Self::MulDistributiveLeft => BuiltinTheoremId::MatrixMulDistributiveLeft,
            Self::MulDistributiveRight => BuiltinTheoremId::MatrixMulDistributiveRight,
            Self::MulIdentityLeft => BuiltinTheoremId::MatrixMulIdentity,
            Self::MulIdentityRight => BuiltinTheoremId::MatrixMulIdentity,
            Self::MulZeroRight => BuiltinTheoremId::MatrixMulZero,
            Self::MulZeroLeft => BuiltinTheoremId::MatrixMulZero,
            Self::ApplyIdentity => BuiltinTheoremId::MatrixApplyIdentity,
            Self::ApplyCompose => BuiltinTheoremId::MatrixApplyCompose,
            Self::MatrixTransposeMul => BuiltinTheoremId::MatrixTransposeMul,
            Self::MatrixAdjointMul => BuiltinTheoremId::MatrixAdjointMul,
            Self::TraceAdd => BuiltinTheoremId::MatrixTraceLinearity,
            Self::TraceScale => BuiltinTheoremId::MatrixTraceLinearity,
            Self::TraceCyclic => BuiltinTheoremId::MatrixTraceCyclic,
            Self::PowerZero => BuiltinTheoremId::MatrixPowerZero,
            Self::PowerSuccessor => BuiltinTheoremId::MatrixPowerSuccessor,
            Self::PowerAdd => BuiltinTheoremId::MatrixPowerAdd,
            Self::DetIdentity => BuiltinTheoremId::MatrixDetIdentity,
            Self::DetTranspose => BuiltinTheoremId::MatrixDetTranspose,
            Self::DetAdjoint => BuiltinTheoremId::MatrixDetAdjoint,
            Self::DetMul => BuiltinTheoremId::MatrixDetMul,
            Self::AdjugateLeft => BuiltinTheoremId::MatrixAdjugateIdentity,
            Self::InverseLeft => BuiltinTheoremId::MatrixInverseLaws,
            Self::AdjugateRight => BuiltinTheoremId::MatrixAdjugateIdentity,
            Self::InverseRight => BuiltinTheoremId::MatrixInverseLaws,
            Self::RankZero => BuiltinTheoremId::MatrixRankZero,
            Self::RankIdentity => BuiltinTheoremId::MatrixRankIdentity,
            Self::MatrixRankTranspose => BuiltinTheoremId::MatrixRankTranspose,
            Self::MatrixRankAdjoint => BuiltinTheoremId::MatrixRankAdjoint,
            Self::RankInvertible => BuiltinTheoremId::MatrixRankInvertible,
            Self::InnerConjugateSymmetry => BuiltinTheoremId::InnerProductConjugateSymmetry,
            Self::EuclideanNormSquare => BuiltinTheoremId::EuclideanNormSquare,
            Self::FrobeniusNormScale => BuiltinTheoremId::FrobeniusNormScale,
        }
    }
    fn conclusion_index(self) -> usize {
        match self {
            Self::MulIdentityRight
            | Self::MulZeroLeft
            | Self::AdjugateLeft
            | Self::InverseLeft
            | Self::EuclideanNormSquare => 1,
            _ => 0,
        }
    }
}

// Match only a fixed root and its immediate children; dimensions and the whole
// requested equation are subsequently checked against the shared schema.
fn matrix_law_candidates(root: &Obj) -> Vec<(NativeMatrixLawKind, Vec<Obj>)> {
    use MatrixOperator as M;
    use NativeMatrixLawKind as L;
    let mut out = Vec::new();
    if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = root {
        if let Some(M::EuclideanNorm(x)) = matrix_operator(&power.base) {
            out.push((
                L::EuclideanNormSquare,
                vec![(*x.vector).clone(), (*x.dimension).clone()],
            ));
        }
        return out;
    }
    let Some(operator) = matrix_operator(root) else {
        return out;
    };
    match operator {
        M::Multiply(x) => {
            match matrix_operator(&x.left) {
                Some(M::Multiply(y)) => out.push((
                    L::MulAssociative,
                    vec![
                        (*y.left).clone(),
                        (*y.right).clone(),
                        (*x.right).clone(),
                        (*x.rows).clone(),
                        (*y.inner).clone(),
                        (*x.inner).clone(),
                        (*x.cols).clone(),
                    ],
                )),
                Some(M::Add(y)) => out.push((
                    L::MulDistributiveRight,
                    vec![
                        (*y.left).clone(),
                        (*y.right).clone(),
                        (*x.right).clone(),
                        (*x.rows).clone(),
                        (*x.inner).clone(),
                        (*x.cols).clone(),
                    ],
                )),
                Some(M::IdentityMatrix(_)) => out.push((
                    L::MulIdentityLeft,
                    vec![(*x.right).clone(), (*x.rows).clone(), (*x.cols).clone()],
                )),
                Some(M::ZeroMatrix(_)) => out.push((
                    L::MulZeroLeft,
                    vec![
                        (*x.right).clone(),
                        (*x.inner).clone(),
                        (*x.cols).clone(),
                        (*x.rows).clone(),
                    ],
                )),
                Some(M::Adjugate(y)) => out.push((
                    L::AdjugateLeft,
                    vec![(*y.matrix).clone(), (*y.order).clone()],
                )),
                Some(M::Inverse(y)) => out.push((
                    L::InverseLeft,
                    vec![(*y.matrix).clone(), (*y.order).clone()],
                )),
                _ => {}
            }
            match matrix_operator(&x.right) {
                Some(M::Add(y)) => out.push((
                    L::MulDistributiveLeft,
                    vec![
                        (*x.left).clone(),
                        (*y.left).clone(),
                        (*y.right).clone(),
                        (*x.rows).clone(),
                        (*x.inner).clone(),
                        (*x.cols).clone(),
                    ],
                )),
                Some(M::IdentityMatrix(_)) => out.push((
                    L::MulIdentityRight,
                    vec![(*x.left).clone(), (*x.rows).clone(), (*x.cols).clone()],
                )),
                Some(M::ZeroMatrix(_)) => out.push((
                    L::MulZeroRight,
                    vec![
                        (*x.left).clone(),
                        (*x.rows).clone(),
                        (*x.inner).clone(),
                        (*x.cols).clone(),
                    ],
                )),
                Some(M::Adjugate(y)) => out.push((
                    L::AdjugateRight,
                    vec![(*y.matrix).clone(), (*y.order).clone()],
                )),
                Some(M::Inverse(y)) => out.push((
                    L::InverseRight,
                    vec![(*y.matrix).clone(), (*y.order).clone()],
                )),
                _ => {}
            }
        }
        M::Apply(x) => match matrix_operator(&x.matrix) {
            Some(M::IdentityMatrix(y)) => out.push((
                L::ApplyIdentity,
                vec![(*x.vector).clone(), (*y.order).clone()],
            )),
            Some(M::Multiply(y)) => out.push((
                L::ApplyCompose,
                vec![
                    (*y.left).clone(),
                    (*y.right).clone(),
                    (*x.vector).clone(),
                    (*y.rows).clone(),
                    (*y.inner).clone(),
                    (*y.cols).clone(),
                ],
            )),
            _ => {}
        },
        M::Transpose(x) => {
            if let Some(M::Multiply(y)) = matrix_operator(&x.matrix) {
                out.push((
                    L::MatrixTransposeMul,
                    vec![
                        (*y.left).clone(),
                        (*y.right).clone(),
                        (*y.rows).clone(),
                        (*y.inner).clone(),
                        (*y.cols).clone(),
                    ],
                ));
            }
        }
        M::ConjugateTranspose(x) => {
            if let Some(M::Multiply(y)) = matrix_operator(&x.matrix) {
                out.push((
                    L::MatrixAdjointMul,
                    vec![
                        (*y.left).clone(),
                        (*y.right).clone(),
                        (*y.rows).clone(),
                        (*y.inner).clone(),
                        (*y.cols).clone(),
                    ],
                ));
            }
        }
        M::Trace(x) => match matrix_operator(&x.matrix) {
            Some(M::Add(y)) => out.push((
                L::TraceAdd,
                vec![(*y.left).clone(), (*y.right).clone(), (*x.order).clone()],
            )),
            Some(M::Scale(y)) => out.push((
                L::TraceScale,
                vec![(*y.scalar).clone(), (*y.matrix).clone(), (*x.order).clone()],
            )),
            Some(M::Multiply(y)) => out.push((
                L::TraceCyclic,
                vec![
                    (*y.left).clone(),
                    (*y.right).clone(),
                    (*y.rows).clone(),
                    (*y.inner).clone(),
                ],
            )),
            _ => {}
        },
        M::Power(x) => {
            out.push((L::PowerZero, vec![(*x.matrix).clone(), (*x.order).clone()]));
            if let Obj::ArithmeticOperator(ArithmeticOperator::Add(y)) = x.exponent.as_ref() {
                out.push((
                    L::PowerSuccessor,
                    vec![(*x.matrix).clone(), (*x.order).clone(), (*y.left).clone()],
                ));
                out.push((
                    L::PowerAdd,
                    vec![
                        (*x.matrix).clone(),
                        (*x.order).clone(),
                        (*y.left).clone(),
                        (*y.right).clone(),
                    ],
                ));
            }
        }
        M::Determinant(x) => match matrix_operator(&x.matrix) {
            Some(M::IdentityMatrix(_)) => out.push((L::DetIdentity, vec![(*x.order).clone()])),
            Some(M::Transpose(y)) => out.push((
                L::DetTranspose,
                vec![(*y.matrix).clone(), (*x.order).clone()],
            )),
            Some(M::ConjugateTranspose(y)) => {
                out.push((L::DetAdjoint, vec![(*y.matrix).clone(), (*x.order).clone()]))
            }
            Some(M::Multiply(y)) => out.push((
                L::DetMul,
                vec![(*y.left).clone(), (*y.right).clone(), (*x.order).clone()],
            )),
            _ => {}
        },
        M::Rank(x) => {
            match matrix_operator(&x.matrix) {
                Some(M::ZeroMatrix(_)) => {
                    out.push((L::RankZero, vec![(*x.rows).clone(), (*x.cols).clone()]))
                }
                Some(M::IdentityMatrix(_)) => out.push((L::RankIdentity, vec![(*x.rows).clone()])),
                Some(M::Transpose(y)) => out.push((
                    L::MatrixRankTranspose,
                    vec![(*y.matrix).clone(), (*y.rows).clone(), (*y.cols).clone()],
                )),
                Some(M::ConjugateTranspose(y)) => out.push((
                    L::MatrixRankAdjoint,
                    vec![(*y.matrix).clone(), (*y.rows).clone(), (*y.cols).clone()],
                )),
                _ => {}
            }
            out.push((
                L::RankInvertible,
                vec![(*x.matrix).clone(), (*x.rows).clone()],
            ));
        }
        M::InnerProduct(x) => out.push((
            L::InnerConjugateSymmetry,
            vec![
                (*x.left).clone(),
                (*x.right).clone(),
                (*x.dimension).clone(),
            ],
        )),
        M::FrobeniusNorm(x) => {
            if let Some(M::Scale(y)) = matrix_operator(&x.matrix) {
                out.push((
                    L::FrobeniusNormScale,
                    vec![
                        (*y.scalar).clone(),
                        (*y.matrix).clone(),
                        (*x.rows).clone(),
                        (*x.cols).clone(),
                    ],
                ));
            }
        }
        _ => {}
    }
    out
}
fn matrix_operator(obj: &Obj) -> Option<&MatrixOperator> {
    if let Obj::MatrixOperator(operator) = obj {
        Some(operator)
    } else {
        None
    }
}
#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/native_matrix/direct_laws.rs"]
mod native_matrix_laws_tests;
