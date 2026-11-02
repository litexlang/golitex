//! Replay the original root-selected matrix law and its direct endpoint matches.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_builtin_determinant_theorem::{
    determinant_law_term, validate_determinant_law,
};
use crate::compile_to_lean::compile_builtin_matrix_power_theorem::{matrix_power_law_term, matrix_power_add_law_term, validate_matrix_power_law};
use crate::compile_to_lean::compile_builtin_rank_theorem::{simple_rank_law_term, validate_simple_rank_law, rank_transform_law_term, validate_rank_transform_law};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::compile_frobenius_scale_law::{validate_frobenius_scale_law,frobenius_scale_law_term};
use crate::compile_to_lean::compile_vector_laws::{validate_inner_symmetry_law, validate_euclidean_inner_law, inner_symmetry_law_term, euclidean_inner_law_term};
use crate::compile_to_lean::compile_trace_laws::{TraceLaw, validate_trace_law, trace_law_term};
use crate::compile_to_lean::compile_matrix_simple_laws::{SimpleMatrixLaw, validate_simple_matrix_law, simple_matrix_law_term};
use crate::compile_to_lean::compile_matrix_algebra_laws::{MatrixAlgebraLaw, validate_matrix_algebra_law, matrix_algebra_law_term};
use crate::compile_to_lean::compile_matrix_apply_laws::{MatrixApplyLaw, validate_matrix_apply_law, matrix_apply_law_term};
use crate::compile_to_lean::compile_matrix_transform_laws::{MatrixTransformLaw, validate_matrix_transform_law, matrix_transform_law_term};
use crate::compile_to_lean::compile_matrix_adjugate_laws::{MatrixAdjugateLaw, validate_matrix_adjugate_law, matrix_adjugate_law_term};
use crate::compile_to_lean::compile_matrix_inverse_laws::{MatrixInverseLaw, validate_matrix_inverse_law, matrix_inverse_law_term};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::compile_builtin_rank_theorem::{validate_rank_invertible_law, rank_invertible_law_term};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{
    MatrixLawOrientation, NativeMatrixLawProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_native_matrix_law(
        &self,
        goal: &EqualFact,
        proof: &NativeMatrixLawProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let inverse = match proof {
            NativeMatrixLawProof::InverseLeft(_) => Some(MatrixInverseLaw::Left),
            NativeMatrixLawProof::InverseRight(_) => Some(MatrixInverseLaw::Right),
            _ => None,
        };
        let adjugate = match proof {
            NativeMatrixLawProof::AdjugateLeft(_) => Some(MatrixAdjugateLaw::Left),
            NativeMatrixLawProof::AdjugateRight(_) => Some(MatrixAdjugateLaw::Right),
            _ => None,
        };
        let transform = match proof {
            NativeMatrixLawProof::MatrixTransposeMul(_) => Some(MatrixTransformLaw::Transpose),
            NativeMatrixLawProof::MatrixAdjointMul(_) => Some(MatrixTransformLaw::Adjoint),
            _ => None,
        };
        let action = match proof {
            NativeMatrixLawProof::ApplyIdentity(_) => Some(MatrixApplyLaw::Identity),
            NativeMatrixLawProof::ApplyCompose(_) => Some(MatrixApplyLaw::Compose),
            _ => None,
        };
        let algebra = match proof {
            NativeMatrixLawProof::MulAssociative(_) => Some(MatrixAlgebraLaw::Associative),
            NativeMatrixLawProof::MulDistributiveLeft(_) => {
                Some(MatrixAlgebraLaw::DistributiveLeft)
            }
            NativeMatrixLawProof::MulDistributiveRight(_) => {
                Some(MatrixAlgebraLaw::DistributiveRight)
            }
            _ => None,
        };
        let simple = match proof {
            NativeMatrixLawProof::MulIdentityLeft(_) => Some(SimpleMatrixLaw::IdentityLeft),
            NativeMatrixLawProof::MulIdentityRight(_) => Some(SimpleMatrixLaw::IdentityRight),
            NativeMatrixLawProof::MulZeroRight(_) => Some(SimpleMatrixLaw::ZeroRight),
            NativeMatrixLawProof::MulZeroLeft(_) => Some(SimpleMatrixLaw::ZeroLeft),
            _ => None,
        };
        let trace = match proof {
            NativeMatrixLawProof::TraceAdd(_) => Some(TraceLaw::Add),
            NativeMatrixLawProof::TraceScale(_) => Some(TraceLaw::Scale),
            NativeMatrixLawProof::TraceCyclic(_) => Some(TraceLaw::Cyclic),
            _ => None,
        };
        let theorem = match proof {
            NativeMatrixLawProof::InverseLeft(_) | NativeMatrixLawProof::InverseRight(_) => {
                BuiltinTheoremId::MatrixInverseLaws
            }
            NativeMatrixLawProof::AdjugateLeft(_) | NativeMatrixLawProof::AdjugateRight(_) => {
                BuiltinTheoremId::MatrixAdjugateIdentity
            }
            NativeMatrixLawProof::FrobeniusNormScale(_) => BuiltinTheoremId::FrobeniusNormScale,
            NativeMatrixLawProof::MatrixTransposeMul(_) => BuiltinTheoremId::MatrixTransposeMul,
            NativeMatrixLawProof::MatrixAdjointMul(_) => BuiltinTheoremId::MatrixAdjointMul,
            NativeMatrixLawProof::ApplyIdentity(_) => BuiltinTheoremId::MatrixApplyIdentity,
            NativeMatrixLawProof::ApplyCompose(_) => BuiltinTheoremId::MatrixApplyCompose,
            NativeMatrixLawProof::MulAssociative(_) => BuiltinTheoremId::MatrixMulAssociative,
            NativeMatrixLawProof::MulDistributiveLeft(_) => {
                BuiltinTheoremId::MatrixMulDistributiveLeft
            }
            NativeMatrixLawProof::MulDistributiveRight(_) => {
                BuiltinTheoremId::MatrixMulDistributiveRight
            }
            NativeMatrixLawProof::MulIdentityLeft(_)
            | NativeMatrixLawProof::MulIdentityRight(_) => BuiltinTheoremId::MatrixMulIdentity,
            NativeMatrixLawProof::MulZeroRight(_) | NativeMatrixLawProof::MulZeroLeft(_) => {
                BuiltinTheoremId::MatrixMulZero
            }
            NativeMatrixLawProof::TraceAdd(_) | NativeMatrixLawProof::TraceScale(_) => {
                BuiltinTheoremId::MatrixTraceLinearity
            }
            NativeMatrixLawProof::TraceCyclic(_) => BuiltinTheoremId::MatrixTraceCyclic,
            NativeMatrixLawProof::DetMul(_) => BuiltinTheoremId::MatrixDetMul,
            NativeMatrixLawProof::DetIdentity(_) => BuiltinTheoremId::MatrixDetIdentity,
            NativeMatrixLawProof::DetTranspose(_) => BuiltinTheoremId::MatrixDetTranspose,
            NativeMatrixLawProof::DetAdjoint(_) => BuiltinTheoremId::MatrixDetAdjoint,
            NativeMatrixLawProof::PowerZero(_) => BuiltinTheoremId::MatrixPowerZero,
            NativeMatrixLawProof::PowerSuccessor(_) => BuiltinTheoremId::MatrixPowerSuccessor,
            NativeMatrixLawProof::PowerAdd(_) => BuiltinTheoremId::MatrixPowerAdd,
            NativeMatrixLawProof::RankZero(_) => BuiltinTheoremId::MatrixRankZero,
            NativeMatrixLawProof::RankIdentity(_) => BuiltinTheoremId::MatrixRankIdentity,
            NativeMatrixLawProof::RankInvertible(_) => BuiltinTheoremId::MatrixRankInvertible,
            NativeMatrixLawProof::MatrixRankTranspose(_) => BuiltinTheoremId::MatrixRankTranspose,
            NativeMatrixLawProof::MatrixRankAdjoint(_) => BuiltinTheoremId::MatrixRankAdjoint,
            NativeMatrixLawProof::InnerConjugateSymmetry(_) => {
                BuiltinTheoremId::InnerProductConjugateSymmetry
            }
            NativeMatrixLawProof::EuclideanNormSquare(_) => BuiltinTheoremId::EuclideanNormSquare,
        };
        let application = proof.application();
        let validate = match theorem {
            BuiltinTheoremId::MatrixRankInvertible => validate_rank_invertible_law,
            BuiltinTheoremId::FrobeniusNormScale => validate_frobenius_scale_law,
            BuiltinTheoremId::InnerProductConjugateSymmetry => validate_inner_symmetry_law,
            BuiltinTheoremId::EuclideanNormSquare => validate_euclidean_inner_law,
            BuiltinTheoremId::MatrixRankTranspose | BuiltinTheoremId::MatrixRankAdjoint => {
                validate_rank_transform_law
            }
            BuiltinTheoremId::MatrixPowerZero
            | BuiltinTheoremId::MatrixPowerSuccessor
            | BuiltinTheoremId::MatrixPowerAdd => validate_matrix_power_law,
            BuiltinTheoremId::MatrixRankZero | BuiltinTheoremId::MatrixRankIdentity => {
                validate_simple_rank_law
            }
            _ => validate_determinant_law,
        };
        let count = if let Some(kind) = inverse {
            validate_matrix_inverse_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = adjugate {
            validate_matrix_adjugate_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = transform {
            validate_matrix_transform_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = action {
            validate_matrix_apply_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = algebra {
            validate_matrix_algebra_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = simple {
            validate_simple_matrix_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else if let Some(kind) = trace {
            validate_trace_law(
                kind,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        } else {
            validate(
                theorem,
                &application.arguments,
                &application.requirements,
                &application.conclusion,
            )?
        };
        if application.requirement_proofs.len() != count {
            return Err(LeanCompileError::unsupported("MatrixLaw/RequirementCount"));
        }
        let (left, right) = match application.orientation {
            MatrixLawOrientation::Forward => {
                (&application.conclusion.left, &application.conclusion.right)
            }
            MatrixLawOrientation::Reverse => {
                (&application.conclusion.right, &application.conclusion.left)
            }
        };
        let mut lines = Vec::new();
        // The producer compares both endpoints before verifying requirements.
        // These subject views are never published as facts or proof producers.
        for (index, (source, target, evidence)) in [
            (left, &goal.left, application.left_equal.as_ref()),
            (right, &goal.right, application.right_equal.as_ref()),
        ]
        .into_iter()
        .enumerate()
        {
            if !matches!(
                evidence,
                EqualFactSearchedProof::ByTheyAreTheSame(_)
                    | EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
                    )
                    | EqualFactSearchedProof::ByClosedCalculation(_)
            ) {
                return Err(LeanCompileError::unsupported("MatrixLaw/DirectMatchRoute"));
            }
            let subject = EqualFact {
                fact_id: goal.fact_id,
                left: source.clone(),
                right: target.clone(),
                line_file: None,
            };
            let source_term = self.compile_object_reference(source, position)?;
            let target_term = self.compile_object_reference(target, position)?;
            let compiled = self.compile_equality_search(&subject, evidence, position)?;
            lines.push(format!(
                "have _matrix_match_{index} : Litex.Same {source_term} {target_term} := {compiled}"
            ));
        }
        for (index, (requirement, child)) in application
            .requirements
            .iter()
            .zip(&application.requirement_proofs)
            .enumerate()
        {
            let actual = source_subject(child)?;
            if actual.fact_id() != requirement.fact_id() || actual.ir() != requirement.ir() {
                return Err(LeanCompileError::unsupported(
                    "MatrixLaw/RequirementSubject",
                ));
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(&application.requirement_proofs),
                index,
            );
            let compiled = self.compile_verify(child, &prior)?;
            lines.push(format!(
                "have _matrix_requirement_{index} : {} := {}",
                compiled.0, compiled.1
            ));
        }
        // The law's constructors come from the original parent formation.
        // Successful requirement checks do not publish additional truth facts.
        let root = self.compile_object_reference(&application.conclusion.left, position)?;
        let other = self.compile_object_reference(&application.conclusion.right, position)?;
        let statement = format!("Litex.Same {root} {other}");
        let law = if let Some(kind) = inverse {
            matrix_inverse_law_term(kind, &root, &statement, "_matrix_requirement_3")
        } else if let Some(kind) = adjugate {
            matrix_adjugate_law_term(kind, &root, &statement)
        } else if let Some(kind) = transform {
            matrix_transform_law_term(kind, &root, &statement)
        } else if let Some(kind) = action {
            matrix_apply_law_term(kind, &root, &statement)
        } else if let Some(kind) = algebra {
            matrix_algebra_law_term(kind, &root, &statement)
        } else if let Some(kind) = simple {
            simple_matrix_law_term(kind, &root, &statement)
        } else if let Some(kind) = trace {
            trace_law_term(kind, &root, &statement)
        } else {
            match theorem {
                BuiltinTheoremId::MatrixRankInvertible => {
                    rank_invertible_law_term(&root, &statement, "_matrix_requirement_3")
                }
                BuiltinTheoremId::FrobeniusNormScale => frobenius_scale_law_term(&root, &statement),
                BuiltinTheoremId::InnerProductConjugateSymmetry => {
                    inner_symmetry_law_term(&root, &statement)
                }
                BuiltinTheoremId::EuclideanNormSquare => {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(square)) =
                        &application.conclusion.left
                    else {
                        unreachable!("validated norm square")
                    };
                    let norm = self.compile_object_reference(&square.base, position)?;
                    euclidean_inner_law_term(&norm, &statement)
                }
                BuiltinTheoremId::MatrixRankTranspose | BuiltinTheoremId::MatrixRankAdjoint => {
                    rank_transform_law_term(theorem, &root, &statement)?
                }
                BuiltinTheoremId::MatrixPowerZero => {
                    matrix_power_law_term(theorem, &root, &statement, None)?
                }
                BuiltinTheoremId::MatrixPowerSuccessor => matrix_power_law_term(
                    theorem,
                    &root,
                    &statement,
                    Some("_matrix_requirement_3"),
                )?,
                BuiltinTheoremId::MatrixPowerAdd => matrix_power_add_law_term(
                    &root,
                    &statement,
                    "_matrix_requirement_3",
                    "_matrix_requirement_4",
                ),
                BuiltinTheoremId::MatrixRankZero | BuiltinTheoremId::MatrixRankIdentity => {
                    simple_rank_law_term(theorem, &root, &statement)?
                }
                _ => determinant_law_term(theorem, &root, &statement)?,
            }
        };
        lines.push(format!(
            "have _matrix_law : Litex.Same {root} {other} := {law}"
        ));
        let oriented = match application.orientation {
            MatrixLawOrientation::Forward => "_matrix_law",
            MatrixLawOrientation::Reverse => "_matrix_law.symm",
        };
        lines.push(format!(
            "exact _matrix_match_0.symm.trans ({oriented}.trans _matrix_match_1)"
        ));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
