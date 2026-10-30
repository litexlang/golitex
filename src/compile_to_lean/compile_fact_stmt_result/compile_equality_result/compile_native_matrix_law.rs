//! Replay the original root-selected matrix law and its direct endpoint matches.
use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_builtin_determinant_theorem::{
    determinant_law_term, validate_determinant_law,
};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
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
        let theorem = match proof {
            NativeMatrixLawProof::DetIdentity(_) => BuiltinTheoremId::MatrixDetIdentity,
            NativeMatrixLawProof::DetTranspose(_) => BuiltinTheoremId::MatrixDetTranspose,
            NativeMatrixLawProof::DetAdjoint(_) => BuiltinTheoremId::MatrixDetAdjoint,
            _ => {
                return Err(LeanCompileError::unsupported(&format!(
                    "MatrixLaw/Unsupported/{}",
                    proof.rule_name(),
                )))
            }
        };
        let application = proof.application();
        let count = validate_determinant_law(
            theorem,
            &application.arguments,
            &application.requirements,
            &application.conclusion,
        )?;
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
        let law = determinant_law_term(theorem, &root, &format!("Litex.Same {root} {other}"))?;
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
