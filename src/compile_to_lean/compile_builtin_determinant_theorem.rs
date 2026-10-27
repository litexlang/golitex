//! Explicit determinant laws selected by the source theorem invocation.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_determinant_theorem(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let identity = match builtin.theorem {
            BuiltinTheoremId::MatrixDetIdentity => true,
            BuiltinTheoremId::MatrixDetTranspose | BuiltinTheoremId::MatrixDetAdjoint => false,
            _ => return Err(LeanCompileError::unsupported("Determinant/Theorem")),
        };
        let adjoint = builtin.theorem == BuiltinTheoremId::MatrixDetAdjoint;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("Determinant/TheoremContract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("Determinant/Arguments"));
        };
        let count = if identity { 1 } else { 3 };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != if identity { 1 } else { 2 }
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported("Determinant/TheoremStages"));
        }
        let n = &arguments[usize::from(!identity)];
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("Determinant/Conclusion"));
        };
        let Obj::MatrixOperator(MatrixOperator::Determinant(det)) = &conclusion.left else {
            return Err(LeanCompileError::unsupported(
                "Determinant/ConclusionSubject",
            ));
        };
        if det.order.ir() != n.ir() {
            return Err(LeanCompileError::unsupported("Determinant/ConclusionOrder"));
        }
        if identity {
            if !matches!(det.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) if p.order.ir()==n.ir())
                || closed_integer(&conclusion.right) != Some(1)
            {
                return Err(LeanCompileError::unsupported(
                    "Determinant/IdentityConclusion",
                ));
            }
        } else {
            let valid = match det.matrix.as_ref() {
                Obj::MatrixOperator(MatrixOperator::Transpose(p)) if !adjoint => {
                    p.matrix.ir() == arguments[0].ir()
                        && p.rows.ir() == n.ir()
                        && p.cols.ir() == n.ir()
                }
                Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(p)) if adjoint => {
                    p.matrix.ir() == arguments[0].ir()
                        && p.rows.ir() == n.ir()
                        && p.cols.ir() == n.ir()
                }
                _ => false,
            };
            let right = if adjoint {
                let Obj::ComplexOperator(ComplexOperator::Conjugate(p)) = &conclusion.right else {
                    return Err(LeanCompileError::unsupported(
                        "Determinant/AdjointConclusion",
                    ));
                };
                p.arg.as_ref()
            } else {
                &conclusion.right
            };
            if !valid
                || !matches!(right, Obj::MatrixOperator(MatrixOperator::Determinant(p)) if p.matrix.ir()==arguments[0].ir() && p.order.ir()==n.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "Determinant/TransposeConclusion",
                ));
            }
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            let expected = if index < 2 || identity {
                matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
            } else {
                matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==arguments[0].ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m)) if m.set.as_ref()==&Obj::StandardSet(StandardSet::C) && m.rows.ir()==n.ir() && m.cols.ir()==n.ir()))
            };
            if !expected || source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("Determinant/TheoremPremise"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let root = self.compile_object_reference(&conclusion.left, &scope)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let law = if identity {
            "Litex.matrixDeterminantIdentity _det.val.order _det.wd.1".to_string()
        } else {
            let name = if adjoint {
                "matrixDeterminantAdjoint"
            } else {
                "matrixDeterminantTranspose"
            };
            format!(
                "Litex.{name} _det.val.matrix.val.matrix _det.val.order _det.wd.1 _det.val.matrix.wd.2.2"
            )
        };
        let proof = format!("(show {statement} from by\n  let _det := {root}\n  exact {law}\n)");
        Ok((definitions, proof, builtin.conclusions.clone()))
    }
}
