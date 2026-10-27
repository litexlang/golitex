use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixDefinitionResidualProof, MatrixEqualityProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_equality(
        &self,
        fact: &EqualFact,
        proof: &MatrixEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let MatrixEqualityProof::ScalarDefinition(p) = proof {
            if [&fact.left, &fact.right]
                .iter()
                .any(|obj| matches!(obj, Obj::MatrixOperator(MatrixOperator::Cofactor(_))))
            {
                return self.compile_matrix_cofactor_definition(fact, p, position);
            }
            if [&fact.left, &fact.right]
                .iter()
                .any(|obj| matches!(obj, Obj::MatrixOperator(MatrixOperator::Determinant(_))))
            {
                return self.compile_matrix_determinant_definition(fact, p, position);
            }
            if [&fact.left, &fact.right].iter().any(|obj| {
                matches!(
                    obj,
                    Obj::MatrixOperator(
                        MatrixOperator::EuclideanNorm(_) | MatrixOperator::FrobeniusNorm(_)
                    )
                )
            }) {
                return self.compile_matrix_norm_definition(fact, p, position);
            }
            if matches!(
                &fact.left,
                Obj::MatrixOperator(MatrixOperator::InnerProduct(_))
            ) || matches!(
                &fact.right,
                Obj::MatrixOperator(MatrixOperator::InnerProduct(_))
            ) {
                return self.compile_finite_inner_product_definition(fact, p, position);
            }
            return self.compile_matrix_trace_definition(fact, p, position);
        }
        if matches!(
            proof,
            MatrixEqualityProof::FunctionDefinition(_)
                | MatrixEqualityProof::ComponentDefinition(_)
        ) {
            return self.compile_matrix_operator_definition(fact, proof, position);
        }
        let MatrixEqualityProof::SpaceDefinition(proof) = proof else {
            return Err(LeanCompileError::unsupported("Matrix/DefinitionRule"));
        };
        let MatrixDefinitionResidualProof::Verified(residual) = proof.equality.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/ResidualRule"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported("Matrix/ResidualSubject"));
        };
        let expanded = Obj::FunctionSpace(FunctionSpace::FnSet(proof.signature.clone()));
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::SetFormer(SetFormer::MatrixSet(space)) = native else {
                continue;
            };
            Self::validate_matrix_signature(space, &proof.signature)?;
            if equality.left.ir() != expanded.ir() || equality.right.ir() != other.ir() {
                continue;
            }
            let matrix = self.compile_object_reference(native, position)?;
            let checked = self.compile_verify(residual, position)?.1;
            let forward = format!("((Litex.matrixSet_eq_fnSet {matrix}).trans {checked})");
            return Ok(if reversed {
                format!("{forward}.symm")
            } else {
                forward
            });
        }
        Err(LeanCompileError::unsupported("Matrix/DefinitionSubject"))
    }
}

impl LitexToLeanCompiler {
    fn compile_matrix_operator_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (callable, residual, expanded) = match proof {
            MatrixEqualityProof::FunctionDefinition(p) => (
                &p.callable,
                &p.equality,
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.callable.function.clone())),
            ),
            MatrixEqualityProof::ComponentDefinition(p) => {
                (&p.callable, &p.equality, p.reduction.value.clone())
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/DefinitionRule")),
        };
        Self::validate_matrix_callable(callable)?;
        if let (
            MatrixEqualityProof::ComponentDefinition(component),
            MatrixDefinitionResidualProof::ExactEvaluation(evaluation),
        ) = (proof, residual.as_ref())
        {
            return self.compile_identity_matrix_evaluation(fact, component, evaluation, position);
        }

        if let (
            MatrixEqualityProof::ComponentDefinition(component),
            MatrixDefinitionResidualProof::CheckedBeta(beta),
        ) = (proof, residual.as_ref())
        {
            return self.compile_matrix_checked_residual(fact, component, beta, position);
        }
        let MatrixDefinitionResidualProof::Verified(residual) = residual.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/ResidualRule"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported("Matrix/ResidualSubject"));
        };
        if equality.left.ir() != expanded.ir() {
            return Err(LeanCompileError::unsupported("Matrix/ResidualEndpoint"));
        }
        let root_obj = Obj::MatrixOperator(callable.operator.clone());
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if equality.right.ir() != other.ir() {
                continue;
            }
            let bridge = match proof {
                MatrixEqualityProof::FunctionDefinition(_) if native.ir() == root_obj.ir() => {
                    let root = self.compile_matrix_callable_root(callable, position)?;
                    let same = self.compile_equality_path(
                        native,
                        &root_obj,
                        &callable.function_equal,
                        position,
                    )?;
                    let formed = SourcePosition::new(
                        Some(position),
                        SourceOwner::Verify(residual),
                        usize::MAX,
                    );
                    let function = self.compile_object_reference(&expanded, &formed)?;
                    match &callable.operator {
                        MatrixOperator::ZeroMatrix(_) | MatrixOperator::IdentityMatrix(_) => {
                            format!(
                                "({same}.trans (show Litex.Same {root} {function} from by rfl))"
                            )
                        }
                        MatrixOperator::Add(_) | MatrixOperator::Subtract(_) => format!(
                            "({same}.trans (Litex.matrixEntrywise_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Apply(_) => format!(
                            "({same}.trans (Litex.matrixApply_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Multiply(_) => format!(
                            "({same}.trans (Litex.matrixMultiply_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Scale(_) => format!(
                            "({same}.trans (Litex.matrixScale_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::OuterProduct(_) => format!(
                            "({same}.trans (Litex.matrixOuter_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Adjugate(_) => format!(
                            "({same}.trans (Litex.matrixAdjugate_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Inverse(_) => format!(
                            "({same}.trans (Litex.matrixInverse_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Diagonal(_) => format!(
                            "({same}.trans (Litex.matrixDiagonal_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::Transpose(_) => format!(
                            "({same}.trans (Litex.transpose_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        MatrixOperator::ConjugateTranspose(_) => format!(
                            "({same}.trans (Litex.conjugateTranspose_eq_formula {root} {function} (by rfl) (by rfl)))"
                        ),
                        _ => {
                            return Err(LeanCompileError::unsupported(
                                "Matrix/FunctionDefinitionOperator",
                            ));
                        }
                    }
                }
                MatrixEqualityProof::ComponentDefinition(p) => {
                    if !matches!(native, Obj::FnObj(_)) {
                        continue;
                    }
                    let call_object = self.compile_object_reference(native, position)?;
                    let formed = SourcePosition::new(
                        Some(position),
                        SourceOwner::Verify(residual),
                        usize::MAX,
                    );
                    let endpoint = self.compile_object_reference(&expanded, &formed)?;
                    position
                        .with_visible_wd(native, &mut |wd, producer| {
                            let (body_value, step) = self.compile_matrix_component_step(
                                native,
                                &call_object,
                                callable,
                                &p.body,
                                wd,
                                producer,
                            )?;
                            let reduced = self.compile_matrix_component_reduction(
                                &p.body,
                                &body_value,
                                &p.reduction,
                                &format!("(Litex.denote {endpoint})"),
                                &formed,
                            )?;
                            Ok(format!("({step}.trans {reduced})"))
                        })?
                        .ok_or_else(|| LeanCompileError::unsupported("Matrix/ComponentProducer"))?
                }
                _ => continue,
            };
            let checked = self.compile_verify(residual, position)?.1;
            let term = format!("({bridge}.trans {checked})");
            return Ok(if reversed {
                format!("{term}.symm")
            } else {
                term
            });
        }
        Err(LeanCompileError::unsupported(
            "Matrix/OperatorDefinitionSubject",
        ))
    }
}
