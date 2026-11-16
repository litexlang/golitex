//! Replay each recorded native beta/congruence step, followed by the checked scalar proof.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::matrix_entry_normalization_proof::*;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_entry_reduction(
        &self,
        goal: &EqualFact,
        proof: &MatrixEntryReductionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(&goal.left, &proof.left.source_wd)?;
        ensure_object(&goal.right, &proof.right.source_wd)?;
        let VerifyFactResult::Equality(scalar) = &proof.scalar_equality else {
            return Err(LeanCompileError::unsupported("MatrixEntry/ScalarEquality"));
        };
        let VerifyEqualityResult::Success(scalar) = scalar.as_ref() else {
            return Err(LeanCompileError::unsupported("MatrixEntry/ScalarFailure"));
        };
        if scalar.fact.left.ir() != proof.left.value.ir()
            || scalar.fact.right.ir() != proof.right.value.ir()
        {
            return Err(LeanCompileError::unsupported("MatrixEntry/ScalarEndpoints"));
        }
        let mut lines =
            self.compile_equal_wd_locals(&scalar.fact, &scalar.well_defined_proof, position)?;
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::EqualWDLocals(&scalar.well_defined_proof, 2),
            2,
        );
        let checked = match &scalar.searched_proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Conjugation(p),
            ) => self.compile_conjugate_identity(&scalar.fact, p, true, &scope)?,
            _ => self.compile_equality_search_with_parent_wd(
                &scalar.fact,
                &scalar.searched_proof,
                Some(&scalar.well_defined_proof),
                &scope,
            )?,
        };
        let (a, ha) = self.compile_matrix_entry_normalization(&proof.left, &scope)?;
        let (b, hb) = self.compile_matrix_entry_normalization(&proof.right, &scope)?;
        let left = self.compile_object_reference(&goal.left, position)?;
        let right = self.compile_object_reference(&goal.right, position)?;
        let x = self.compile_object_reference(&scalar.fact.left, &scope)?;
        let y = self.compile_object_reference(&scalar.fact.right, &scope)?;
        lines.push(format!("have _left : Litex.denote {left} = Litex.denote {x} := (show Litex.denote {left} = {a} from {ha}).trans (by rfl)"));
        lines.push(format!("have _right : Litex.denote {right} = Litex.denote {y} := (show Litex.denote {right} = {b} from {hb}).trans (by rfl)"));
        lines.push(format!("exact _left.trans (({checked}).trans _right.symm)"));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    fn compile_matrix_entry_normalization(
        &self,
        proof: &MatrixEntryNormalizationProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let source = proof.source_wd.obj();
        let object = self.compile_wd(&proof.source_wd, position)?;
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&proof.source_wd),
            usize::MAX,
        );
        let start = format!("(Litex.denote {object})");
        match &proof.step {
            MatrixEntryNormalizationStep::Unchanged => {
                if source.ir() != proof.value.ir() {
                    return Err(LeanCompileError::unsupported("MatrixEntry/Identity"));
                }
                Ok((start.clone(), format!("(Eq.refl {start})")))
            }
            MatrixEntryNormalizationStep::NativeCall(p) => {
                if p.body.ir() != p.continuation.source_wd.obj().ir()
                    || p.continuation.value.ir() != proof.value.ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "MatrixEntry/NativeContinuation",
                    ));
                }
                let (raw, step) = self.compile_matrix_component_step(
                    source,
                    &object,
                    &p.callable,
                    &p.body,
                    None,
                    &proof.source_wd,
                    position,
                )?;
                let (value, continuation) =
                    self.compile_matrix_entry_normalization(&p.continuation, &scope)?;
                Ok((
                    value.clone(),
                    format!("({step}.trans (show {raw} = {value} from {continuation}))"),
                ))
            }
            MatrixEntryNormalizationStep::Conjugate(p) => {
                let (
                    Obj::ComplexOperator(ComplexOperator::Conjugate(a)),
                    Obj::ComplexOperator(ComplexOperator::Conjugate(b)),
                ) = (source, &proof.value)
                else {
                    return Err(LeanCompileError::unsupported("MatrixEntry/Conjugate"));
                };
                ensure_object(&a.arg, &p.source_wd)?;
                if b.arg.ir() != p.value.ir() {
                    return Err(LeanCompileError::unsupported(
                        "MatrixEntry/ConjugateEndpoint",
                    ));
                }
                let (value, step) = self.compile_matrix_entry_normalization(p, &scope)?;
                let f = "(Litex.complexUnaryValue (M := M) (fun z : ℂ => star z))";
                Ok((
                    format!("({f} {value})"),
                    format!("(show {start} = {f} {value} from congrArg {f} {step})"),
                ))
            }
            MatrixEntryNormalizationStep::Add(a, b)
            | MatrixEntryNormalizationStep::Subtract(a, b)
            | MatrixEntryNormalizationStep::Multiply(a, b) => {
                let (left, right, x, y, op) = match (source, &proof.value, &proof.step) {
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(q)),
                        MatrixEntryNormalizationStep::Add(..),
                    ) => (&p.left, &p.right, &q.left, &q.right, "add"),
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(q)),
                        MatrixEntryNormalizationStep::Subtract(..),
                    ) => (&p.left, &p.right, &q.left, &q.right, "sub"),
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(q)),
                        MatrixEntryNormalizationStep::Multiply(..),
                    ) => (&p.left, &p.right, &q.left, &q.right, "mul"),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "MatrixEntry/BinaryConstructor",
                        ))
                    }
                };
                ensure_object(left, &a.source_wd)?;
                ensure_object(right, &b.source_wd)?;
                if x.ir() != a.value.ir() || y.ir() != b.value.ir() {
                    return Err(LeanCompileError::unsupported("MatrixEntry/BinaryEndpoints"));
                }
                let (a, ha) = self.compile_matrix_entry_normalization(a, &scope)?;
                let (b, hb) = self.compile_matrix_entry_normalization(b, &scope)?;
                let value = format!("(M.{op}Value {a} {b})");
                Ok((
                    value.clone(),
                    format!("(show {start} = {value} from congrArg₂ M.{op}Value {ha} {hb})"),
                ))
            }
        }
    }
}
