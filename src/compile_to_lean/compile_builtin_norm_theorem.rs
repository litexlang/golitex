use super::compile_matrix_norm::validate_norm_sum;
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
    pub(super) fn compile_builtin_norm_theorem(
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
        let euclidean = match builtin.theorem {
            BuiltinTheoremId::EuclideanNormSquare => true,
            BuiltinTheoremId::FrobeniusNormSquare => false,
            _ => return Err(LeanCompileError::unsupported("NormSquare/Theorem")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("NormSquare/Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("NormSquare/Arguments"));
        };
        let arity = if euclidean { 2 } else { 3 };
        let count = if euclidean { 3 } else { 2 };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != arity
            || builtin.requirements.len() != arity
            || dom_proofs.len() != arity
            || dom_stores.len() != arity
            || builtin.conclusions.len() != count
            || conclusions_wd.len() != count
        {
            return Err(LeanCompileError::unsupported("NormSquare/Stages"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(first)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("NormSquare/FirstConclusion"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(square)) = &first.left else {
            return Err(LeanCompileError::unsupported("NormSquare/Power"));
        };
        if closed_integer(&square.exponent) != Some(2) {
            return Err(LeanCompileError::unsupported("NormSquare/Exponent"));
        }
        let native = square.base.as_ref();
        let carrier = match native {
            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p))
                if euclidean
                    && p.vector.ir() == arguments[0].ir()
                    && p.dimension.ir() == arguments[1].ir() =>
            {
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: p.dimension.clone(),
                }))
            }
            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p))
                if !euclidean
                    && p.matrix.ir() == arguments[0].ir()
                    && p.rows.ir() == arguments[1].ir()
                    && p.cols.ir() == arguments[2].ir() =>
            {
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: p.rows.clone(),
                    cols: p.cols.clone(),
                }))
            }
            _ => return Err(LeanCompileError::unsupported("NormSquare/NativeSubject")),
        };
        validate_norm_sum(native, &first.right)?;
        if euclidean {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &builtin.conclusions[1] else {
                return Err(LeanCompileError::unsupported("NormSquare/InnerConclusion"));
            };
            if f.left.ir() != first.left.ir()
                || !matches!(&f.right, Obj::MatrixOperator(MatrixOperator::InnerProduct(p))
                if p.left.ir() == arguments[0].ir() && p.right.ir() == arguments[0].ir() && p.dimension.ir() == arguments[1].ir())
            {
                return Err(LeanCompileError::unsupported("NormSquare/InnerSubject"));
            }
        }
        if !matches!(&builtin.conclusions[count-1], Fact::AtomicFact(AtomicFact::LessEqualFact(f))
            if closed_integer(&f.left) == Some(0) && f.right.ir() == native.ir())
        {
            return Err(LeanCompileError::unsupported(
                "NormSquare/NonnegativeConclusion",
            ));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            let (subject, set) = if index + 1 == arity {
                (&arguments[0], &carrier)
            } else {
                (&arguments[index + 1], &Obj::StandardSet(StandardSet::N))
            };
            if !matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==set.ir())
                || source_subject(checked)? != *requirement
            {
                return Err(LeanCompileError::unsupported("NormSquare/Premise"));
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
            before: arity,
            ..*position
        };
        let mut proofs = Vec::new();
        for (index, (fact, wd)) in builtin.conclusions.iter().zip(conclusions_wd).enumerate() {
            self.compile_fact_wd(wd, fact, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let root = self.compile_object_reference(native, &scope)?;
            let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
            let name = if euclidean {
                "euclideanNorm"
            } else {
                "frobeniusNorm"
            };
            let body = if index == 0 {
                let expanded = self.compile_object_reference(&first.right, &scope)?;
                format!(
                    "(Litex.{name}Square {root}).trans (congrArg M.number (Litex.{name}SumFormula {root} ({expanded}).val.function (by rfl) (by rfl)))"
                )
            } else if euclidean && index == 1 {
                format!("Litex.euclideanNormSquareInner {root}")
            } else {
                format!("Litex.{name}Nonnegative {root}")
            };
            proofs.push(format!("(show {statement} from {body})"));
        }
        Ok((
            definitions,
            proofs
                .into_iter()
                .rev()
                .reduce(|right, left| format!("(And.intro {left} {right})"))
                .expect("nonempty norm conclusions"),
            builtin.conclusions.clone(),
        ))
    }
}
