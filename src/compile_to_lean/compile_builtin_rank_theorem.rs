//! Explicit rank bounds and zero/identity laws from the original theorem result.
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
    pub(super) fn compile_builtin_rank_theorem(
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
        use BuiltinTheoremId::{MatrixRankBounds, MatrixRankIdentity, MatrixRankZero};
        let (arity, count) = match builtin.theorem {
            MatrixRankBounds => (3, 3),
            MatrixRankZero => (2, 1),
            MatrixRankIdentity => (1, 1),
            _ => return Err(LeanCompileError::unsupported("Rank/Theorem")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("Rank/TheoremContract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("Rank/Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != arity
            || builtin.requirements.len() != arity
            || dom_proofs.len() != arity
            || dom_stores.len() != arity
            || builtin.conclusions.len() != count
            || conclusions_wd.len() != count
        {
            return Err(LeanCompileError::unsupported("Rank/TheoremStages"));
        }
        let (rows, cols) = match builtin.theorem {
            MatrixRankBounds => (&arguments[1], &arguments[2]),
            MatrixRankZero => (&arguments[0], &arguments[1]),
            _ => (&arguments[0], &arguments[0]),
        };
        let native = match &builtin.conclusions[0] {
            Fact::AtomicFact(AtomicFact::InFact(f))
                if builtin.theorem == MatrixRankBounds
                    && f.set == Obj::StandardSet(StandardSet::N) =>
            {
                &f.element
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f))
                if builtin.theorem == MatrixRankZero && closed_integer(&f.right) == Some(0) =>
            {
                &f.left
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f))
                if builtin.theorem == MatrixRankIdentity && f.right.ir() == rows.ir() =>
            {
                &f.left
            }
            _ => return Err(LeanCompileError::unsupported("Rank/FirstConclusion")),
        };
        let Obj::MatrixOperator(MatrixOperator::Rank(rank)) = native else {
            return Err(LeanCompileError::unsupported("Rank/ConclusionObject"));
        };
        let matrix_matches = match builtin.theorem {
            MatrixRankBounds => rank.matrix.ir() == arguments[0].ir(),
            MatrixRankZero => {
                matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::ZeroMatrix(p)) if p.rows.ir()==rows.ir() && p.cols.ir()==cols.ir())
            }
            _ => {
                matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) if p.order.ir()==rows.ir())
            }
        };
        if !matrix_matches || rank.rows.ir() != rows.ir() || rank.cols.ir() != cols.ir() {
            return Err(LeanCompileError::unsupported("Rank/ConclusionDimensions"));
        }
        if builtin.theorem == MatrixRankBounds {
            for (index, dimension) in [rows, cols].iter().enumerate() {
                if !matches!(&builtin.conclusions[index+1],Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==native.ir() && f.right.ir()==dimension.ir())
                {
                    return Err(LeanCompileError::unsupported("Rank/BoundConclusion"));
                }
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
            let expected = if index < 2 {
                let subject = if index == 0 { rows } else { cols };
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set==Obj::StandardSet(StandardSet::N))
            } else {
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==rank.matrix.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m)) if m.set.as_ref()==&Obj::StandardSet(StandardSet::C) && m.rows.ir()==rows.ir() && m.cols.ir()==cols.ir()))
            };
            if !expected || source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("Rank/TheoremPremise"));
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
            let law = match builtin.theorem {
                MatrixRankBounds => match index {
                    0 => "Litex.matrixRankInN _rank",
                    1 => "Litex.matrixRankLeRows _rank",
                    _ => "Litex.matrixRankLeCols _rank",
                },
                MatrixRankZero => {
                    "Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1"
                }
                _ => "Litex.matrixRankIdentity _rank.val.rows _rank.wd.1",
            };
            proofs.push(format!(
                "(show {statement} from by\n  let _rank := {root}\n  exact {law}\n)"
            ));
        }
        Ok((
            definitions,
            proofs
                .into_iter()
                .rev()
                .reduce(|right, left| format!("(And.intro {left} {right})"))
                .expect("rank conclusions"),
            builtin.conclusions.clone(),
        ))
    }
}
