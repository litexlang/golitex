//! Replay the original Frobenius scaling schema and its complete evidence.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

pub(super) fn validate_frobenius_scale_law(
    theorem: BuiltinTheoremId,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    if theorem != BuiltinTheoremId::FrobeniusNormScale {
        return Err(LeanCompileError::unsupported("FrobeniusScale/Theorem"));
    }
    let [z, a, m, n] = args else {
        return Err(LeanCompileError::unsupported("FrobeniusScale/Arguments"));
    };
    if requirements.len() != 4 {
        return Err(LeanCompileError::unsupported("FrobeniusScale/Stages"));
    }
    for (index, expected) in [z, m, n, a].into_iter().enumerate() {
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &requirements[index] else {
            return Err(LeanCompileError::unsupported("FrobeniusScale/Premise"));
        };
        let valid = f.element.ir() == expected.ir()
            && match index {
                0 => f.set == Obj::StandardSet(StandardSet::C),
                1 | 2 => f.set == Obj::StandardSet(StandardSet::N),
                3 => matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(p))
                if p.set.as_ref()==&Obj::StandardSet(StandardSet::C) && p.rows.ir()==m.ir() && p.cols.ir()==n.ir()),
                _ => unreachable!(),
            };
        if !valid {
            return Err(LeanCompileError::unsupported("FrobeniusScale/Premise"));
        }
    }
    let Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(norm)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("FrobeniusScale/Conclusion"));
    };
    let valid = norm.rows.ir() == m.ir()
        && norm.cols.ir() == n.ir()
        && matches!(norm.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::Scale(p))
            if p.scalar.ir()==z.ir() && p.matrix.ir()==a.ir() && p.rows.ir()==m.ir() && p.cols.ir()==n.ir())
        && matches!(&conclusion.right, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p))
            if matches!(p.left.as_ref(), Obj::ComplexOperator(ComplexOperator::ComplexAbs(v)) if v.arg.ir()==z.ir())
                && matches!(p.right.as_ref(), Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(v))
                    if v.matrix.ir()==a.ir() && v.rows.ir()==m.ir() && v.cols.ir()==n.ir()));
    if !valid {
        return Err(LeanCompileError::unsupported("FrobeniusScale/Subjects"));
    }
    Ok(4)
}

pub(super) fn frobenius_scale_law_term(root: &str, statement: &str) -> String {
    format!("(show {statement} from by\n  let _norm := {root}\n  exact Litex.frobeniusNormScale _norm.val.matrix.val.scalar _norm.val.matrix.val.matrix _norm.val.rows _norm.val.cols _norm.val.matrix.wd.1 _norm.wd.1 _norm.wd.2.1 _norm.val.matrix.wd.2.2.2\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_frobenius_scale_theorem(
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
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("FrobeniusScale/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "FrobeniusScale/TheoremStages",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("FrobeniusScale/Conclusion"));
        };
        validate_frobenius_scale_law(builtin.theorem, args, &builtin.requirements, conclusion)?;
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "FrobeniusScale/RequirementIdentity",
                ));
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
            before: 4,
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
        Ok((
            definitions,
            frobenius_scale_law_term(&root, &statement),
            builtin.conclusions.clone(),
        ))
    }
}
