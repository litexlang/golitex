//! Fixed vector-law schemas over the actual original application stages.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn vector_member(fact: &Fact, vector: &Obj, dimension: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==vector.ir()
        && matches!(&f.set,Obj::SetFormer(SetFormer::FiniteSeqSet(s)) if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.n.ir()==dimension.ir()))
}

pub(super) fn validate_inner_symmetry_law(
    theorem: BuiltinTheoremId,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    if theorem != BuiltinTheoremId::InnerProductConjugateSymmetry
        || args.len() != 3
        || requirements.len() != 4
    {
        return Err(LeanCompileError::unsupported("InnerSymmetry/Stages"));
    }
    let (u, v, n) = (&args[0], &args[1], &args[2]);
    let Obj::MatrixOperator(MatrixOperator::InnerProduct(left)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("InnerSymmetry/Conclusion"));
    };
    let Obj::ComplexOperator(ComplexOperator::Conjugate(conjugate)) = &conclusion.right else {
        return Err(LeanCompileError::unsupported("InnerSymmetry/Conjugate"));
    };
    let Obj::MatrixOperator(MatrixOperator::InnerProduct(right)) = conjugate.arg.as_ref() else {
        return Err(LeanCompileError::unsupported("InnerSymmetry/Conclusion"));
    };
    if left.left.ir() != u.ir()
        || left.right.ir() != v.ir()
        || left.dimension.ir() != n.ir()
        || right.left.ir() != v.ir()
        || right.right.ir() != u.ir()
        || right.dimension.ir() != n.ir()
    {
        return Err(LeanCompileError::unsupported("InnerSymmetry/Subjects"));
    }
    for (index, fact) in requirements.iter().enumerate() {
        let valid = if index % 2 == 0 {
            matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
        } else {
            vector_member(fact, &args[index / 2], n)
        };
        if !valid {
            return Err(LeanCompileError::unsupported("InnerSymmetry/Premise"));
        }
    }
    Ok(4)
}

pub(super) fn validate_euclidean_inner_law(
    theorem: BuiltinTheoremId,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    if theorem != BuiltinTheoremId::EuclideanNormSquare
        || args.len() != 2
        || requirements.len() != 2
    {
        return Err(LeanCompileError::unsupported("EuclideanInner/Stages"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(square)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("EuclideanInner/Power"));
    };
    let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) = square.base.as_ref() else {
        return Err(LeanCompileError::unsupported("EuclideanInner/Norm"));
    };
    let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &conclusion.right else {
        return Err(LeanCompileError::unsupported("EuclideanInner/Inner"));
    };
    if closed_integer(&square.exponent) != Some(2)
        || norm.vector.ir() != args[0].ir()
        || norm.dimension.ir() != args[1].ir()
        || inner.left.ir() != args[0].ir()
        || inner.right.ir() != args[0].ir()
        || inner.dimension.ir() != args[1].ir()
    {
        return Err(LeanCompileError::unsupported("EuclideanInner/Subjects"));
    }
    if !matches!(&requirements[0],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir() && f.set==Obj::StandardSet(StandardSet::N))
        || !vector_member(&requirements[1], &args[0], &args[1])
    {
        return Err(LeanCompileError::unsupported("EuclideanInner/Premise"));
    }
    Ok(2)
}

pub(super) fn inner_symmetry_law_term(root: &str, statement: &str) -> String {
    format!("(show {statement} from Litex.finiteInnerProductConjugateSymmetry {root})")
}

pub(super) fn euclidean_inner_law_term(norm: &str, statement: &str) -> String {
    format!("(show {statement} from Litex.euclideanNormSquareInner {norm})")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_inner_symmetry_theorem(
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
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
        {
            return Err(LeanCompileError::unsupported("InnerSymmetry/TheoremStages"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("InnerSymmetry/Arguments"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("InnerSymmetry/Conclusion"));
        };
        if args != &builtin.arguments || call.name.local_name() != builtin.theorem.as_str() {
            return Err(LeanCompileError::unsupported(
                "InnerSymmetry/TheoremIdentity",
            ));
        }
        validate_inner_symmetry_law(builtin.theorem, args, &builtin.requirements, conclusion)?;
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
                    "InnerSymmetry/RequirementIdentity",
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
            inner_symmetry_law_term(&root, &statement),
            builtin.conclusions.clone(),
        ))
    }
}
