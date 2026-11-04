//! Cauchy–Schwarz for the original finite inner product andnorm objects.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("CauchySchwarz/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn vector(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
        && matches!(&f.set,Obj::SetFormer(SetFormer::FiniteSeqSet(s))
            if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.n.ir()==n.ir()))
}
fn norm(obj: &Obj, a: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p)) if p.vector.ir()==a.ir() && p.dimension.ir()==n.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_cauchy_schwarz(
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
        if builtin.theorem != BuiltinTheoremId::InnerProductCauchySchwarz {
            return Err(invalid("Theorem"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let arity = 3;
        let count = 4;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, n) = (&args[0], &args[1], &args[2]);
        let req = &builtin.requirements;
        let valid = natural(&req[0], n)
            && vector(&req[1], a, n)
            && natural(&req[2], n)
            && vector(&req[3], b, n);
        if !valid {
            return Err(invalid("OriginalCarrierContexts"));
        }
        let Fact::AtomicFact(atomic @ AtomicFact::LessEqualFact(goal)) = &builtin.conclusions[0]
        else {
            return Err(invalid("OriginalInequality"));
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalInequalityWD"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(right)) = &goal.right else {
            return Err(invalid("OriginalNormProduct"));
        };
        if !norm(&right.left, a, n) || !norm(&right.right, b, n) {
            return Err(invalid("OrderedOriginalNorms"));
        }
        let Obj::ComplexOperator(ComplexOperator::ComplexAbs(modulus)) = &goal.left else {
            return Err(invalid("OriginalComplexModulus"));
        };
        if !matches!(modulus.arg.as_ref(),Obj::MatrixOperator(MatrixOperator::InnerProduct(p))
            if p.left.ir()==a.ir() && p.right.ir()==b.ir() && p.dimension.ir()==n.ir())
        {
            return Err(invalid("OriginalInnerProduct"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                stored,
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
        let bindings = self.compile_atomic_wd_locals(wd, atomic, &formed)?;
        let complete = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, 2),
            usize::MAX,
        );
        let root = self
            .compile_object_reference(&goal.left, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let term = format!("(by\n  let _cauchy_modulus := {root}\n  exact Litex.finiteInnerProductCauchySchwarz _cauchy_modulus.val.arg\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), term, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
