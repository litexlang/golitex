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
    pub(super) fn compile_builtin_inner_positive_theorem(
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
        if builtin.theorem != BuiltinTheoremId::InnerProductPositive
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let (
            [vector, dimension],
            [natural, member],
            [_, _],
            [_, _],
            [real, nonnegative, imaginary],
            [_, _, _],
        ) = (
            args.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        )
        else {
            return Err(invalid("Stages"));
        };
        if args != &builtin.arguments
            || !matches!(natural, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==dimension.ir() && f.set==Obj::StandardSet(StandardSet::N))
        {
            return Err(invalid("OriginalDimension"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = member else {
            return Err(invalid("OriginalVector"));
        };
        let Obj::SetFormer(SetFormer::FiniteSeqSet(carrier)) = &member.set else {
            return Err(invalid("OriginalVector"));
        };
        if member.element.ir() != vector.ir()
            || carrier.n.ir() != dimension.ir()
            || carrier.set.as_ref() != &Obj::StandardSet(StandardSet::C)
        {
            return Err(invalid("OriginalVector"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(real)) = real else {
            return Err(invalid("RealConclusion"));
        };
        let inner = &real.element;
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = inner else {
            return Err(invalid("SelfInnerProduct"));
        };
        if real.set != Obj::StandardSet(StandardSet::R)
            || p.left.ir() != vector.ir()
            || p.right.ir() != vector.ir()
            || p.dimension.ir() != dimension.ir()
        {
            return Err(invalid("SelfInnerProduct"));
        }
        let Fact::AtomicFact(AtomicFact::LessEqualFact(bound)) = nonnegative else {
            return Err(invalid("NonnegativeConclusion"));
        };
        let Obj::ComplexOperator(ComplexOperator::RealPart(part)) = &bound.right else {
            return Err(invalid("RealProjection"));
        };
        if closed_integer(&bound.left) != Some(0) || part.arg.ir() != inner.ir() {
            return Err(invalid("RealProjection"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(zero)) = imaginary else {
            return Err(invalid("ImaginaryConclusion"));
        };
        let Obj::ComplexOperator(ComplexOperator::ImaginaryPart(part)) = &zero.left else {
            return Err(invalid("ImaginaryProjection"));
        };
        if closed_integer(&zero.right) != Some(0) || part.arg.ir() != inner.ir() {
            return Err(invalid("ImaginaryProjection"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, proof), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(proof)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let checked = self.compile_verify(proof, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &checked, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(checked.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: 2,
            ..*position
        };
        let mut proofs = Vec::new();
        for (index, (conclusion, wd)) in builtin.conclusions.iter().zip(conclusions_wd).enumerate()
        {
            let statement = self.compile_formed_fact_proposition(wd, conclusion, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let subject = match index {
                0 => inner,
                1 => &bound.right,
                _ => &zero.left,
            };
            let object = self
                .compile_object_reference(subject, &scope)?
                .replace('\n', "\n  ");
            let proof = match index {
                0 => format!("(Litex.finiteInnerProductSelfPositive {object} (by rfl)).1"),
                1 => format!("(by\n  let _inner_re := {object}\n  have _positive := Litex.finiteInnerProductSelfPositive _inner_re.val.arg (by rfl)\n  change Litex.realBound true (M.number 0) (Litex.complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (Litex.denote _inner_re.val.arg))\n  rw [Litex.realPartOfRealValue _ _positive.1]\n  exact _positive.2\n)"),
                _ => format!("(by\n  let _inner_img := {object}\n  have _positive := Litex.finiteInnerProductSelfPositive _inner_img.val.arg (by rfl)\n  exact Litex.imaginaryPartOfRealValue (Litex.denote _inner_img.val.arg) _positive.1\n)"),
            };
            proofs.push(format!("(show {statement} from {proof})"));
        }
        Ok((
            definitions,
            proofs
                .into_iter()
                .rev()
                .reduce(|tail, head| format!("(And.intro {head} {tail})"))
                .unwrap(),
            builtin.conclusions.clone(),
        ))
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("InnerPositive/{stage}"),
        "Self inner-product positivity evidence has another original vector, dimension, field projection or formation stage.")
}
