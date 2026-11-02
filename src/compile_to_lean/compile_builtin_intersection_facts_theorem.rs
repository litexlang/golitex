use super::compile_real_set_bounds::contains_parameter;
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
    pub(super) fn compile_builtin_intersection_facts_theorem(
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
        if builtin.theorem != BuiltinTheoremId::FamilyIntersectionMemberFacts
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
            [element, intersection],
            [is_set, nonempty, member],
            [_, _, _],
            [_, _, _],
            [Fact::ForallFact(conclusion)],
            [FactWellDefinedProof::ForallFact(_)],
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
        let Obj::SetOperator(SetOperator::FamilyIntersect(family)) = intersection else {
            return Err(invalid("IntersectionConstructor"));
        };
        if args != &builtin.arguments
            || !matches!(is_set,Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==family.left.ir())
            || !matches!(nonempty,Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==family.left.ir())
            || !matches!(member,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==element.ir() && f.set.ir()==intersection.ir())
        {
            return Err(invalid("OriginalRequirements"));
        }
        validate_conclusion(conclusion, element, &family.left)?;
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
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
            before: 3,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let VerifyFactResult::AtomicExceptEquality(proof) = &dom_proofs[2] else {
            return Err(invalid("MemberFormation"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
            return Err(invalid("MemberFormation"));
        };
        // Reuse the actual required membership's construction evidence locally.
        // The generated forall does not own an intersection constructor itself.
        let prior = SourcePosition {
            before: 2,
            ..*position
        };
        let bindings =
            self.compile_atomic_wd_locals(&proof.well_defined_proof, &proof.fact, &prior)?;
        let complete = SourcePosition::new(
            Some(&prior),
            SourceOwner::AtomicWDLocals(&proof.well_defined_proof, 2),
            usize::MAX,
        );
        let intersection = self
            .compile_object_reference(intersection, &complete)?
            .replace('\n', "\n  ");
        let element = self
            .compile_object_reference(element, &complete)?
            .replace('\n', "\n  ");
        let hypothesis = format!("h_{}", member.fact_id().value());
        let term=format!("(by\n  let _intersection := {intersection}\n  let _element := {element}\n  exact (fun {{_Host : Type _}} [_rep : Litex.Representation M _Host] (_factor : Litex.Obj (M := M) _Host) _member _isSet => (Litex.familyIntersect_members _intersection (Litex.denote _element)).mp {hypothesis} (Litex.denote (M := M) _factor) _member)\n)");
        let term = Self::scope_equal_wd_proof(statement.clone(), term, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {term})"),
            builtin.conclusions.clone(),
        ))
    }
}
fn validate_conclusion(
    fact: &ForallFact,
    element: &Obj,
    family: &Obj,
) -> Result<(), LeanCompileError> {
    let [group] = fact.typed_parameters.groups.as_slice() else {
        return Err(invalid("BinderGroups"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("BinderCount"));
    };
    let ParamType::Obj(domain) = &group.param_type else {
        return Err(invalid("BinderCarrier"));
    };
    let [Fact::AtomicFact(AtomicFact::IsSetFact(guard))] = fact.dom_facts.as_slice() else {
        return Err(invalid("SetGuard"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(body))] =
        fact.then_facts.as_slice()
    else {
        return Err(invalid("MemberBody"));
    };
    if domain.ir() != family.ir()
        || contains_parameter(element, parameter.id)
        || contains_parameter(family, parameter.id)
        || !matches!(&guard.set,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
        || !matches!(&body.set,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
        || body.element.ir() != element.ir()
    {
        return Err(invalid("OriginalConclusion"));
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("IntersectionFacts/{part}"))
}
