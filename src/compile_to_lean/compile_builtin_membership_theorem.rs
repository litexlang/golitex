use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_membership_theorem(
        &self,
        call: &TheoremCall,
        builtin: Option<&BuiltinThmApplication>,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let Some(builtin) = builtin else {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Application",
            ));
        };
        if !matches!(
            builtin.theorem,
            BuiltinTheoremId::SetBuilderMember
                | BuiltinTheoremId::DefinedSetMember
                | BuiltinTheoremId::CartesianMemberFromCoordinates
                | BuiltinTheoremId::FunctionSetMember
        ) || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
        {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Contract"));
        }
        let (AtomicName::Plain { name }, TheoremCallArguments::Parenthesized(arguments)) =
            (&call.name, &call.arguments)
        else {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Arguments"));
        };
        if name != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != 2
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
            || dom_proofs.len() != builtin.requirements.len()
            || dom_stores.len() != dom_proofs.len()
        {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Stages"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Conclusion",
            ));
        };
        if member.element.ir() != arguments[0].ir() || member.set.ir() != arguments[1].ir() {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Conclusion",
            ));
        }
        let mut definitions = Vec::new();
        let domain = match (builtin.theorem, function_domain) {
            (
                BuiltinTheoremId::CartesianMemberFromCoordinates
                | BuiltinTheoremId::FunctionSetMember,
                Some(BuiltinFunctionDomainProof::Membership(domain)),
            ) => Some(domain),
            (BuiltinTheoremId::SetBuilderMember | BuiltinTheoremId::DefinedSetMember, None) => None,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "BuiltinMembership/CompleteDomain",
                ))
            }
        };
        let domain_complete = if let Some(domain) = domain {
            ensure_object(&arguments[0], &domain.function_wd)?;
            ensure_object(
                &Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone())),
                &domain.target_wd,
            )?;
            let prior =
                SourcePosition::new(Some(position), SourceOwner::FunctionDomainWD(domain), 0);
            let function = self.compile_wd(&domain.function_wd, &prior)?;
            let formed = SourcePosition { before: 1, ..prior };
            let target = self.compile_wd(&domain.target_wd, &formed)?;
            definitions.push(format!("let _membership_function := {function}"));
            definitions.push(format!("let _membership_target := {target}"));
            Some(SourcePosition { before: 2, ..prior })
        } else {
            None
        };
        let invocation = SourcePosition {
            parent: domain_complete.as_ref().or(position.parent),
            ..*position
        };
        let position = &invocation;
        let mut references = Vec::new();
        for (index, ((requirement, proof), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported("BuiltinMembership/Premise"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(proof, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            let published = SourcePosition {
                before: index + 1,
                ..*position
            };
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, reference.clone()),
                &published,
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: dom_proofs.len(),
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let formation = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let application = match builtin.theorem {
            BuiltinTheoremId::SetBuilderMember => self.compile_builder_membership_evidence(
                member,
                &builtin.requirements,
                references,
                &formation,
            )?,
            BuiltinTheoremId::DefinedSetMember => {
                if !matches!(
                    member.set,
                    Obj::Identifier(_) | Obj::InstantiatedTemplateObj(_)
                ) || builtin.requirements.len() != 1
                    || builtin.requirements[0].ir() != builtin.conclusions[0].ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "BuiltinMembership/DefinedSet",
                    ));
                }
                references.remove(0)
            }
            BuiltinTheoremId::CartesianMemberFromCoordinates => self
                .compile_builtin_cart_membership(
                    member,
                    domain.unwrap(),
                    &builtin.requirements,
                    &references,
                    &formation,
                )?,
            BuiltinTheoremId::FunctionSetMember => self.compile_builtin_function_membership(
                member,
                domain.unwrap(),
                &builtin.requirements,
                &references,
                &formation,
            )?,
            _ => unreachable!(),
        };
        Ok((definitions, application, builtin.conclusions.clone()))
    }
}
