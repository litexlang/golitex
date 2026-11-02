use super::compile_real_set_bounds::contains_parameter;
use super::helper::{ensure_object, source_subject};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_finite_index_theorem(
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
        if builtin.theorem != BuiltinTheoremId::FiniteSetHasBijectiveIndex
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let ([argument], [requirement], [checked], [store], [conclusion], [wd]) = (
            arguments.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        ) else {
            return Err(invalid("Stages"));
        };
        if arguments != &builtin.arguments
            || !matches!(requirement,Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f))if f.set.ir()==argument.ir())
        {
            return Err(invalid("FiniteSubject"));
        }
        let (sequence, range) = validate_conclusion(argument, conclusion)?;
        if source_subject(checked)? != *requirement {
            return Err(invalid("OriginalRequirement"));
        }
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let proof = self.compile_verify(checked, &prior)?;
        self.validate_store(&store.store, requirement)?;
        let mut definitions = vec![self.emit_internal_fact(requirement, &proof, &prior)?];
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let member = format!("h_{}", requirement.fact_id().value());
        definitions.extend(self.compile_stored_inferences(
            store,
            requirement,
            &(proof.0, member.clone()),
            &formed,
        )?);
        self.compile_fact_wd(wd, conclusion, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, conclusion, &formed)?;
        let argument = self
            .compile_object_reference(argument, &scope)?
            .replace('\n', "\n  ");
        let FactWellDefinedProof::ExistFact(formation) = wd else {
            return Err(invalid("ExistFormation"));
        };
        let [ParamTypeWellDefinedProof::Obj(sequence_wd)] = formation
            .detailed_ref()
            .introduced_params
            .param_type_well_defined
            .as_slice()
        else {
            return Err(invalid("OriginalSequenceFormation"));
        };
        let [body] = formation.detailed_ref().assumed_body_facts.as_slice() else {
            return Err(invalid("OriginalBodyFormation"));
        };
        let FactWellDefinedProof::AtomicExceptEquality(body_wd) = &body.well_defined else {
            return Err(invalid("OriginalBijectionFormation"));
        };
        let [range_wd, _, _] = body_wd
            .detailed_ref()
            .well_defined_of_each_parameter
            .as_slice()
        else {
            return Err(invalid("OriginalRangeFormation"));
        };
        ensure_object(sequence, sequence_wd)?;
        ensure_object(range, range_wd)?;
        // Replay the original formation children in the enclosing scope.
        // Neither the existential binder nor its hypothetical body is exposed
        // as an assumption while constructing this witness.
        let sequence = self.compile_wd(sequence_wd, &formed)?.replace('\n', "\n  ");
        let range = self.compile_wd(range_wd, &formed)?.replace('\n', "\n  ");
        let proof=format!("(show {statement} from (by\n  let _fi_argument := {argument}\n  let _fi_sequence := {sequence}\n  let _fi_range := {range}\n  rcases Litex.finiteSetBijectiveIndexWitness _fi_argument {member} _fi_sequence _fi_range rfl rfl rfl rfl with ⟨_fi_index, _fi_member, _fi_bijective⟩\n  exact ⟨_fi_index, _fi_member, _fi_bijective⟩\n))");
        Ok((definitions, proof, builtin.conclusions.clone()))
    }
}
fn validate_conclusion<'a>(
    argument: &Obj,
    conclusion: &'a Fact,
) -> Result<(&'a Obj, &'a Obj), LeanCompileError> {
    let Fact::ExistFact(fact) = conclusion else {
        return Err(invalid("ExistConclusion"));
    };
    let [group] = fact.typed_parameters.groups.as_slice() else {
        return Err(invalid("BinderGroups"));
    };
    let [index] = group.params.as_slice() else {
        return Err(invalid("BinderCount"));
    };
    let ParamType::Obj(sequence) = &group.param_type else {
        return Err(invalid("BinderDomain"));
    };
    let Obj::SetFormer(SetFormer::FiniteSeqSet(seq)) = sequence else {
        return Err(invalid("SequenceDomain"));
    };
    let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = seq.n.as_ref() else {
        return Err(invalid("SequenceCardinality"));
    };
    if seq.set.ir() != argument.ir()
        || size.set.ir() != argument.ir()
        || contains_parameter(argument, index.id)
    {
        return Err(invalid("SequenceSubject"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::BijectiveFact(body))] = fact.facts.as_slice()
    else {
        return Err(invalid("BijectiveBody"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = &body.domain else {
        return Err(invalid("IndexDomain"));
    };
    if body.codomain.ir() != argument.ir()
        || body.function.ir() != Obj::Identifier(IdentifierObj::from_bound_name(index)).ir()
        || range.end.ir() != seq.n.ir()
        || !matches!(range.start.as_ref(),Obj::Literal(Literal::Number(n))if n.normalized_value=="1")
    {
        return Err(invalid("IndexAndBijection"));
    }
    Ok((sequence, &body.domain))
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FiniteIndex/{part}"))
}
