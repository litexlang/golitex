use crate::compile_to_lean::helper::{ensure_object, source_subject};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ExecReleaseAxiomOfChoiceStmtResult, ExecReleaseAxiomOfChoiceStmtSuccess,
};
use crate::prelude::*;

pub(super) fn choice_statement(
    statement: &ExecStmtResult,
) -> Option<&ExecReleaseAxiomOfChoiceStmtSuccess> {
    match statement {
        ExecStmtResult::ReleaseAndExpand(
            crate::execute::ExecReleaseAndExpandStmtResult::AxiomOfChoice(
                ExecReleaseAxiomOfChoiceStmtResult::Success(p),
            ),
        ) => Some(p),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_choice(
        &self,
        result: &ExecReleaseAxiomOfChoiceStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseAxiomOfChoiceStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Choice/Failed"));
        };
        if p.statement.proof.len() != p.proof_steps.len() {
            return Err(LeanCompileError::unsupported("Choice/ProofSteps"));
        }
        for (statement, result) in p.statement.proof.iter().zip(&p.proof_steps) {
            crate::compile_to_lean::helper::validate_statement_capture(statement, result)?;
        }
        let VerifyObjWellDefinedResult::Success(wd) = &p.family_wd else {
            return Err(LeanCompileError::unsupported("Choice/FamilyWD"));
        };
        ensure_object(&p.statement.family, wd)?;
        let family = self.compile_wd(wd, position)?;
        let [sethood, nonempty] = p.obligations.as_slice() else {
            return Err(LeanCompileError::unsupported("Choice/Obligations"));
        };
        if !matches!(source_subject(&sethood.verified)?, Fact::AtomicFact(AtomicFact::IsSetFact(f))
            if f.set.ir() == p.statement.family.ir())
        {
            return Err(LeanCompileError::unsupported("Choice/SethoodSubject"));
        }
        let Fact::ForallFact(f) = source_subject(&nonempty.verified)? else {
            return Err(LeanCompileError::unsupported("Choice/NonemptySubject"));
        };
        let [group] = f.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Choice/NonemptyBinder"));
        };
        let [a] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Choice/NonemptyBinder"));
        };
        if !f.dom_facts.is_empty()
            || !matches!(&group.param_type, ParamType::Obj(s) if s.ir() == p.statement.family.ir())
            || !matches!(f.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::IsNonemptySetFact(n))]
                if n.set.ir() == Obj::Identifier(IdentifierObj::from_bound_name(a)).ir())
        {
            return Err(LeanCompileError::unsupported("Choice/NonemptySubject"));
        }
        let caller = SourcePosition {
            before: 1,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::Choice(p), 0);
        let mut steps = Vec::new();
        for (i, stmt) in p.proof_steps.iter().enumerate() {
            steps.push(self.compile_statement_in_scope(
                stmt,
                &SourcePosition { before: i, ..scope },
                i + 1,
                true,
            )?);
        }
        for (i, obligation) in p.obligations.iter().enumerate() {
            let (formation, store) = obligation
                .stored
                .as_ref()
                .map_err(|_| LeanCompileError::unsupported("Choice/ObligationStore"))?;
            let stage = p.proof_steps.len() + 3 * i;
            let before = SourcePosition {
                before: stage,
                ..scope
            };
            let source = source_subject(&obligation.verified)?;
            let compiled = self.compile_verify(&obligation.verified, &before)?;
            self.compile_fact_wd(
                formation,
                &source,
                &SourcePosition {
                    before: stage + 1,
                    ..scope
                },
            )?;
            self.validate_store(&store.store, &source)?;
            steps.push(self.emit_fact(&source, compiled.clone(), i, true, &before)?);
            steps.extend(self.compile_stored_inferences(
                store,
                &source,
                &(compiled.0, format!("h_{}", source.fact_id().value())),
                &SourcePosition {
                    before: stage + 3,
                    ..scope
                },
            )?);
        }
        let source = self.resolve_fact(p.stored.primary_fact_id(), position)?;
        let Fact::ExistFact(exist) = &source else {
            return Err(LeanCompileError::unsupported("Choice/Conclusion"));
        };
        let [group] = exist.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Choice/ConclusionBinder"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Choice/ConclusionBinder"));
        };
        let [QuantifierFreeFact::AtomicFact(AtomicFact::IsChoiceFunctionForFact(choice))] =
            exist.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Choice/ConclusionBody"));
        };
        let ParamType::Obj(Obj::FunctionSpace(FunctionSpace::FnSet(signature))) = &group.param_type
        else {
            return Err(LeanCompileError::unsupported("Choice/ConclusionFunction"));
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(identity)) = &choice.family else {
            return Err(LeanCompileError::unsupported("Choice/Identity"));
        };
        let valid_domain = |signature: &FnSet| {
            matches!(signature.set_bound_parameters.groups.as_slice(), [g]
            if g.params.len() == 1 && g.param_type.ir() == p.statement.family.ir())
                && signature.dom_facts.is_empty()
        };
        if !valid_domain(signature)
            || !valid_domain(&identity.body)
            || !matches!(signature.ret_set.as_ref(), Obj::SetOperator(SetOperator::FamilyUnion(u)) if u.left.ir() == p.statement.family.ir())
            || identity.body.ret_set.ir() != p.statement.family.ir()
            || identity.equal_to.ir()
                != Obj::Identifier(IdentifierObj::from_bound_name(
                    &identity.body.set_bound_parameters.groups[0].params[0],
                ))
                .ir()
            || choice.index.ir() != p.statement.family.ir()
            || choice.set.ir() != p.statement.family.ir()
            || choice.choice.ir() != Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir()
        {
            return Err(LeanCompileError::unsupported("Choice/ConclusionSubject"));
        }
        let outer = SourcePosition {
            before: 2,
            ..*position
        };
        let proposition = self.compile_formed_fact_proposition(&p.stored_wd, &source, &outer)?;
        let FactWellDefinedProof::ExistFact(formation) = &p.stored_wd else {
            return Err(LeanCompileError::unsupported("Choice/ConclusionFormation"));
        };
        let body = formation
            .detailed_ref()
            .assumed_body_facts
            .first()
            .ok_or_else(|| LeanCompileError::unsupported("Choice/ConclusionFormation"))?;
        let existential =
            SourcePosition::new(Some(&outer), SourceOwner::ExistWD(exist, formation), 1);
        let formed = SourcePosition::new(
            Some(&existential),
            SourceOwner::FactWD(&body.well_defined),
            usize::MAX,
        );
        // This validated identity only mentions the outer family, never f or
        // the hypothetical choice-function predicate introduced during formation.
        let identity = self.compile_object_reference(&choice.family, &formed)?;
        steps.push(format!("exact Litex.choiceForIdentity {family} {identity} (by\n  intro x hx\n  exact Litex.formulaIdentityCall _ (fun _ => rfl) x ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)) (fun a ha => h_{} (Litex.objectAtLevel (Litex.denote a) (Litex.isSet a)) ha)", f.fact_id.value()));
        let term = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));
        self.emit_by_completed_fact(
            &source,
            (proposition, term),
            &p.stored,
            position,
            4,
            index,
            local,
        )
    }
}
