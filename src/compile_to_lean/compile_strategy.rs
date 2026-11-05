//! Declared strategies retain a separate proved interface from ordinary facts.
use super::compile_known_application::ProvedApplicationRef;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{ExecDefStrategyStmtResult, ExecDefStrategyStmtSuccess};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_known_strategy(
        &self,
        goal: &AtomicFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::SearchProofByKnownStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let proof = proof
            .as_detailed()
            .map_err(|_| LeanCompileError::unsupported("Strategy/Detail"))?;
        let (declaration, prior) = position.visible_strategy(&proof.strategy_name)?;
        let source = &declaration.statement.forall_fact;
        if !matches!(source.then_facts.get(proof.then_index),
            Some(ExistOrAndChainAtomicFact::AtomicFact(fact)) if !matches!(fact, AtomicFact::EqualFact(_)))
            || matches!(goal, AtomicFact::EqualFact(_))
        {
            return Err(LeanCompileError::unsupported("Strategy/SelectedClause"));
        }
        let name = format!("strategy_{}", source.fact_id.value());
        let reference = if matches!(prior.owner, SourceOwner::Run(_)) {
            self.context_application(&name, &prior)
        } else {
            name
        };
        self.compile_proved_forall_application(
            &Fact::AtomicFact(goal.clone()),
            source,
            reference,
            &ForallConclusionLocation::DirectThenFact(DirectForallConclusionLocation {
                then_fact_index: proof.then_index,
            }),
            super::compile_known_application::ForallApplicationInput {
                arguments: &proof.forall_parameters_match_what_args,
                matches: &proof.arg_match_proofs,
                requirements: &proof.instantiation_requirements,
            },
            SourceOwner::StrategyApplication(proof),
            SourceOwner::CalleeInstance(ProvedApplicationRef::Strategy(proof)),
            position,
        )
        .map(|compiled| compiled.1)
    }

    pub(super) fn compile_strategy_statement(
        &self,
        result: &ExecDefStrategyStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecDefStrategyStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Strategy/Failed"));
        };
        let compiled = self.compile_strategy_body(proof, position)?;
        Ok(format!(
            "{} strategy_{}{} : {} :=\n  {}",
            if local { "have" } else { "theorem" },
            proof.statement.forall_fact.fact_id.value(),
            if local {
                String::new()
            } else {
                self.context_header(position)?
            },
            compiled.0,
            self.share_local_proof(&compiled.1, local)
                .replace('\n', "\n  ")
        ))
    }

    fn compile_strategy_body(
        &self,
        proof: &ExecDefStrategyStmtSuccess,
        original: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let fact = &proof.statement.forall_fact;
        let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
            &proof.goal_wd
        else {
            return Err(LeanCompileError::unsupported("Strategy/GoalWD"));
        };
        let (proposition, introductions, mut definitions) =
            self.compile_forall_goal_capture(fact, goal, original)?;
        let scope = SourcePosition::new(Some(original), SourceOwner::Strategy(proof), 0);
        let (_, _, body_definitions) = self.compile_forall_head(
            fact,
            &proof.body.introduced_params,
            &proof.body.assumed_dom_facts,
            &scope,
        )?;
        if proof.body.proof_steps.len() != proof.statement.prove_process.len()
            || proof.body.conclusion_proofs.len() != fact.then_facts.len()
            || fact.then_facts.is_empty()
        {
            return Err(LeanCompileError::unsupported("Strategy/Stages"));
        }
        definitions.extend(self.compile_forall_header_aliases(
            fact,
            goal,
            &proof.body.introduced_params,
            &proof.body.assumed_dom_facts,
            original,
            &scope,
        )?);
        definitions.extend(body_definitions);
        let head = fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len();
        for (index, (source, result)) in proof
            .statement
            .prove_process
            .iter()
            .zip(&proof.body.proof_steps)
            .enumerate()
        {
            validate_statement_capture(source, result)?;
            definitions.push(self.compile_statement_in_scope(
                result,
                &SourcePosition {
                    before: head + index,
                    ..scope
                },
                index + 1,
                true,
            )?);
        }
        let mut conclusions = Vec::new();
        for (source, result) in fact.then_facts.iter().zip(&proof.body.conclusion_proofs) {
            let expected: Fact = source.clone().into();
            if source_subject(result)? != expected {
                return Err(LeanCompileError::unsupported("Strategy/ConclusionSubject"));
            }
            conclusions.push(
                self.compile_verify(
                    result,
                    &SourcePosition {
                        before: head + proof.body.proof_steps.len(),
                        ..scope
                    },
                )?
                .1,
            );
        }
        let mut conclusion = conclusions.pop().expect("nonempty strategy conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion = format!("(And.intro {left} {conclusion})");
        }
        let mut lines = Vec::new();
        if !introductions.is_empty() {
            lines.push(format!("intro {}", introductions.join(" ")));
        }
        lines.extend(definitions);
        lines.push(format!("exact {conclusion}"));
        Ok((
            proposition,
            format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
        ))
    }
}
