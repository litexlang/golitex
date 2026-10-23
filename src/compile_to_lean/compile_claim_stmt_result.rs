use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecClaimStmtSuccess,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_claim_statement(
        &self,
        result: &ExecClaimStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecClaimStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::new(
                "Claim/Failed",
                "A failed claim is not proof evidence.",
            ));
        };
        let VerifyFactWellDefinedResult::Success(goal_wd) = &proof.goal_wd else {
            return Err(LeanCompileError::new(
                "Claim/GoalWD",
                "A successful claim has failed goal-formation evidence.",
            ));
        };
        self.compile_fact_wd(goal_wd, &proof.statement.fact, position)?;
        let scope = SourcePosition::new(Some(position), SourceOwner::Claim(proof), 0);
        let compiled = self.compile_claim_body(proof, &scope)?;
        self.compile_completed_fact_statement(
            &proof.statement.fact,
            compiled,
            &proof.stored,
            position,
            index,
            local,
        )
    }

    pub(in crate::compile_to_lean) fn compile_claim_body(
        &self,
        proof: &ExecClaimStmtSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (_binders, _introductions, definitions, steps, results, expected) =
            match (&proof.statement.fact, &proof.body) {
                (Fact::ForallFact(fact), ExecClaimBodyProof::Forall(body)) => {
                    let (binders, introductions, definitions) = self.compile_forall_head(
                        fact,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        position,
                    )?;
                    let expected = fact
                        .then_facts
                        .iter()
                        .map(claim_goal_component)
                        .collect::<Result<Vec<_>, _>>()?;
                    (
                        binders,
                        introductions,
                        definitions,
                        &body.proof_steps,
                        body.conclusion_proofs.iter().collect::<Vec<_>>(),
                        expected,
                    )
                }
                (
                    Fact::AtomicFact(_) | Fact::AndFact(_) | Fact::ChainFact(_) | Fact::OrFact(_),
                    ExecClaimBodyProof::NonForall(body),
                ) => (
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    &body.proof_steps,
                    vec![&body.conclusion_proof],
                    vec![proof.statement.fact.clone()],
                ),
                _ => return Err(LeanCompileError::unsupported("Claim/GoalBodyShape")),
            };
        if steps.len() != proof.statement.proof.len()
            || results.len() != expected.len()
            || results.is_empty()
        {
            return Err(LeanCompileError::new(
                "Claim/Stages",
                "The claim body has different source steps or conclusion arity.",
            ));
        }
        let head_count = match &proof.statement.fact {
            Fact::ForallFact(f) => {
                f.typed_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
                    + f.dom_facts.len()
            }
            _ => 0,
        };
        let original_scope = position.parent.ok_or_else(|| {
            LeanCompileError::new(
                "Claim/GoalScope",
                "The claim proof has no original declaration scope.",
            )
        })?;
        let (proposition, introductions, mut body_text) =
            self.compile_claim_goal(proof, original_scope)?;
        body_text.extend(self.compile_claim_header_aliases(proof, original_scope, position)?);
        body_text.extend(definitions);
        for (index, (source, step)) in proof.statement.proof.iter().zip(steps).enumerate() {
            validate_statement_capture(source, step)?;
            body_text.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: head_count + index,
                    ..*position
                },
                index + 1,
                true,
            )?);
        }
        let mut conclusions = Vec::new();
        for (expected, result) in expected.iter().zip(results) {
            let compiled = self.compile_verify(
                result,
                &SourcePosition {
                    before: head_count + steps.len(),
                    ..*position
                },
            )?;
            if &source_subject(result)? != expected {
                return Err(LeanCompileError::new(
                    "Claim/Conclusion",
                    "The proof has another source conclusion.",
                ));
            }
            conclusions.push(compiled);
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.0 = format!("(({}) ∧ ({}))", left.0, conclusion.0);
            conclusion.1 = format!("(And.intro {} {})", left.1, conclusion.1);
        }
        let mut statements = Vec::new();
        if !introductions.is_empty() {
            statements.push(format!("intro {}", introductions.join(" ")));
        }
        statements.extend(body_text);
        statements.push(format!("exact {}", conclusion.1));
        Ok((
            proposition,
            format!("(by\n  {}\n)", statements.join("\n").replace('\n', "\n  ")),
        ))
    }

    // Public meaning is formed from the original goal before body-local choices.
    // Only that goal header's actual producers may close constructor WD here.
    fn compile_claim_goal(
        &self,
        proof: &ExecClaimStmtSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Vec<String>, Vec<String>), LeanCompileError> {
        let VerifyFactWellDefinedResult::Success(goal_wd) = &proof.goal_wd else {
            return Err(LeanCompileError::unsupported("Claim/GoalWD"));
        };
        match (&proof.statement.fact, goal_wd) {
            (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) => {
                let header =
                    SourcePosition::new(Some(position), SourceOwner::ForallWD(fact, wd), 0);
                let (binders, introductions, definitions) = self.compile_forall_head(
                    fact,
                    &wd.introduced_params,
                    &wd.assumed_dom_facts,
                    &header,
                )?;
                if wd.then.len() != fact.then_facts.len() {
                    return Err(LeanCompileError::new(
                        "Claim/GoalThenWD",
                        "The original goal has a different ordered WD arity.",
                    ));
                }
                let complete = SourcePosition {
                    before: fact
                        .typed_parameters
                        .groups
                        .iter()
                        .map(|group| group.params.len())
                        .sum::<usize>()
                        + fact.dom_facts.len(),
                    ..header
                };
                let mut propositions = Vec::new();
                for (source, formation) in fact.then_facts.iter().zip(&wd.then) {
                    let source = claim_goal_component(source)?;
                    self.compile_fact_wd(formation, &source, &complete)?;
                    let formed = SourcePosition::new(
                        Some(&complete),
                        SourceOwner::FactWD(formation),
                        usize::MAX,
                    );
                    propositions.push(self.fact_proposition(&source, &formed)?);
                }
                let meaning =
                    self.scope_proposition(conjunction_proposition(propositions)?, &definitions);
                Ok((
                    format!("∀ {}, {meaning}", binders.join(" ")),
                    introductions,
                    definitions,
                ))
            }
            (Fact::AtomicFact(_) | Fact::AndFact(_) | Fact::ChainFact(_) | Fact::OrFact(_), _) => {
                let formed =
                    SourcePosition::new(Some(position), SourceOwner::FactWD(goal_wd), usize::MAX);
                Ok((
                    self.fact_proposition(&proof.statement.fact, &formed)?,
                    Vec::new(),
                    Vec::new(),
                ))
            }
            _ => Err(LeanCompileError::unsupported("Claim/GoalBodyShape")),
        }
    }

    // The goal WD scope and the truth body introduced the same source parameters
    // in separate executions. Bind their actual body FactIds to the corresponding
    // original hypotheses, preserving both captures without adding premises.
    fn compile_claim_header_aliases(
        &self,
        proof: &ExecClaimStmtSuccess,
        original: &SourcePosition<'_>,
        body_position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            Fact::ForallFact(fact),
            VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)),
            ExecClaimBodyProof::Forall(body),
        ) = (&proof.statement.fact, &proof.goal_wd, &proof.body)
        else {
            return Ok(Vec::new());
        };
        let goal_stores = &goal
            .introduced_params
            .defined_params
            .store_and_infer_results;
        let body_stores = &body
            .introduced_params
            .defined_params
            .store_and_infer_results;
        if goal_stores.len() != body_stores.len()
            || goal.assumed_dom_facts.len() != body.assumed_dom_facts.len()
        {
            return Err(LeanCompileError::new(
                "Claim/HeaderArity",
                "The original goal and body have different header captures.",
            ));
        }
        let goal_header = SourcePosition::new(Some(original), SourceOwner::ForallWD(fact, goal), 0);
        let mut aliases = Vec::new();
        for (index, (goal_store, body_store)) in goal_stores.iter().zip(body_stores).enumerate() {
            let goal_position = SourcePosition {
                before: index + 1,
                ..goal_header
            };
            let body_position = SourcePosition {
                before: index + 1,
                ..*body_position
            };
            aliases.extend(self.compile_claim_header_alias(
                goal_store,
                body_store,
                &goal_position,
                &body_position,
            )?);
        }
        for (index, (goal_dom, body_dom)) in goal
            .assumed_dom_facts
            .iter()
            .zip(&body.assumed_dom_facts)
            .enumerate()
        {
            let before = goal_stores.len() + index + 1;
            let goal_position = SourcePosition {
                before,
                ..goal_header
            };
            let body_position = SourcePosition {
                before,
                ..*body_position
            };
            aliases.extend(self.compile_claim_header_alias(
                &goal_dom.store_and_infer,
                &body_dom.store_and_infer,
                &goal_position,
                &body_position,
            )?);
        }
        Ok(aliases)
    }

    fn compile_claim_header_alias(
        &self,
        goal: &StoreFactAndInferResult,
        body: &StoreFactAndInferResult,
        goal_position: &SourcePosition<'_>,
        body_position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        // Iff sugar stores only its two directions. Its source assumption is
        // already captured here and is not a separate Runtime fact.
        if let (
            StoreFactResult::ForallFactWithIff(goal_iff),
            StoreFactResult::ForallFactWithIff(body_iff),
        ) = (&goal.store, &body.store)
        {
            let source = Fact::ForallFactWithIff(goal_iff.fact.clone());
            self.validate_store(&goal.store, &source)?;
            self.validate_store(&body.store, &source)?;
            if goal_iff.fact != body_iff.fact {
                return Err(LeanCompileError::unsupported("ForallIff/HeaderSubject"));
            }
            // Each header replays its own direction stores from this same
            // hypothesis; their fresh projection IDs are not extra premises.
            return Ok(Vec::new());
        }
        let goal_fact = self.resolve_fact(goal.primary_fact_id(), goal_position)?;
        let body_fact = self.resolve_fact(body.primary_fact_id(), body_position)?;
        self.validate_store(&goal.store, &goal_fact)?;
        self.validate_store(&body.store, &body_fact)?;
        if !instantiated_fact_matches(&goal_fact, &body_fact, &std::collections::HashMap::new()) {
            return Err(LeanCompileError::new(
                "Claim/HeaderSubject",
                "The original goal and body introduced different source assumptions.",
            ));
        }
        if goal.primary_fact_id() == body.primary_fact_id() {
            return Ok(Vec::new());
        }
        let compiled = (
            self.fact_proposition(&body_fact, body_position)?,
            format!("h_{}", goal.primary_fact_id().value()),
        );
        Ok(vec![self.emit_internal_fact(
            &body_fact,
            &compiled,
            body_position,
        )?])
    }
}

fn claim_goal_component(fact: &ExistOrAndChainAtomicFact) -> Result<Fact, LeanCompileError> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(fact) => Ok(Fact::AtomicFact(fact.clone())),
        ExistOrAndChainAtomicFact::AndFact(fact) => Ok(Fact::AndFact(fact.clone())),
        ExistOrAndChainAtomicFact::ChainFact(fact) => Ok(Fact::ChainFact(fact.clone())),
        ExistOrAndChainAtomicFact::OrFact(fact) => Ok(Fact::OrFact(fact.clone())),
        ExistOrAndChainAtomicFact::ExistFact(_)
        | ExistOrAndChainAtomicFact::ExistUniqueFact(_)
        | ExistOrAndChainAtomicFact::NotExistFact(_) => {
            Err(LeanCompileError::unsupported("Claim/CompoundThen"))
        }
    }
}
