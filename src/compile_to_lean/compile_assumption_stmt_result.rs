use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_unsafe_stmt::{ExecTrustBoundaryStmtResult, ExecTrustStmtResult};
use crate::prelude::*;

/// Borrow the original assumption stages. WD precedes every truth store.
pub(super) fn assumption_stages(
    statement: &ExecStmtResult,
) -> Vec<(Fact, &FactWellDefinedProof, &StoreFactAndInferResult)> {
    match statement {
        ExecStmtResult::Trust(ExecTrustBoundaryStmtResult::TrustStmt(
            ExecTrustStmtResult::Success(p),
        )) => p
            .statement
            .facts
            .iter()
            .cloned()
            .zip(&p.facts_well_defined)
            .zip(&p.store_and_infer_results)
            .map(|((f, wd), store)| (f, wd, store))
            .collect(),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(
            crate::execute::ExecAxiomStmtResult::Success(p),
        )) => match &p.goal_wd {
            VerifyFactWellDefinedResult::Success(wd) => vec![(
                Fact::ForallFact(p.statement.forall_fact.clone()),
                wd,
                &p.stored,
            )],
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_assumption_statement(
        &self,
        statement: &ExecStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        // A local trust cannot be moved outside its binders or silently proved.
        if local {
            return Err(LeanCompileError::unsupported("Assumption/LocalClosure"));
        }
        let stages = assumption_stages(statement);
        let expected = match statement {
            ExecStmtResult::Trust(ExecTrustBoundaryStmtResult::TrustStmt(
                ExecTrustStmtResult::Success(p),
            )) if p.statement.facts.len() == p.facts_well_defined.len()
                && p.statement.facts.len() == p.store_and_infer_results.len() =>
            {
                p.statement.facts.len()
            }
            ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(
                crate::execute::ExecAxiomStmtResult::Success(_),
            )) => 1,
            _ => return Err(LeanCompileError::unsupported("Assumption/Stages")),
        };
        if stages.len() != expected || stages.is_empty() {
            return Err(LeanCompileError::unsupported("Assumption/Stages"));
        }
        let mut declarations = Vec::new();
        // Form all statements before publishing any assumed truth.
        let mut propositions = Vec::new();
        for (index, (fact, wd, store)) in stages.iter().enumerate() {
            self.validate_store(&store.store, fact)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            propositions.push(self.compile_assumption_proposition(wd, fact, &prior)?);
        }
        for (index, ((fact, _, store), proposition)) in stages.iter().zip(propositions).enumerate()
        {
            let name = format!("h_{}", fact.fact_id().value());
            declarations.push(format!("variable ({name} : {proposition})"));
            let published = SourcePosition {
                before: stages.len() + index + 1,
                ..*position
            };
            declarations.extend(self.compile_stored_inferences(
                store,
                fact,
                &(proposition, name),
                &published,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    fn compile_assumption_proposition(
        &self,
        wd: &FactWellDefinedProof,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (fact, wd) {
            (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) => {
                self.compile_canonical_forall_formation(fact, wd, position)
            }
            (Fact::ForallFactWithIff(_), _) => {
                Err(LeanCompileError::unsupported("Assumption/QuantifiedIff"))
            }
            _ => self.compile_formed_fact_proposition(wd, fact, position),
        }
    }

    pub(super) fn assumption_binders(
        &self,
        statement: &ExecStmtResult,
        before: usize,
        parent: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let stages = assumption_stages(statement);
        let count = before.saturating_sub(stages.len()).min(stages.len());
        stages
            .iter()
            .take(count)
            .enumerate()
            .map(|(index, (fact, wd, _))| {
                let site =
                    SourcePosition::new(Some(parent), SourceOwner::Statement(statement), index);
                let proposition = self.compile_assumption_proposition(wd, fact, &site)?;
                Ok(format!("(h_{} : {proposition})", fact.fact_id().value()))
            })
            .collect()
    }
}
