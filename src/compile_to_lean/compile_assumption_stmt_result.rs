use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_unsafe_stmt::{ExecTrustBoundaryStmtResult, ExecTrustStmtResult};
use crate::execute::{ExecTrustHaveStmtResult, ExecTrustHaveStmtSuccessResult};
use crate::prelude::*;

pub(super) fn trust_have(statement: &ExecStmtResult) -> Option<&ExecTrustHaveStmtSuccessResult> {
    match statement {
        ExecStmtResult::Trust(ExecTrustBoundaryStmtResult::TrustHaveStmt(
            ExecTrustHaveStmtResult::Success(p),
        )) => Some(p),
        _ => None,
    }
}

/// Parameter stores and automatic structure opening precede body formation.
pub(super) fn assumption_start(statement: &ExecStmtResult) -> usize {
    trust_have(statement).map_or(0, |p| {
        p.statement
            .param_def
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>()
            + 1
    })
}

fn stored_subject(store: &StoreFactResult) -> Fact {
    match store {
        StoreFactResult::AtomicFact(p) => Fact::AtomicFact(p.fact.clone()),
        StoreFactResult::AndFact(p) => Fact::AndFact(p.fact.clone()),
        StoreFactResult::ChainFact(p) => Fact::ChainFact(p.fact.clone()),
        StoreFactResult::OrFact(p) => Fact::OrFact(p.fact.clone()),
        StoreFactResult::ExistShapedFact(p) => crate::ast::fact::exist_shaped_fact_to_fact(&p.fact),
        StoreFactResult::NotForallFact(p) => Fact::NotForall(p.fact.clone()),
        StoreFactResult::ForallFact(p) => Fact::ForallFact(p.fact.clone()),
        StoreFactResult::ForallFactWithIff(p) => Fact::ForallFactWithIff(p.fact.clone()),
    }
}

/// Borrow the original assumption stages. WD precedes every truth store.
pub(super) fn assumption_stages(
    statement: &ExecStmtResult,
) -> Vec<(Fact, &FactWellDefinedProof, &StoreFactAndInferResult)> {
    if let Some(p) = trust_have(statement) {
        return p
            .body_facts_well_defined
            .iter()
            .zip(&p.body_store_and_infer_results)
            .map(|(wd, store)| (stored_subject(&store.store), wd, store))
            .collect();
    }
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
        if local && trust_have(statement).is_some() {
            return Err(LeanCompileError::unsupported(
                "Assumption/LocalWitnessClosure",
            ));
        }
        let stages = assumption_stages(statement);
        if local
            && stages.iter().any(|(fact, _, _)| {
                matches!(fact, Fact::ForallFact(_) | Fact::ForallFactWithIff(_))
            })
        {
            return Err(LeanCompileError::unsupported("Assumption/LocalQuantified"));
        }
        let start = assumption_start(statement);
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
            _ if trust_have(statement).is_some_and(|p| {
                p.statement.facts.len() == p.body_facts_well_defined.len()
                    && p.statement.facts.len() == p.body_store_and_infer_results.len()
            }) =>
            {
                stages.len()
            }
            _ => return Err(LeanCompileError::unsupported("Assumption/Stages")),
        };
        if stages.len() != expected || (stages.is_empty() && trust_have(statement).is_none()) {
            return Err(LeanCompileError::unsupported("Assumption/Stages"));
        }
        let mut declarations = Vec::new();
        if let Some(p) = trust_have(statement) {
            declarations.extend(self.compile_trust_have_parameters(p, position)?);
            for (source, (actual, _, _)) in p.statement.facts.iter().zip(&stages) {
                if source.ir() != actual.ir() {
                    return Err(LeanCompileError::unsupported("TrustHave/BodySubject"));
                }
            }
        }
        // Form all statements before publishing any assumed truth.
        let mut propositions = Vec::new();
        for (index, (fact, wd, store)) in stages.iter().enumerate() {
            self.validate_store(&store.store, fact)?;
            let prior = SourcePosition {
                before: start + index,
                ..*position
            };
            propositions.push(self.compile_assumption_proposition(wd, fact, &prior)?);
        }
        for (index, ((fact, _, store), proposition)) in stages.iter().zip(propositions).enumerate()
        {
            let name = format!("h_{}", fact.fact_id().value());
            declarations.push(if local {
                format!(
                    "have {name} : {proposition} := {}",
                    self.local_assumption_reference(fact.fact_id(), position)?
                )
            } else {
                format!("variable ({name} : {proposition})")
            });
            let published = SourcePosition {
                before: start + stages.len() + index + 1,
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

    pub(super) fn compile_assumption_proposition(
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
        let start = assumption_start(statement);
        let count = before
            .saturating_sub(start + stages.len())
            .min(stages.len());
        stages
            .iter()
            .take(count)
            .enumerate()
            .map(|(index, (fact, wd, _))| {
                let site = SourcePosition::new(
                    Some(parent),
                    SourceOwner::Statement(statement),
                    start + index,
                );
                let proposition = self.compile_assumption_proposition(wd, fact, &site)?;
                Ok(format!("(h_{} : {proposition})", fact.fact_id().value()))
            })
            .collect()
    }

    fn compile_trust_have_parameters(
        &self,
        proof: &ExecTrustHaveStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let groups = &proof.statement.param_def.groups;
        let stores = &proof.defined_param_store_and_infer.store_and_infer_results;
        self.validate_parameter_store_capture(&proof.defined_param_store_and_infer)?;
        if groups.len() != proof.param_type_well_defined.len()
            || groups.iter().map(|g| g.params.len()).sum::<usize>() != stores.len()
        {
            return Err(LeanCompileError::unsupported("TrustHave/ParameterStages"));
        }
        let mut declarations = Vec::new();
        let mut offset = 0;
        for (group, wd) in groups.iter().zip(&proof.param_type_well_defined) {
            let prior = SourcePosition {
                before: offset,
                ..*position
            };
            match (&group.param_type, wd) {
                (ParamType::Obj(set), ParamTypeWellDefinedProof::Obj(wd)) => {
                    super::helper::ensure_object(set, wd)?;
                    self.compile_wd(wd, &prior)?;
                }
                (ParamType::Set(_), ParamTypeWellDefinedProof::Set) => {}
                _ => return Err(LeanCompileError::unsupported("TrustHave/ParameterKind")),
            }
            for parameter in &group.params {
                let introduced = SourcePosition {
                    before: offset + 1,
                    ..*position
                };
                let formed =
                    SourcePosition::new(Some(&introduced), SourceOwner::ParamTypeWD(wd), 1);
                let (binders, _) = match &group.param_type {
                    ParamType::Obj(set) => {
                        self.introduce_member_parameter(parameter, set, &stores[offset], &formed)?
                    }
                    kind => self.introduce_set_kind_parameter(
                        parameter,
                        kind,
                        &stores[offset],
                        &formed,
                    )?,
                };
                declarations.push(format!("variable {}", binders.join(" ")));
                let fact = self.resolve_fact(stores[offset].primary_fact_id(), &introduced)?;
                let member = (
                    self.fact_proposition(&fact, &formed)?,
                    format!("h_{}", fact.fact_id().value()),
                );
                declarations.extend(self.compile_parameter_inferences(
                    &stores[offset],
                    &fact,
                    &member,
                    &formed,
                )?);
                offset += 1;
            }
        }
        let complete = SourcePosition {
            before: offset,
            ..*position
        };
        declarations.extend(self.compile_auto_struct_layers(
            groups,
            stores,
            proof.auto_opened_struct_layers.as_deref(),
            &complete,
        )?);
        Ok(declarations)
    }
}
