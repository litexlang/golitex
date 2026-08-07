use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub(crate) fn build_stmt_to_lean_ir(
        &self,
        result: &StmtResult,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        if let Some(success) = result.factual_success() {
            let fact = self.fact_to_lean_ir_from_success(success)?;
            let excluded = HashSet::from([success.stmt.to_string()]);
            return Ok(StmtToLeanIR::Fact(FactStmtToLeanIR {
                fact,
                inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &excluded)?,
            }));
        }

        let Some(success) = result.non_factual_success() else {
            return Err(to_lean_ir_error(
                &result.line_file(),
                "To-Lean IR requires a successful statement result",
            ));
        };
        match &success.stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(stmt)) => {
                Ok(StmtToLeanIR::AbstractProp(AbstractPropToLeanIR {
                    name: stmt.name.clone(),
                    params: stmt.params.clone(),
                }))
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(stmt)) => {
                Ok(StmtToLeanIR::Prop(PropToLeanIR {
                    name: stmt.name.clone(),
                    params: stmt
                        .params_def_with_type
                        .groups
                        .iter()
                        .map(param_group_to_lean_ir)
                        .collect(),
                    iff_facts: stmt.iff_facts.clone(),
                }))
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(stmt)) => {
                let excluded = stmt
                    .facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<HashSet<_>>();
                let mut facts = Vec::with_capacity(stmt.facts.len());
                for fact in stmt.facts.iter() {
                    facts.push(FactToLeanIR {
                        fact_id: self.known_fact_id_for_fact(fact)?,
                        proposition: fact.clone(),
                        proof: FactProofToLeanIR::Trusted,
                    });
                }
                Ok(StmtToLeanIR::Trust(TrustToLeanIR {
                    facts,
                    inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &excluded)?,
                }))
            }
            other => Err(to_lean_ir_error(
                &other.line_file(),
                format!(
                    "To-Lean IR MVP does not support statement kind `{}`",
                    other.stmt_type_name()
                ),
            )),
        }
    }

    fn fact_to_lean_ir_from_success(
        &self,
        success: &FactualStmtSuccess,
    ) -> Result<FactToLeanIR, RuntimeError> {
        Ok(FactToLeanIR {
            fact_id: success.fact_id,
            proposition: success.stmt.clone(),
            proof: self.verified_by_to_lean_ir(
                &success.stmt,
                success.fact_id,
                &success.verified_by,
            )?,
        })
    }

    fn fact_to_lean_ir_from_result(
        &self,
        result: &StmtResult,
        context: &str,
    ) -> Result<FactToLeanIR, RuntimeError> {
        let Some(success) = result.factual_success() else {
            return Ok(FactToLeanIR {
                fact_id: None,
                proposition: result
                    .as_fact_unknown()
                    .map(|unknown| unknown.goal().clone())
                    .unwrap_or_else(|| {
                        NormalAtomicFact::new(
                            AtomicName::WithoutMod("to_lean_unknown_subgoal".to_string()),
                            vec![],
                            result.line_file(),
                        )
                        .into()
                    }),
                proof: FactProofToLeanIR::Unsupported {
                    reason: format!("{} did not return a factual success", context),
                },
            });
        };
        self.fact_to_lean_ir_from_success(success)
    }

    fn verified_by_to_lean_ir(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        verified_by: &VerifiedByResult,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => Ok(FactProofToLeanIR::Builtin {
                kind: BuiltinProofKindToLeanIR::Rule,
                rule: BuiltinRuleToLeanIR::from_verified_label(&result.msg, goal),
                subgoals: self.subgoals_to_lean_ir(&result.subgoals)?,
            }),
            VerifiedByResult::BuiltinStrategy(result) => Ok(FactProofToLeanIR::Builtin {
                kind: BuiltinProofKindToLeanIR::Strategy,
                rule: BuiltinRuleToLeanIR::from_verified_label(&result.msg, goal),
                subgoals: self.subgoals_to_lean_ir(&result.subgoals)?,
            }),
            VerifiedByResult::Fact(result) => match result.cite_what.as_ref() {
                Stmt::Fact(source_fact) => {
                    let source_fact_id = match result.source_fact_id {
                        Some(fact_id) => Some(fact_id),
                        None => self.citation_fact_id(source_fact, goal, goal_fact_id)?,
                    };
                    match source_fact_id {
                        Some(source_fact_id) => Ok(FactProofToLeanIR::KnownFact { source_fact_id }),
                        None => Ok(FactProofToLeanIR::Unsupported {
                            reason: format!(
                                "verified citation `{}` has no stored FactId",
                                source_fact
                            ),
                        }),
                    }
                }
                Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                    Ok(FactProofToLeanIR::Definition {
                        name: definition.name.clone(),
                    })
                }
                Stmt::DefStrategyStmt(strategy) => Ok(FactProofToLeanIR::UserStrategy {
                    name: strategy.name.clone(),
                }),
                cited => Ok(FactProofToLeanIR::Unsupported {
                    reason: format!(
                        "citation kind `{}` is not represented by the To-Lean MVP",
                        cited.stmt_type_name()
                    ),
                }),
            },
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.known_forall_to_lean_ir(result)
            }
            VerifiedByResult::VerifiedBys(result) => {
                let mut steps = Vec::with_capacity(result.cite_what.len());
                for step in result.cite_what.iter() {
                    steps.push(self.verified_bys_step_to_lean_ir(step, goal, goal_fact_id)?);
                }
                Ok(FactProofToLeanIR::Composite { steps })
            }
            VerifiedByResult::ForallProof(result) => {
                let parameter_reason = InferReason::ParameterDefinition.store_reason();
                let parameter_assumptions = result
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| output.itself_and_why_itself_is_stored.1 == parameter_reason)
                    .map(|output| FactToLeanIR {
                        fact_id: output.fact_id,
                        proposition: output.itself_and_why_itself_is_stored.0.clone(),
                        proof: FactProofToLeanIR::Assumption,
                    })
                    .collect();
                let mut assumptions = Vec::with_capacity(result.forall_fact.dom_facts.len());
                for dom_fact in result.forall_fact.dom_facts.iter() {
                    let proposition = dom_fact.clone();
                    let fact_id = result
                        .assumption_infers
                        .store_fact_outputs
                        .iter()
                        .find(|output| {
                            output.itself_and_why_itself_is_stored.0.to_string()
                                == proposition.to_string()
                        })
                        .and_then(|output| output.fact_id);
                    assumptions.push(FactToLeanIR {
                        fact_id,
                        proposition,
                        proof: FactProofToLeanIR::Assumption,
                    });
                }
                let mut conclusions = Vec::with_capacity(result.proves.len());
                for proved in result.proves.iter() {
                    conclusions.push(self.fact_to_lean_ir_from_result(
                        proved.result.as_ref(),
                        "forall conclusion",
                    )?);
                }
                Ok(FactProofToLeanIR::ForallIntroduction {
                    parameter_assumptions,
                    assumptions,
                    conclusions,
                })
            }
            VerifiedByResult::StatementMemo(source) => Ok(FactProofToLeanIR::Memo {
                proof: Box::new(self.verified_by_to_lean_ir(
                    goal,
                    source.fact_id.or(goal_fact_id),
                    &source.verified_by,
                )?),
            }),
        }
    }

    fn citation_fact_id(
        &self,
        cited_fact: &Fact,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
    ) -> Result<Option<FactId>, RuntimeError> {
        if let Some(fact_id) = self.known_fact_id_for_fact(cited_fact)? {
            return Ok(Some(fact_id));
        }
        // A forall conclusion can cite one of its temporary assumptions. The
        // local environment has already been popped when statement IR is
        // assembled, but verification stored the identical conclusion under
        // the assumption's ID and retained that ID on the result.
        if cited_fact.to_string() == goal.to_string() {
            return Ok(goal_fact_id);
        }
        Ok(None)
    }

    fn known_forall_to_lean_ir(
        &self,
        result: &KnownForallInstantiationResult,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let Stmt::Fact(source_fact) = result.cite_what.as_ref() else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: "known-forall verification did not cite a fact".to_string(),
            });
        };
        let source_fact_id = match result.source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.known_fact_id_for_fact(source_fact)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("known forall `{}` has no stored FactId", source_fact),
            });
        };
        let arguments = result
            .instantiation
            .iter()
            .map(|item| KnownForallArgumentToLeanIR {
                param: item.param.clone(),
                argument: item.arg_obj.clone(),
            })
            .collect();
        let mut parameter_requirements = Vec::new();
        let mut requirements = Vec::new();
        for requirement in result.requirements.iter() {
            let requirement_ir = self.fact_to_lean_ir_from_result(
                requirement.result.as_ref(),
                "known-forall requirement",
            )?;
            match requirement.kind {
                KnownForallRequirementKind::ParameterType => {
                    parameter_requirements.push(requirement_ir)
                }
                KnownForallRequirementKind::Domain => requirements.push(requirement_ir),
            }
        }
        Ok(FactProofToLeanIR::KnownForall {
            source_fact_id,
            arguments,
            parameter_requirements,
            requirements,
        })
    }

    fn subgoals_to_lean_ir(
        &self,
        subgoals: &[StmtResult],
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        subgoals
            .iter()
            .map(|result| self.fact_to_lean_ir_from_result(result, "builtin subgoal"))
            .collect()
    }

    fn verified_bys_step_to_lean_ir(
        &self,
        step: &VerifiedBysEnum,
        enclosing_goal: &Fact,
        enclosing_goal_fact_id: Option<FactId>,
    ) -> Result<FactToLeanIR, RuntimeError> {
        let step_fact_id = |fact: &Fact| -> Result<Option<FactId>, RuntimeError> {
            let known = self.known_fact_id_for_fact(fact)?;
            if known.is_some() || fact.to_string() != enclosing_goal.to_string() {
                Ok(known)
            } else {
                Ok(enclosing_goal_fact_id)
            }
        };
        match step {
            VerifiedBysEnum::ByBuiltinRule(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: FactProofToLeanIR::Builtin {
                    kind: BuiltinProofKindToLeanIR::Rule,
                    rule: BuiltinRuleToLeanIR::from_verified_label(
                        &result.msg,
                        &result.verify_what,
                    ),
                    subgoals: self.subgoals_to_lean_ir(&result.subgoals)?,
                },
            }),
            VerifiedBysEnum::ByBuiltinStrategy(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: FactProofToLeanIR::Builtin {
                    kind: BuiltinProofKindToLeanIR::Strategy,
                    rule: BuiltinRuleToLeanIR::from_verified_label(
                        &result.msg,
                        &result.verify_what,
                    ),
                    subgoals: self.subgoals_to_lean_ir(&result.subgoals)?,
                },
            }),
            VerifiedBysEnum::ByFact(result) => {
                let proof = match result.cite_what.as_ref() {
                    Stmt::Fact(source) => {
                        let source_fact_id = match result.source_fact_id {
                            Some(fact_id) => Some(fact_id),
                            None => self.citation_fact_id(
                                source,
                                &result.verify_what,
                                step_fact_id(&result.verify_what)?,
                            )?,
                        };
                        source_fact_id
                            .map(|source_fact_id| FactProofToLeanIR::KnownFact { source_fact_id })
                            .unwrap_or_else(|| FactProofToLeanIR::Unsupported {
                                reason: format!("cited fact `{}` has no stored FactId", source),
                            })
                    }
                    Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                        FactProofToLeanIR::Definition {
                            name: definition.name.clone(),
                        }
                    }
                    cited => FactProofToLeanIR::Unsupported {
                        reason: format!("unsupported composite citation `{}`", cited),
                    },
                };
                Ok(FactToLeanIR {
                    fact_id: step_fact_id(&result.verify_what)?,
                    proposition: result.verify_what.clone(),
                    proof,
                })
            }
            VerifiedBysEnum::ByKnownForall(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.known_forall_to_lean_ir(&result.result)?,
            }),
            VerifiedBysEnum::ByStatementMemo(goal, source) => Ok(FactToLeanIR {
                fact_id: step_fact_id(goal)?,
                proposition: goal.clone(),
                proof: FactProofToLeanIR::Memo {
                    proof: Box::new(self.verified_by_to_lean_ir(
                        goal,
                        source.fact_id.or(step_fact_id(goal)?),
                        &source.verified_by,
                    )?),
                },
            }),
        }
    }

    fn inferred_facts_to_lean_ir(
        &self,
        infer_result: &InferResult,
        excluded: &HashSet<String>,
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        let mut seen = excluded.clone();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            let source_fact = &output.itself_and_why_itself_is_stored.0;
            let source_id = output.fact_id.or(self.known_fact_id_for_fact(source_fact)?);
            let source_key = source_fact.to_string();
            if seen.insert(source_key) {
                inferred.push(FactToLeanIR {
                    fact_id: source_id,
                    proposition: source_fact.clone(),
                    proof: FactProofToLeanIR::Inference {
                        source_fact_id: None,
                        reason: output.itself_and_why_itself_is_stored.1.clone(),
                    },
                });
            }
            for fact in output.inferred_facts.iter() {
                if !seen.insert(fact.to_string()) {
                    continue;
                }
                inferred.push(FactToLeanIR {
                    fact_id: self.known_fact_id_for_fact(fact)?,
                    proposition: fact.clone(),
                    proof: FactProofToLeanIR::Inference {
                        source_fact_id: source_id,
                        reason: output.itself_and_why_itself_is_stored.1.clone(),
                    },
                });
            }
        }
        Ok(inferred)
    }
}

fn param_group_to_lean_ir(group: &ParamGroupWithParamType) -> ParamGroupToLeanIR {
    let param_type = match &group.param_type {
        ParamType::Set(_) => ParamTypeToLeanIR::LitexSet,
        ParamType::NonemptySet(_) => ParamTypeToLeanIR::LitexNonemptySet,
        ParamType::Obj(Obj::StandardSet(StandardSet::R)) => ParamTypeToLeanIR::Real,
        other => ParamTypeToLeanIR::Unsupported(other.to_string()),
    };
    ParamGroupToLeanIR {
        names: group
            .params
            .iter()
            .map(|binding| binding.name().to_string())
            .collect(),
        param_type,
    }
}

fn to_lean_ir_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}
