use crate::prelude::*;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
struct ToLeanIrContext {
    local_fact_ids: HashMap<String, FactId>,
}

impl ToLeanIrContext {
    fn with_infer_result(&self, infer_result: &InferResult) -> Self {
        let mut nested = self.clone();
        for output in infer_result.store_fact_outputs.iter() {
            if let Some(fact_id) = output.fact_id {
                nested.local_fact_ids.insert(
                    output.itself_and_why_itself_is_stored.0.to_string(),
                    fact_id,
                );
            }
        }
        nested
    }
}

impl Runtime {
    pub(crate) fn build_stmt_to_lean_ir(
        &self,
        result: &StmtResult,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        if let Some(success) = result.factual_success() {
            ensure_fact_objects_lower_to_lean_ir(&success.stmt)?;
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
                for fact in stmt.iff_facts.iter() {
                    ensure_fact_objects_lower_to_lean_ir(fact)?;
                }
                Ok(StmtToLeanIR::Prop(PropToLeanIR {
                    name: stmt.name.clone(),
                    params: stmt
                        .params_def_with_type
                        .groups
                        .iter()
                        .map(param_group_to_lean_ir)
                        .collect::<Result<Vec<_>, RuntimeError>>()?,
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
                    ensure_fact_objects_lower_to_lean_ir(fact)?;
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
        self.fact_to_lean_ir_from_success_with_context(success, &ToLeanIrContext::default())
    }

    fn fact_to_lean_ir_from_success_with_context(
        &self,
        success: &FactualStmtSuccess,
        context: &ToLeanIrContext,
    ) -> Result<FactToLeanIR, RuntimeError> {
        Ok(FactToLeanIR {
            fact_id: success.fact_id,
            proposition: success.stmt.clone(),
            proof: self.verified_by_to_lean_ir(
                &success.stmt,
                success.fact_id,
                &success.verified_by,
                context,
            )?,
        })
    }

    fn fact_to_lean_ir_from_result(
        &self,
        result: &StmtResult,
        result_context: &str,
        context: &ToLeanIrContext,
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
                    reason: format!("{} did not return a factual success", result_context),
                },
            });
        };
        self.fact_to_lean_ir_from_success_with_context(success, context)
    }

    fn verified_by_to_lean_ir(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        verified_by: &VerifiedByResult,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => self.builtin_rule_application_to_lean_ir(
                goal,
                &result.msg,
                result.evidence.as_ref(),
                &result.subgoals,
                context,
            ),
            VerifiedByResult::BuiltinStrategy(result) => self.builtin_rule_application_to_lean_ir(
                goal,
                &result.msg,
                result.evidence.as_ref(),
                &result.subgoals,
                context,
            ),
            VerifiedByResult::Fact(result) => match result.cite_what.as_ref() {
                Stmt::Fact(source_fact) => self.fact_citation_to_lean_ir(
                    goal,
                    goal_fact_id,
                    source_fact,
                    result.source_fact_id,
                    result.equality_transport.as_ref(),
                    context,
                ),
                Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                    Ok(FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::DefinitionReduction {
                            definition: definition.name.clone(),
                        },
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
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
                self.known_forall_to_lean_ir(goal, result, context)
            }
            VerifiedByResult::VerifiedBys(result) => {
                let mut steps = Vec::with_capacity(result.cite_what.len());
                for step in result.cite_what.iter() {
                    steps.push(self.verified_bys_step_to_lean_ir(
                        step,
                        goal,
                        goal_fact_id,
                        context,
                    )?);
                }
                Ok(FactProofToLeanIR::Composite { steps })
            }
            VerifiedByResult::ForallProof(result) => {
                let parameter_reason = InferReason::ParameterDefinition.store_reason();
                let parameter_premises = result
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| output.itself_and_why_itself_is_stored.1 == parameter_reason)
                    .map(|output| {
                        let fact = output.itself_and_why_itself_is_stored.0.clone();
                        let fact_id = output.fact_id.ok_or_else(|| {
                            to_lean_ir_error(
                                &fact.line_file(),
                                "a forall parameter premise reached To-Lean without a FactId",
                            )
                        })?;
                        Ok(LocalPremiseToLeanIR::new(fact_id, fact))
                    })
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let mut premises = Vec::with_capacity(result.forall_fact.dom_facts.len());
                for dom_fact in result.forall_fact.dom_facts.iter() {
                    let fact = dom_fact.clone();
                    let fact_id = result
                        .assumption_infers
                        .store_fact_outputs
                        .iter()
                        .find(|output| {
                            output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string()
                        })
                        .and_then(|output| output.fact_id)
                        .ok_or_else(|| {
                            to_lean_ir_error(
                                &fact.line_file(),
                                "a forall domain premise reached To-Lean without a FactId",
                            )
                        })?;
                    premises.push(LocalPremiseToLeanIR::new(fact_id, fact));
                }
                let conclusion_context = context.with_infer_result(&result.assumption_infers);
                let mut conclusions = Vec::with_capacity(result.proves.len());
                for proved in result.proves.iter() {
                    conclusions.push(self.fact_to_lean_ir_from_result(
                        proved.result.as_ref(),
                        "forall conclusion",
                        &conclusion_context,
                    )?);
                }
                Ok(FactProofToLeanIR::ForallIntroduction {
                    parameter_premises,
                    premises,
                    conclusions,
                })
            }
            VerifiedByResult::StatementMemo(source) => Ok(FactProofToLeanIR::Memo {
                proof: Box::new(self.verified_by_to_lean_ir(
                    goal,
                    source.fact_id.or(goal_fact_id),
                    &source.verified_by,
                    context,
                )?),
            }),
        }
    }

    fn fact_citation_to_lean_ir(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        source_fact: &Fact,
        recorded_source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let source_fact_id = match recorded_source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, goal, goal_fact_id, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("verified citation `{}` has no stored FactId", source_fact),
            });
        };

        let Some(equality_transport) = equality_transport else {
            if source_fact.to_string() == goal.to_string() {
                return Ok(FactProofToLeanIR::KnownFactCitation { source_fact_id });
            }
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::OtherUnsupported {
                    name: format!(
                        "citation `{}` changed goal `{}` without structured rewrite evidence",
                        source_fact, goal
                    ),
                },
                parameter_requirements: Vec::new(),
                premises: vec![FactToLeanIR {
                    fact_id: Some(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: FactProofToLeanIR::KnownFactCitation { source_fact_id },
                }],
            });
        };
        if equality_transport.steps.is_empty() {
            return Ok(FactProofToLeanIR::KnownFactCitation { source_fact_id });
        }

        let mut premises = Vec::with_capacity(equality_transport.steps.len() + 1);
        premises.push(FactToLeanIR {
            fact_id: Some(source_fact_id),
            proposition: source_fact.clone(),
            proof: FactProofToLeanIR::KnownFactCitation { source_fact_id },
        });
        let mut steps = Vec::with_capacity(equality_transport.steps.len());
        for rewrite in equality_transport.steps.iter() {
            let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
            let Some(equality_fact_id) = rewrite.equality_fact_id else {
                return Ok(FactProofToLeanIR::Unsupported {
                    reason: format!(
                        "equality transport `{}` -> `{}` through `{}` has no compiler proof provenance",
                        rewrite.from, rewrite.to, equality_fact
                    ),
                });
            };
            let left_key = obj_equality_key(&rewrite.equality.left);
            let right_key = obj_equality_key(&rewrite.equality.right);
            let from_key = obj_equality_key(&rewrite.from);
            let to_key = obj_equality_key(&rewrite.to);
            let direction = if from_key == left_key && to_key == right_key {
                EqualityRewriteDirectionToLeanIR::Forward
            } else if from_key == right_key && to_key == left_key {
                EqualityRewriteDirectionToLeanIR::Backward
            } else {
                return Ok(FactProofToLeanIR::Unsupported {
                    reason: format!(
                        "equality rewrite edge `{}` -> `{}` is not oriented by `{}`",
                        rewrite.from, rewrite.to, equality_fact
                    ),
                });
            };
            premises.push(FactToLeanIR {
                fact_id: Some(equality_fact_id),
                proposition: equality_fact,
                proof: FactProofToLeanIR::KnownFactCitation {
                    source_fact_id: equality_fact_id,
                },
            });
            steps.push(EqualityRewriteStepToLeanIR {
                from: rewrite.from.clone(),
                to: rewrite.to.clone(),
                direction,
            });
        }

        Ok(FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::EqualityRewrite(EqualityRewriteToLeanIR { steps }),
            parameter_requirements: Vec::new(),
            premises,
        })
    }

    fn citation_fact_id(
        &self,
        cited_fact: &Fact,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        context: &ToLeanIrContext,
    ) -> Result<Option<FactId>, RuntimeError> {
        if let Some(fact_id) = context.local_fact_ids.get(&cited_fact.to_string()) {
            return Ok(Some(*fact_id));
        }
        if let Some(fact_id) = self.known_fact_id_for_fact(cited_fact)? {
            return Ok(Some(fact_id));
        }
        // A forall conclusion can cite one of its temporary premises. The
        // local environment has already been popped when statement IR is
        // assembled, but verification stored the identical conclusion under
        // the premise's ID and retained that ID on the result.
        if cited_fact.to_string() == goal.to_string() {
            return Ok(goal_fact_id);
        }
        Ok(None)
    }

    fn known_forall_to_lean_ir(
        &self,
        goal: &Fact,
        result: &KnownForallInstantiationResult,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let Stmt::Fact(source_fact) = result.cite_what.as_ref() else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: "known-forall verification did not cite a fact".to_string(),
            });
        };
        let Fact::ForallFact(source_forall) = source_fact else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: "known-forall verification cited a non-forall fact".to_string(),
            });
        };
        let source_fact_id = match result.source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, source_fact, None, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("known forall `{}` has no stored FactId", source_fact),
            });
        };

        let mut param_types = Vec::new();
        for group in source_forall.params_def_with_type.groups.iter() {
            let param_type = param_type_to_lean_ir(&group.param_type)?;
            for _ in group.params.iter() {
                param_types.push(param_type.clone());
            }
        }
        if result.instantiation.len() != param_types.len() {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` recorded {} arguments for {} parameter types",
                    source_fact,
                    result.instantiation.len(),
                    param_types.len()
                ),
            });
        }
        let arguments = result
            .instantiation
            .iter()
            .zip(param_types)
            .map(|(item, param_type)| KnownForallArgumentToLeanIR {
                param: item.param.clone(),
                argument: item.arg_obj.clone(),
                param_type,
            })
            .collect::<Vec<_>>();
        let mut parameter_requirements = Vec::new();
        let mut requirements = Vec::new();
        for requirement in result.requirements.iter() {
            let requirement_ir = self.fact_to_lean_ir_from_result(
                requirement.result.as_ref(),
                "known-forall requirement",
                context,
            )?;
            match requirement.kind {
                KnownForallRequirementKind::ParameterType => {
                    parameter_requirements.push(requirement_ir)
                }
                KnownForallRequirementKind::Domain => requirements.push(requirement_ir),
            }
        }
        if parameter_requirements.len() != arguments.len() {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` recorded {} arguments but {} parameter requirements",
                    source_fact,
                    arguments.len(),
                    parameter_requirements.len()
                ),
            });
        }

        let Some(source_conclusion) = source_forall.then_facts.first() else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("known forall `{}` has no conclusion", source_fact),
            });
        };
        if source_forall.then_facts.len() != 1 {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` has {} conclusions instead of one matched conclusion",
                    source_fact,
                    source_forall.then_facts.len()
                ),
            });
        }
        let argument_objects = arguments
            .iter()
            .map(|argument| argument.argument.clone())
            .collect::<Vec<_>>();
        let param_to_arg_map = source_forall
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&argument_objects);
        let instantiated_conclusion = self.inst_fact(
            &source_conclusion.clone().to_fact(),
            &param_to_arg_map,
            ParamObjType::Forall,
            None,
        )?;
        let application = FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::KnownForallInstantiation {
                source_fact_id,
                arguments,
            },
            parameter_requirements,
            premises: requirements,
        };
        if instantiated_conclusion.to_string() == goal.to_string() {
            return Ok(application);
        }

        let instantiated_fact = FactToLeanIR {
            fact_id: None,
            proposition: instantiated_conclusion.clone(),
            proof: application,
        };
        if facts_align_by_rational_normalization(&instantiated_conclusion, goal) {
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::Normalization {
                    kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                },
                parameter_requirements: Vec::new(),
                premises: vec![instantiated_fact],
            });
        }

        Ok(FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::OtherUnsupported {
                name: format!(
                    "known-forall instance `{}` does not structurally match goal `{}`",
                    instantiated_conclusion, goal
                ),
            },
            parameter_requirements: Vec::new(),
            premises: vec![instantiated_fact],
        })
    }

    fn builtin_rule_application_to_lean_ir(
        &self,
        goal: &Fact,
        label: &str,
        evidence: Option<&BuiltinRuleEvidence>,
        subgoals: &[StmtResult],
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let rule = match evidence {
            Some(evidence) => ProofRuleToLeanIR::Builtin(evidence.into()),
            None => ProofRuleToLeanIR::from_verified_builtin_label(label, goal),
        };
        Ok(FactProofToLeanIR::RuleApplication {
            rule,
            parameter_requirements: Vec::new(),
            premises: self.subgoals_to_lean_ir(subgoals, context)?,
        })
    }

    fn subgoals_to_lean_ir(
        &self,
        subgoals: &[StmtResult],
        context: &ToLeanIrContext,
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        subgoals
            .iter()
            .map(|result| self.fact_to_lean_ir_from_result(result, "builtin subgoal", context))
            .collect()
    }

    fn verified_bys_step_to_lean_ir(
        &self,
        step: &VerifiedBysEnum,
        enclosing_goal: &Fact,
        enclosing_goal_fact_id: Option<FactId>,
        context: &ToLeanIrContext,
    ) -> Result<FactToLeanIR, RuntimeError> {
        let step_fact_id = |fact: &Fact| -> Result<Option<FactId>, RuntimeError> {
            let known =
                self.citation_fact_id(fact, enclosing_goal, enclosing_goal_fact_id, context)?;
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
                proof: self.builtin_rule_application_to_lean_ir(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByBuiltinStrategy(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.builtin_rule_application_to_lean_ir(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByFact(result) => {
                let proof = match result.cite_what.as_ref() {
                    Stmt::Fact(source) => self.fact_citation_to_lean_ir(
                        &result.verify_what,
                        step_fact_id(&result.verify_what)?,
                        source,
                        result.source_fact_id,
                        result.equality_transport.as_ref(),
                        context,
                    )?,
                    Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                        FactProofToLeanIR::RuleApplication {
                            rule: ProofRuleToLeanIR::DefinitionReduction {
                                definition: definition.name.clone(),
                            },
                            parameter_requirements: Vec::new(),
                            premises: Vec::new(),
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
                proof: self.known_forall_to_lean_ir(
                    &result.verify_what,
                    &result.result,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByStatementMemo(goal, source) => Ok(FactToLeanIR {
                fact_id: step_fact_id(goal)?,
                proposition: goal.clone(),
                proof: FactProofToLeanIR::Memo {
                    proof: Box::new(self.verified_by_to_lean_ir(
                        goal,
                        source.fact_id.or(step_fact_id(goal)?),
                        &source.verified_by,
                        context,
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

fn param_group_to_lean_ir(
    group: &ParamGroupWithParamType,
) -> Result<ParamGroupToLeanIR, RuntimeError> {
    Ok(ParamGroupToLeanIR {
        names: group
            .params
            .iter()
            .map(|binding| binding.name().to_string())
            .collect(),
        param_type: param_type_to_lean_ir(&group.param_type)?,
    })
}

fn param_type_to_lean_ir(param_type: &ParamType) -> Result<ParamTypeToLeanIR, RuntimeError> {
    match param_type {
        ParamType::Set(_) => Ok(ParamTypeToLeanIR::LitexSet),
        ParamType::NonemptySet(_) => Ok(ParamTypeToLeanIR::LitexNonemptySet),
        ParamType::FiniteSet(_) => Ok(ParamTypeToLeanIR::LitexFiniteSet),
        ParamType::Obj(obj) => ObjToLeanIR::lower(obj)
            .map(ParamTypeToLeanIR::MemberOf)
            .map_err(|message| to_lean_ir_error(&default_line_file(), message)),
    }
}

fn facts_align_by_rational_normalization(source: &Fact, goal: &Fact) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(goal)) = (source, goal) else {
        return false;
    };
    if source.key() != goal.key() || source.is_true() != goal.is_true() {
        return false;
    }
    let source_args = source.args_ref();
    let goal_args = goal.args_ref();
    source_args.len() == goal_args.len()
        && source_args
            .iter()
            .zip(goal_args.iter())
            .all(|(source, goal)| objs_equal_by_rational_expression_evaluation(source, goal))
}

fn ensure_fact_objects_lower_to_lean_ir(fact: &Fact) -> Result<(), RuntimeError> {
    let mut objects = Vec::new();
    collect_fact_objects_for_to_lean(fact, &mut objects);
    for object in objects {
        ObjToLeanIR::lower(object)
            .map_err(|message| to_lean_ir_error(&fact.line_file(), message))?;
    }
    Ok(())
}

fn collect_fact_objects_for_to_lean<'a>(fact: &'a Fact, objects: &mut Vec<&'a Obj>) {
    match fact {
        Fact::AtomicFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ForallFact(fact) => collect_forall_objects_for_to_lean(fact, objects),
        Fact::ForallFactWithIff(fact) => {
            collect_forall_objects_for_to_lean(&fact.forall_fact, objects);
            for iff_fact in fact.iff_facts.iter() {
                collect_forall_conclusion_objects_for_to_lean(iff_fact, objects);
            }
        }
        Fact::NotForall(fact) => collect_forall_objects_for_to_lean(&fact.forall_fact, objects),
    }
}

fn collect_forall_objects_for_to_lean<'a>(fact: &'a ForallFact, objects: &mut Vec<&'a Obj>) {
    for group in fact.params_def_with_type.groups.iter() {
        if let ParamType::Obj(set) = &group.param_type {
            objects.push(set);
        }
    }
    for premise in fact.dom_facts.iter() {
        collect_fact_objects_for_to_lean(premise, objects);
    }
    for conclusion in fact.then_facts.iter() {
        collect_forall_conclusion_objects_for_to_lean(conclusion, objects);
    }
}

fn collect_forall_conclusion_objects_for_to_lean<'a>(
    fact: &'a ExistOrAndChainAtomicFact,
    objects: &mut Vec<&'a Obj>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(fact) => {
            objects.extend(fact.get_args_from_fact_ref())
        }
        ExistOrAndChainAtomicFact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
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
