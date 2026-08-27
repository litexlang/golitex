//! Constructors and accessors for successful verification evidence.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

impl SuccessFactStmtResult {
    pub fn new_with_verified_by_builtin_rules(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
    ) -> Self {
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_evidence_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::BuiltinStrategy(SuccessBuiltinFactProofResult {
            msg: strategy_label,
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(evidence),
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, SuccessInferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_and_steps(
        stmt: Fact,
        infers: SuccessInferResult,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::builtin_rule_with_evidence(
            builtin_rule_label,
            evidence,
            step_results,
        );
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rule_evidence_and_steps(
            stmt,
            SuccessInferResult::new(),
            builtin_rule_label,
            evidence,
            step_results,
        )
    }

    pub fn new_with_verified_by_known_fact_and_infer(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = merge_verified_by_with_steps(stmt.clone(), verified_by, step_results);
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_known_fact(
        stmt: Fact,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_known_fact_and_infer(
            stmt,
            SuccessInferResult::new(),
            verified_by,
            step_results,
        )
    }

    pub fn new_with_statement_proof_cache(
        stmt: Fact,
        infers: SuccessInferResult,
        source: Rc<SuccessVerifyFactResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rules(
            stmt,
            infers,
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        )
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/result/verification/success_access.rs"]
mod test_support;

impl SuccessFactProofResult {
    pub fn builtin_rule_with_evidence(
        msg: impl Into<String>,
        evidence: BuiltinRuleEvidence,
        subgoals: Vec<StmtResult>,
    ) -> Self {
        Self::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: msg.into(),
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(evidence),
            subgoals,
        })
    }

    pub fn stored_fact_citation(
        source_fact: Fact,
        source_fact_id: FactId,
        detail: Option<String>,
    ) -> Self {
        Self::StoredFactCitation(SuccessStoredFactCitationProofResult {
            detail,
            source_fact,
            source_fact_id,
        })
    }

    pub fn cited_definition(
        _goal: Fact,
        definition: DefPropStmt,
        argument_verification: SuccessVerifyArgsSatisfyParamDefResult,
        clause_checks: Vec<(Fact, StmtResult)>,
        detail: Option<String>,
    ) -> Self {
        let (clause_facts, clause_checks) = clause_checks.into_iter().unzip();
        Self::DefinitionReduction(SuccessDefinitionReductionFactProofResult {
            detail,
            definition,
            verification: Rc::new(DefinitionReductionVerificationEvidence {
                argument_verification,
                clause_facts,
                clause_checks,
            }),
        })
    }

    pub fn cited_fact_with_provenance(
        goal: Fact,
        source_fact: Fact,
        source_fact_id: FactId,
        equality_transport: Option<EqualityTransportEvidence>,
        fact_transformation: Option<FactTransformationEvidence>,
        detail: Option<String>,
    ) -> Result<Self, String> {
        if equality_transport
            .as_ref()
            .map(|result| result.steps.is_empty())
            .unwrap_or(true)
            && fact_transformation.is_none()
        {
            return Ok(Self::stored_fact_citation(
                source_fact,
                source_fact_id,
                detail,
            ));
        }
        let transformation_source = fact_transformation
            .as_ref()
            .map(|result| result.source.clone())
            .unwrap_or_else(|| goal.clone());
        let mut current = SuccessVerifyFactResult::new(
            source_fact.clone(),
            Self::stored_fact_citation(source_fact, source_fact_id, detail),
        );
        if let Some(transport) = equality_transport {
            if !transport.steps.is_empty() {
                current = SuccessVerifyFactResult::new(
                    transformation_source.clone(),
                    Self::Transform(Box::new(SuccessTransformFactResult::new(
                        FactTransformationRule::EqualityRewrite(transport),
                        current,
                    ))),
                );
            }
        }
        if let Some(transformation) = fact_transformation {
            for step in transformation.steps {
                current = SuccessVerifyFactResult::new(
                    step.result,
                    Self::Transform(Box::new(SuccessTransformFactResult::new(
                        step.rule, current,
                    ))),
                );
            }
        }
        let (result_fact, proof) = current.into_parts();
        if result_fact.to_string() == goal.to_string() {
            Ok(proof)
        } else {
            Err(format!(
                "fact provenance ended at `{}` instead of `{}`",
                result_fact, goal
            ))
        }
    }

    pub fn known_forall_instantiation(
        cite_what: Fact,
        source_fact_id: FactId,
        source_conclusion_location: ForallConclusionLocation,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
    ) -> Self {
        Self::KnownForallInstantiation(SuccessInstantiateKnownForallResult::new(
            cite_what,
            source_fact_id,
            source_conclusion_location,
            instantiation,
            requirements,
        ))
    }

    pub fn diagnostic(detail: impl Into<String>) -> Self {
        Self::DiagnosticOnly(SuccessDiagnosticFactProofResult {
            detail: detail.into(),
        })
    }

    pub fn fact_with_checked_function_definition_reduction(
        _goal: Fact,
        evidence: CheckedFunctionDefinitionReductionEvidence,
        detail: Option<String>,
    ) -> Self {
        Self::CheckedFunctionDefinitionReduction(
            SuccessCheckedFunctionDefinitionReductionFactProofResult {
                detail,
                verification: evidence,
            },
        )
    }

    pub fn cached_fact(fact: Fact, cite_fact_source: LineFile, source_fact_id: FactId) -> Self {
        Self::stored_fact_citation(fact.with_line_file(cite_fact_source), source_fact_id, None)
    }

    pub fn combined_steps(steps: Vec<StmtResult>) -> Self {
        Self::CombinedProofs(SuccessCombinedFactProofResult {
            primary: None,
            steps,
        })
    }

    pub fn forall_proof(
        forall_fact: ForallFact,
        then_results: Vec<StmtResult>,
        parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
        domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
        assumption_infers: SuccessInferResult,
    ) -> Self {
        let mut proves = Vec::new();
        for (stmt, result) in forall_fact
            .then_facts
            .iter()
            .cloned()
            .zip(then_results.into_iter())
        {
            proves.push(SuccessForallProvedFactResult::new(stmt, result));
        }
        Self::ForallProof(SuccessForallProofResult::new(
            forall_fact,
            parameter_assumptions,
            domain_assumptions,
            assumption_infers,
            proves,
        ))
    }

    pub fn tree_is_builtin_rules_only(&self) -> bool {
        match self {
            SuccessFactProofResult::BuiltinRule(r) | SuccessFactProofResult::BuiltinStrategy(r) => {
                !r.msg.is_empty()
            }
            SuccessFactProofResult::StoredFactCitation(_)
            | SuccessFactProofResult::KnownForallInstantiation(_)
            | SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::CheckedFunctionDefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => false,
            SuccessFactProofResult::CombinedProofs(w) => {
                let primary_is_builtin = w
                    .primary
                    .as_ref()
                    .map(|result| result.proof().tree_is_builtin_rules_only())
                    .unwrap_or(true);
                primary_is_builtin
                    && !w.steps.is_empty()
                    && w.steps.iter().all(|step| {
                        step.factual_success()
                            .map(SuccessFactStmtResult::is_verified_by_builtin_rules_only)
                            .unwrap_or(false)
                    })
            }
            SuccessFactProofResult::ForallProof(_) => false,
            SuccessFactProofResult::Transform(result) => {
                result.source.proof().tree_is_builtin_rules_only()
            }
            SuccessFactProofResult::Reuse(result) => {
                result.source.is_verified_by_builtin_rules_only()
            }
        }
    }
}

impl KnownForallInstantiationItem {
    pub fn new(param: String, arg_obj: Obj) -> Self {
        KnownForallInstantiationItem {
            param,
            arg: arg_obj.to_string(),
            arg_obj,
        }
    }
}

impl SuccessVerifyKnownForallRequirementResult {
    pub fn new(stmt: Fact, result: StmtResult, kind: KnownForallRequirementKind) -> Self {
        SuccessVerifyKnownForallRequirementResult {
            stmt,
            result: Box::new(result),
            kind,
        }
    }
}

impl SuccessInstantiateKnownForallResult {
    pub fn new(
        source_fact: Fact,
        source_fact_id: FactId,
        source_conclusion_location: ForallConclusionLocation,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
    ) -> Self {
        SuccessInstantiateKnownForallResult {
            source_fact,
            source_fact_id,
            source_conclusion_location,
            instantiation,
            requirements,
        }
    }
}

impl ObjectDefinitionItem {
    pub fn new(name: String, facts: Vec<Fact>) -> Self {
        ObjectDefinitionItem { name, facts }
    }
}

impl SuccessForallProofResult {
    pub fn new(
        forall_fact: ForallFact,
        parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
        domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
        assumption_infers: SuccessInferResult,
        proves: Vec<SuccessForallProvedFactResult>,
    ) -> Self {
        SuccessForallProofResult {
            forall_fact,
            parameter_assumptions,
            domain_assumptions,
            assumption_infers,
            proves,
        }
    }
}

impl SuccessForallProvedFactResult {
    pub fn new(stmt: ExistOrAndChainAtomicFact, result: StmtResult) -> Self {
        SuccessForallProvedFactResult {
            stmt,
            result: Box::new(result),
        }
    }
}

impl fmt::Debug for SuccessForallProofResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessForallProofResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("parameter_assumptions", &self.parameter_assumptions)
            .field("domain_assumptions", &self.domain_assumptions)
            .field("assumption_infers", &self.assumption_infers)
            .field("proves", &self.proves)
            .finish()
    }
}

impl fmt::Debug for SuccessForallProvedFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessForallProvedFactResult")
            .field("stmt", &self.stmt.to_string())
            .field("result", &self.result)
            .finish()
    }
}

impl SuccessVerifyTheoremResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyTheoremResult {
            name,
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimForallResult {
    pub fn new(
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyClaimForallResult {
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimFactResult {
    pub fn new(
        fact: Fact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_check: StmtResult,
    ) -> Self {
        SuccessVerifyClaimFactResult {
            fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_check: Box::new(conclusion_check),
        }
    }
}

impl From<SuccessVerifyClaimForallResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimForallResult) -> Self {
        SuccessVerifyClaimResult::Forall(Box::new(v))
    }
}

impl From<SuccessVerifyClaimFactResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimFactResult) -> Self {
        SuccessVerifyClaimResult::Fact(Box::new(v))
    }
}

impl SuccessVerifyByCasesResult {
    pub fn new(
        goal_well_definedness: Vec<SuccessVerifyFactWellDefinedResult>,
        coverage_check: StmtResult,
        then_facts: Vec<Fact>,
        branches: Vec<SuccessVerifyByCaseBranchResult>,
    ) -> Self {
        SuccessVerifyByCasesResult {
            goal_well_definedness,
            coverage_check: Box::new(coverage_check),
            then_facts,
            branches,
        }
    }
}

impl SuccessVerifyByContraResult {
    pub fn new(
        to_prove: Fact,
        reverse_assumption: Fact,
        reverse_assumption_fact_id: FactId,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        impossible_fact: AtomicFact,
        contradiction: SuccessVerifyContradictionResult,
    ) -> Self {
        SuccessVerifyByContraResult {
            to_prove,
            reverse_assumption,
            reverse_assumption_fact_id,
            proof_scope,
            proof_steps,
            impossible_fact,
            contradiction,
        }
    }
}

impl SuccessVerifyByAssignmentResult {
    pub fn new(
        assignment: Vec<(String, String)>,
        assumptions: Vec<SuccessVerifyByAssignmentAssumptionResult>,
        domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByAssignmentResult {
            assignment,
            assumptions,
            domain_checks,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyByEnumerateFiniteSetResult {
    pub fn new(
        parameters: Vec<String>,
        parameter_sets: Vec<ListSet>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        SuccessVerifyByEnumerateFiniteSetResult {
            parameters,
            parameter_sets,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}

impl SuccessVerifyByForResult {
    pub fn assignments(&self) -> &[SuccessVerifyByAssignmentResult] {
        match self {
            Self::Ranges(result) => &result.assignments,
            Self::CartesianProductOfListSets(result) => &result.assignments,
        }
    }

    pub fn assignments_mut(&mut self) -> &mut Vec<SuccessVerifyByAssignmentResult> {
        match self {
            Self::Ranges(result) => &mut result.assignments,
            Self::CartesianProductOfListSets(result) => &mut result.assignments,
        }
    }

    pub fn into_assignments(self) -> Vec<SuccessVerifyByAssignmentResult> {
        match self {
            Self::Ranges(result) => result.assignments,
            Self::CartesianProductOfListSets(result) => result.assignments,
        }
    }

    pub fn ranges(
        parameters: Vec<SuccessVerifyByForRangeParameterResult>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        Self::Ranges(Box::new(SuccessVerifyByForRangesResult {
            parameters,
            prove_goal,
            assignments,
            generated_forall,
        }))
    }

    pub fn cartesian_product_of_list_sets(
        parameter: String,
        factors: Vec<ListSet>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        Self::CartesianProductOfListSets(Box::new(
            SuccessVerifyByForCartesianProductOfListSetsResult {
                parameter,
                factors,
                prove_goal,
                assignments,
                generated_forall,
            },
        ))
    }
}

impl SuccessVerifyByEnumerateRangeResult {
    pub fn new(
        element: Obj,
        range: ClosedRangeOrRange,
        membership_fact: Fact,
        generated_cases: Fact,
        membership_check: StmtResult,
        endpoint_checks: Vec<SuccessVerifyByEnumerateRangeEndpointResult>,
    ) -> Self {
        SuccessVerifyByEnumerateRangeResult {
            element,
            range,
            membership_fact,
            generated_cases,
            membership_check: Box::new(membership_check),
            endpoint_checks,
        }
    }
}

impl SuccessVerifyByEnumerateRangeEndpointResult {
    pub fn new(
        position: SuccessVerifyByEnumerateRangeEndpointPosition,
        endpoint: Obj,
        integer_membership_fact: Fact,
        verification: StmtResult,
    ) -> Self {
        Self {
            position,
            endpoint,
            integer_membership_fact,
            verification: Box::new(verification),
        }
    }
}

impl SuccessVerifyByInducResult {
    pub fn new(
        parameter_binding: SymbolBinding,
        parameter: Obj,
        prove_goals: Vec<Fact>,
        generated_forall: ForallFact,
        proof: SuccessVerifyByInducProofResult,
    ) -> Self {
        SuccessVerifyByInducResult {
            parameter_binding,
            parameter,
            prove_goals,
            generated_forall,
            proof,
        }
    }
}

impl SuccessVerifyByExtensionResult {
    pub fn new(
        left: String,
        right: String,
        prove_goal: String,
        left_to_right_subset: String,
        right_to_left_subset: String,
        proof_steps: Vec<StmtResult>,
        left_to_right_check: StmtResult,
        right_to_left_check: StmtResult,
    ) -> Self {
        SuccessVerifyByExtensionResult {
            left,
            right,
            prove_goal,
            left_to_right_subset,
            right_to_left_subset,
            proof_steps,
            left_to_right_check: Box::new(left_to_right_check),
            right_to_left_check: Box::new(right_to_left_check),
        }
    }
}

impl SuccessVerifyByPropRegistrationResult {
    pub fn new(
        registration_type: String,
        prop_name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        assumption_infers: SuccessInferResult,
        proof_steps: Vec<StmtResult>,
        forall_check: StmtResult,
    ) -> Self {
        SuccessVerifyByPropRegistrationResult {
            registration_type,
            prop_name,
            forall_fact,
            well_definedness,
            assumption_infers,
            proof_steps,
            forall_check: Box::new(forall_check),
        }
    }
}

impl SuccessVerifyByChoiceResult {
    pub fn new(
        proof_kind: SuccessVerifyByChoiceProofKind,
        target: SuccessVerifyByChoiceTargetResult,
        proof_steps: Vec<StmtResult>,
        obligations: Vec<SuccessVerifyByChoiceObligationResult>,
        trusted_conclusion: Fact,
        trusted_conclusion_fact_id: FactId,
    ) -> Self {
        SuccessVerifyByChoiceResult {
            proof_kind,
            target,
            proof_steps,
            obligations,
            trusted_conclusion,
            trusted_conclusion_fact_id,
        }
    }
}

impl SuccessVerifyTheoremApplicationResult {
    pub fn new(
        theorem: String,
        source_fact_id: Option<FactId>,
        arguments: Vec<Obj>,
        domain_facts: Vec<Fact>,
        direct_conclusions: Vec<Fact>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        domain_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyTheoremApplicationResult {
            theorem,
            arguments,
            direct_conclusions,
            source: SuccessVerifyTheoremApplicationSourceResult::Litex(
                SuccessVerifyLitexTheoremApplicationResult {
                    source_fact_id,
                    argument_verification: argument_verification.map(Box::new),
                    domain_facts,
                    domain_checks,
                },
            ),
        }
    }

    pub fn new_builtin(
        theorem_id: BuiltinTheoremId,
        arguments: Vec<Obj>,
        requirement_facts: Vec<Fact>,
        requirement_roles: Vec<BuiltinTheoremRequirementRole>,
        direct_conclusions: Vec<Fact>,
        requirement_checks: Vec<StmtResult>,
        provenance: Option<BuiltinTheoremProvenance>,
    ) -> Self {
        SuccessVerifyTheoremApplicationResult {
            theorem: theorem_id.as_str().to_string(),
            arguments,
            direct_conclusions,
            source: SuccessVerifyTheoremApplicationSourceResult::Builtin(
                SuccessVerifyBuiltinTheoremApplicationResult {
                    theorem_id,
                    requirement_facts,
                    requirement_roles,
                    requirement_checks,
                    conclusion_well_definedness: None,
                    provenance,
                },
            ),
        }
    }

    pub fn new_builtin_with_conclusion_well_definedness(
        theorem_id: BuiltinTheoremId,
        arguments: Vec<Obj>,
        requirement_facts: Vec<Fact>,
        requirement_roles: Vec<BuiltinTheoremRequirementRole>,
        direct_conclusions: Vec<Fact>,
        requirement_checks: Vec<StmtResult>,
        conclusion_well_definedness: SuccessVerifyFactWellDefinedResult,
        provenance: Option<BuiltinTheoremProvenance>,
    ) -> Self {
        let mut result = Self::new_builtin(
            theorem_id,
            arguments,
            requirement_facts,
            requirement_roles,
            direct_conclusions,
            requirement_checks,
            provenance,
        );
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &mut result.source
        else {
            unreachable!("new_builtin constructs builtin theorem evidence")
        };
        source.conclusion_well_definedness = Some(conclusion_well_definedness);
        result
    }
}

impl SuccessVerifyByTheoremSelectionResult {
    pub fn new(
        temporary_application: StmtResult,
        selected_fact: AtomicFact,
        selected_fact_check: StmtResult,
    ) -> Self {
        Self {
            temporary_application: Box::new(temporary_application),
            selected_fact,
            selected_fact_check: Box::new(selected_fact_check),
        }
    }
}

impl SuccessVerifyByDefinitionResult {
    pub fn new(
        prop: String,
        definition: Option<DefPropStmt>,
        arguments: Vec<String>,
        definition_clauses: Vec<String>,
        stored_fact: String,
        concrete_user_prop: bool,
        definition_clause_facts: Vec<Fact>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        clause_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyByDefinitionResult {
            prop,
            definition,
            arguments,
            definition_clauses,
            stored_fact,
            concrete_user_prop,
            definition_clause_facts,
            argument_verification: argument_verification.map(Box::new),
            clause_checks,
        }
    }
}

impl fmt::Debug for SuccessVerifyClaimResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SuccessVerifyClaimResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            SuccessVerifyClaimResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyTheoremResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyTheoremResult")
            .field("name", &self.name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimForallResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimForallResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimFactResult")
            .field("fact", &self.fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_check", &self.conclusion_check)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCasesResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let cases = self
            .branches
            .iter()
            .map(|branch| branch.assumption.to_string())
            .collect::<Vec<_>>();
        let then_facts = self
            .then_facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<_>>();
        f.debug_struct("SuccessVerifyByCasesResult")
            .field("goal_well_definedness", &self.goal_well_definedness)
            .field("coverage_check", &self.coverage_check)
            .field("cases", &cases)
            .field("then_facts", &then_facts)
            .field("branches", &self.branches)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseBranchResult")
            .field("assumption", &self.assumption.to_string())
            .field("assumption_fact_id", &self.assumption_fact_id)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("exit", &self.exit)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchExitResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Conclusions(result) => f.debug_tuple("Conclusions").field(result).finish(),
            Self::Contradiction(result) => f.debug_tuple("Contradiction").field(result).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyByCaseConclusionsResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseConclusionsResult")
            .field("checks", &self.checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseContradictionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseContradictionResult")
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByContraResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByContraResult")
            .field("to_prove", &self.to_prove.to_string())
            .field("reverse_assumption", &self.reverse_assumption.to_string())
            .field(
                "reverse_assumption_fact_id",
                &self.reverse_assumption_fact_id,
            )
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByPropRegistrationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByPropRegistrationResult")
            .field("registration_type", &self.registration_type)
            .field("prop_name", &self.prop_name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_steps", &self.proof_steps)
            .field("forall_check", &self.forall_check)
            .finish()
    }
}

fn merge_verified_by_with_steps(
    goal: Fact,
    verified_by: SuccessFactProofResult,
    step_results: Vec<StmtResult>,
) -> SuccessFactProofResult {
    if step_results.is_empty() {
        return verified_by;
    }
    if matches!(
        &verified_by,
        SuccessFactProofResult::CombinedProofs(result)
            if result.primary.is_none() && result.steps.is_empty()
    ) {
        return SuccessFactProofResult::combined_steps(step_results);
    }
    SuccessFactProofResult::CombinedProofs(SuccessCombinedFactProofResult {
        primary: Some(Rc::new(SuccessVerifyFactResult::new(goal, verified_by))),
        steps: step_results,
    })
}
