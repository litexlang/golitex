//! Fact proof composition, universal proofs, and proof reuse.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct SuccessCombinedFactProofResult {
    pub primary: Option<Rc<SuccessFactProofNode>>,
    pub steps: Vec<VerifyFactResult>,
}

pub struct SuccessForallProofResult {
    pub forall_fact: ForallFact,
    /// Exact parameter facts visible in the proof-owned lexical environment.
    /// These are proof-scope identities, not the sibling WD check identities.
    pub parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
    /// Exact source-domain facts visible after the parameters. A repeated
    /// domain premise intentionally reuses the earlier parameter FactId.
    pub domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
    pub assumption_infers: SuccessInferResult,
    pub proves: Vec<SuccessForallProvedFactResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessForallAssumptionFactResult {
    pub fact: Fact,
    pub fact_id: FactId,
}

pub struct SuccessForallProvedFactResult {
    pub stmt: ExistOrAndChainAtomicFact,
    pub result: Box<VerifyFactResult>,
    /// Exact local store performed after this conclusion was proved. Later
    /// conclusions may cite this truth-stage FactId and any typed consequences.
    pub store: SuccessStoreFactResult,
}

#[derive(Debug)]
pub struct SuccessReuseFactProofResult {
    pub source: Rc<SuccessFactProofNode>,
}

#[derive(Debug)]
pub enum SuccessFactProofResult {
    BuiltinRule(SuccessBuiltinFactProofResult),
    BuiltinStrategy(SuccessBuiltinFactProofResult),
    StoredFactCitation(SuccessStoredFactCitationProofResult),
    KnownForallInstantiation(SuccessInstantiateKnownForallResult),
    DefinitionReduction(SuccessDefinitionReductionFactProofResult),
    CheckedFunctionDefinitionReduction(SuccessCheckedFunctionDefinitionReductionFactProofResult),
    DiagnosticOnly(SuccessDiagnosticFactProofResult),
    CombinedProofs(SuccessCombinedFactProofResult),
    ForallProof(SuccessForallProofResult),
    Transform(Box<SuccessTransformFactResult>),
    /// Internal proof sharing; this is not a user-visible verification method.
    Reuse(Box<SuccessReuseFactProofResult>),
}

#[cfg(test)]
#[path = "../../../../tests/unit/result/verification/success_access.rs"]
mod test_support;

impl SuccessFactProofResult {
    pub fn builtin_rule_with_evidence(
        msg: impl Into<String>,
        evidence: BuiltinRuleEvidence,
        subgoals: Vec<VerifyFactResult>,
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
        clause_checks: Vec<(Fact, VerifyFactResult)>,
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
        let mut current = SuccessFactProofNode::new(
            source_fact.clone(),
            Self::stored_fact_citation(source_fact, source_fact_id, detail),
        );
        if let Some(transport) = equality_transport {
            if !transport.steps.is_empty() {
                current = SuccessFactProofNode::new(
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
                current = SuccessFactProofNode::new(
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

    pub fn combined_steps(steps: Vec<VerifyFactResult>) -> Self {
        Self::CombinedProofs(SuccessCombinedFactProofResult {
            primary: None,
            steps,
        })
    }

    pub fn forall_proof(
        forall_fact: ForallFact,
        parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
        domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
        assumption_infers: SuccessInferResult,
        proves: Vec<SuccessForallProvedFactResult>,
    ) -> Self {
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
                        step.verified()
                            .map(|result| result.is_verified_by_builtin_rules_only())
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
    pub fn new(
        stmt: ExistOrAndChainAtomicFact,
        result: VerifyFactResult,
        store: SuccessStoreFactResult,
    ) -> Self {
        SuccessForallProvedFactResult {
            stmt,
            result: Box::new(result),
            store,
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
            .field("store", &self.store)
            .finish()
    }
}

pub(super) fn merge_verified_by_with_steps(
    goal: Fact,
    verified_by: SuccessFactProofResult,
    step_results: Vec<VerifyFactResult>,
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
        primary: Some(Rc::new(SuccessFactProofNode::new(goal, verified_by))),
        steps: step_results,
    })
}
