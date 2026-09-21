//! Semantic node roles and Mermaid labels.

use super::*;

pub(super) fn success_stmt_role(success: &SuccessStmtResult) -> &'static str {
    match success {
        SuccessStmtResult::Fact(_) => "Fact",
        SuccessStmtResult::UnsafeStmt(_) => "UnsafeStmt",
        SuccessStmtResult::Definition(definition) => match definition {
            SuccessDefinitionStmtResult::LetObjStmt(_)
            | SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(_)
            | SuccessDefinitionStmtResult::HaveObjEqualStmt(_)
            | SuccessDefinitionStmtResult::HaveObjByExistFactsStmt(_)
            | SuccessDefinitionStmtResult::ObtainObjFromExistFact(_)
            | SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(_)
            | SuccessDefinitionStmtResult::ObtainObjFromThm(_)
            | SuccessDefinitionStmtResult::HaveByPreimageStmt(_)
            | SuccessDefinitionStmtResult::HaveFnEqualStmt(_)
            | SuccessDefinitionStmtResult::HaveFnEqualCaseByCaseStmt(_)
            | SuccessDefinitionStmtResult::HaveFnByInducStmt(_)
            | SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(_) => "DefObjStmt",
            SuccessDefinitionStmtResult::DefPropStmt(_)
            | SuccessDefinitionStmtResult::DefAbstractPropStmt(_) => "DefPredicateStmt",
            SuccessDefinitionStmtResult::DefSettingStmt(_)
            | SuccessDefinitionStmtResult::DefTemplateStmt(_)
            | SuccessDefinitionStmtResult::DefStructStmt(_) => "DefInterfaceStmt",
            SuccessDefinitionStmtResult::DefAlgoStmt(_) => "DefAlgoStmt",
            SuccessDefinitionStmtResult::DefThmStmt(_) => "DefThmStmt",
            SuccessDefinitionStmtResult::AxiomStmt(_) => "AxiomStmt",
            SuccessDefinitionStmtResult::DefStrategyStmt(_) => "DefStrategyStmt",
        },
        SuccessStmtResult::ReleaseThmStmt(_) => "ReleaseThmStmt",
        SuccessStmtResult::ReleaseStructDefStmt(_) => "ReleaseStructDefStmt",
        SuccessStmtResult::By(_) => "ByStmt",
        SuccessStmtResult::Witness(_) => "WitnessStmt",
        SuccessStmtResult::ProofBlock(_) => "ProofBlockStmt",
        SuccessStmtResult::Command(_) => "CommandStmt",
    }
}

pub(super) fn verify_fact_role(result: &SuccessFactProofNode) -> &'static str {
    match result {
        SuccessFactProofNode::AtomicFact(_) => "AtomicFact",
        SuccessFactProofNode::ExistFact(_) => "ExistFact",
        SuccessFactProofNode::OrFact(_) => "OrFact",
        SuccessFactProofNode::AndFact(_) => "AndFact",
        SuccessFactProofNode::ChainFact(_) => "ChainFact",
        SuccessFactProofNode::ForallFact(_) => "ForallFact",
        SuccessFactProofNode::ForallFactWithIff(_) => "ForallFactWithIff",
        SuccessFactProofNode::NotForallFact(_) => "NotForallFact",
    }
}

pub(super) fn transform_role(rule: &FactTransformationRule) -> &'static str {
    match rule {
        FactTransformationRule::EqualityRewrite(_) => "EqualityRewrite",
        FactTransformationRule::RationalNormalization => "RationalNormalization",
        FactTransformationRule::AnonymousFunctionBetaNormalization => {
            "AnonymousFunctionBetaNormalization"
        }
        FactTransformationRule::TransparentDefinitionReduction(_) => {
            "TransparentDefinitionReduction"
        }
    }
}

pub(super) fn infer_rule_role(rule: &InferRule) -> &'static str {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => "NaturalMembershipImpliesNonnegative",
        InferRule::PositiveStandardSetMembershipImpliesPositive(_) => {
            "PositiveStandardSetMembershipImpliesPositive"
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(_) => {
            "NegativeStandardSetMembershipImpliesNegative"
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(_) => {
            "NonzeroStandardSetMembershipImpliesNonzero"
        }
        InferRule::SetBuilderBaseMembershipProjection => "SetBuilderBaseMembershipProjection",
        InferRule::SetBuilderPredicateProjection { .. } => "SetBuilderPredicateProjection",
        InferRule::DefinedPredicateParameterRequirementProjection(_) => {
            "DefinedPredicateParameterRequirementProjection"
        }
        InferRule::DefinedPredicateDefinitionClauseProjection(_) => {
            "DefinedPredicateDefinitionClauseProjection"
        }
        InferRule::EqualityChainClosure(_) => "EqualityChainClosure",
        InferRule::NumericOrderChainClosure(_) => "NumericOrderChainClosure",
        InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(_) => {
            "ClosedPositivePowerEqualityImpliesEqualSideMembership"
        }
        InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(_) => {
            "PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership"
        }
        InferRule::RegisteredTransitivePredicateChainClosure(_) => {
            "RegisteredTransitivePredicateChainClosure"
        }
        InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_) => {
            "TupleEqualityWithKnownTupleImpliesTupleShape"
        }
        InferRule::CartesianMembershipProjection(_) => "CartesianMembershipProjection",
        InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => {
            "ListSetMembershipImpliesEqualityAlternatives"
        }
        InferRule::FunctionRangeMembershipImpliesCodomainMembership => {
            "FunctionRangeMembershipImpliesCodomainMembership"
        }
        InferRule::NumericOrderBoundImpliesZeroSign => "NumericOrderBoundImpliesZeroSign",
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            "MultiplicationByNegativeOneReversesOrderAgainstZero"
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            "StrictOrderComparedToZeroImpliesWeakOrder"
        }
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => {
            "MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet"
        }
        InferRule::SubsetImpliesElementwiseMembershipForall(_) => {
            "SubsetImpliesElementwiseMembershipForall"
        }
        InferRule::SupersetImpliesElementwiseMembershipForall(_) => {
            "SupersetImpliesElementwiseMembershipForall"
        }
        InferRule::ConjunctionImpliesComponent(_) => "ConjunctionImpliesComponent",
        InferRule::ChainImpliesComponent(_) => "ChainImpliesComponent",
    }
}

pub(super) fn atomic_predicate_domain_check_role(
    role: AtomicPredicateDomainCheckRole,
) -> &'static str {
    match role {
        AtomicPredicateDomainCheckRole::ChoiceFunctionIndexSet => "choice_index_set",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamilySet => "choice_family_set",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamily => "choice_family",
        AtomicPredicateDomainCheckRole::ChoiceFunctionMember => "choice_member",
        AtomicPredicateDomainCheckRole::PrimeNaturalArgument => "prime_natural_argument",
        AtomicPredicateDomainCheckRole::CoprimeNaturalArgument => "coprime_natural_argument",
        AtomicPredicateDomainCheckRole::DivisibilityIntegerArgument => {
            "divisibility_integer_argument"
        }
        AtomicPredicateDomainCheckRole::DivisibilityNonzeroIntegerArgument => {
            "divisibility_nonzero_integer_argument"
        }
        AtomicPredicateDomainCheckRole::OrderedRealCarrierEvidence => {
            "ordered_real_carrier_evidence"
        }
        AtomicPredicateDomainCheckRole::FunctionPropertySignature => "function_property_signature",
    }
}

pub(super) fn mermaid_label(label: &str) -> String {
    label
        .replace('"', "'")
        .replace('\n', " ")
        .replace('\r', " ")
}
