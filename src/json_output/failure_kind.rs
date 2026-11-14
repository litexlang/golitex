use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    VerifyAtomicExceptEqualityFactFailed, VerifyEqualityFailed,
};
use crate::prelude::*;

/// Presentation categories derived from typed failed stages and bounded numeric
/// observations, never from prose.
/// A missing proof is a soft rejection, not a RuntimeError or a disproof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FailureKind {
    WellDefined,
    ProofSearch,
    Membership,
    Nonempty,
    NameClash,
    Arity,
    Unsupported,
    Instantiation,
    Storage,
    Domain,
    DefinitionConstruction,
    StructExpansion,
    DefinitionProofUnavailable,
    NameNotFound,
    Evaluation,
    AlgorithmDispatch,
    DepthLimit,
    CyclicEvaluation,
    AggregateBudget,
    AggregateRange,
    ExactDecimalBudget,
}

impl FailureKind {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::WellDefined => "well_defined",
            Self::ProofSearch => "proof_search",
            Self::Membership => "membership",
            Self::Nonempty => "nonempty",
            Self::NameClash => "name_clash",
            Self::Arity => "arity",
            Self::Unsupported => "unsupported",
            Self::Instantiation => "instantiation",
            Self::Storage => "storage",
            Self::Domain => "domain",
            Self::DefinitionConstruction => "definition_construction",
            Self::StructExpansion => "struct_expansion",
            Self::DefinitionProofUnavailable => "definition_proof_unavailable",
            Self::NameNotFound => "name_not_found",
            Self::Evaluation => "evaluation",
            Self::AlgorithmDispatch => "algorithm_dispatch",
            Self::DepthLimit => "depth_limit",
            Self::CyclicEvaluation => "cyclic_evaluation",
            Self::AggregateBudget => "aggregate_budget",
            Self::AggregateRange => "aggregate_range",
            Self::ExactDecimalBudget => "exact_decimal_budget",
        }
    }

    pub(super) fn for_verification(result: &VerifyFactResult) -> Self {
        debug_assert!(
            result.is_failed(),
            "diagnostics require an actual failed result"
        );
        if result.is_wd_failed() {
            return Self::WellDefined;
        }
        match result {
            VerifyFactResult::ForallFact(r) => match r.as_ref() {
                VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                    failed_then,
                    ..
                }) => Self::for_verification(failed_then),
                VerifyForallFactResult::Failed(
                    VerifyForallFactFailed::FailToVerifyWellDefined(_),
                ) => Self::WellDefined,
                VerifyForallFactResult::Success(_) => unreachable!("diagnostics require a failure"),
            },
            VerifyFactResult::ForallFactWithIff(r) => match r.as_ref() {
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailThenImpliesIff {
                        then_implies_iff, ..
                    },
                ) => Self::for_verification(then_implies_iff),
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailIffImpliesThen {
                        iff_implies_then, ..
                    },
                ) => Self::for_verification(iff_implies_then),
                VerifyForallFactWithIffResult::Success(_) => {
                    unreachable!("diagnostics require a failure")
                }
            },
            VerifyFactResult::NotForall(r) => match r.as_ref() {
                VerifyNotForallFactResult::Failed(
                    VerifyNotForallFactFailed::UnsupportedNegation { .. },
                ) => Self::Unsupported,
                VerifyNotForallFactResult::Failed(
                    VerifyNotForallFactFailed::FailToProveDerivedExist {
                        prove_derived_exist,
                        ..
                    },
                ) => Self::for_verification(prove_derived_exist),
                VerifyNotForallFactResult::Success(_) => {
                    unreachable!("diagnostics require a failure")
                }
            },
            VerifyFactResult::AndFact(r) => match r.as_ref() {
                VerifyAndFactResult::Failed(
                    VerifyAndFactFailed::FailToSearchProof {
                        failed_component, ..
                    }
                    | VerifyAndFactFailed::FailToVerifyWellDefined {
                        failed_component, ..
                    },
                ) => Self::for_verification(failed_component),
                VerifyAndFactResult::Success(_) => unreachable!("diagnostics require a failure"),
            },
            VerifyFactResult::ChainFact(r) => match r.as_ref() {
                VerifyChainFactResult::Failed(
                    VerifyChainFactFailed::FailToSearchProof {
                        failed_adjacent, ..
                    }
                    | VerifyChainFactFailed::FailToVerifyWellDefined {
                        failed_adjacent, ..
                    },
                ) => Self::for_verification(failed_adjacent),
                VerifyChainFactResult::Success(_) => unreachable!("diagnostics require a failure"),
            },
            VerifyFactResult::Equality(r) => match r.as_ref() {
                VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
                    fact,
                    ..
                }) => Self::for_calculation(&[&fact.left, &fact.right]),
                _ => Self::ProofSearch,
            },
            VerifyFactResult::AtomicExceptEquality(r) => match r.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Failed(
                    VerifyAtomicExceptEqualityFactFailed::FailToSearchProof { fact, .. },
                ) => Self::for_calculation(&crate::ast::fact::atomic_fact_args_ref(fact)),
                _ => Self::ProofSearch,
            },
            VerifyFactResult::OrFact(_) | VerifyFactResult::ExistShapedFact(_) => Self::ProofSearch,
        }
    }

    fn for_calculation(objects: &[&Obj]) -> Self {
        if objects
            .iter()
            .any(|object| crate::rational_expression::closed_decimal_budget_exceeded(object))
        {
            Self::ExactDecimalBudget
        } else {
            Self::ProofSearch
        }
    }

    pub(super) fn for_obligation(result: &VerifyFactResult, purpose: Self) -> Self {
        match Self::for_verification(result) {
            Self::ProofSearch => purpose,
            kind => kind,
        }
    }
}
