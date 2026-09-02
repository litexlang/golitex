//! Builtin and Litex theorem application outcomes.

use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinTheoremRequirementRole {
    FirstArgumentIsSet,
    SecondArgumentIsFiniteSet,
    FirstArgumentSubsetOfSecond,
    ArgumentIsFiniteSet,
    ArgumentBelongsToRationals,
    FunctionSignatureMatchesTarget,
    SetBuilderDefiningFacts,
    DefinedSetMembership,
    StructCarrierFacts,
    CartesianCoordinates,
    GeneralCartesianPointwiseMembership,
    GeneralCartesianFamilyNonempty,
    GeneralCartesianPointwiseNonempty,
    IntegerSumPointwiseOrder,
    FiniteSetSumPointwiseOrder,
    FiniteSetSummandNonnegative,
    TupleCoordinatesEqual,
    FiniteSetSumSubstitution,
    BijectiveFiniteSetEnumerations,
    ArgumentSetSubsetOfReals,
    ArgumentSetIsNonempty,
    SuppliedUpperBoundBelongsToReals,
    SuppliedValueBoundsEverySetMember,
    CandidateBelongsToReals,
    CandidateIsRealLeastUpperBound,
    SuppliedLowerBoundBelongsToReals,
    SuppliedValueIsLowerBoundForEverySetMember,
    CandidateIsRealGreatestLowerBound,
    ArgumentBelongsToReals,
    ArgumentIsMemberOfSet,
    LeftArgumentBelongsToReals,
    RightArgumentBelongsToReals,
    RealArgumentsStrictlyOrdered,
}

impl BuiltinTheoremRequirementRole {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FirstArgumentIsSet => "the first argument is a set",
            Self::SecondArgumentIsFiniteSet => "the second argument is a finite set",
            Self::FirstArgumentSubsetOfSecond => "the first argument is a subset of the second",
            Self::ArgumentIsFiniteSet => "the argument is a finite set",
            Self::ArgumentBelongsToRationals => "the argument belongs to Q",
            Self::FunctionSignatureMatchesTarget => {
                "function signature matches the target function set"
            }
            Self::SetBuilderDefiningFacts => {
                "element satisfies the set-builder base and defining facts"
            }
            Self::DefinedSetMembership => {
                "one set-valued definition unfolds and its membership obligations hold"
            }
            Self::StructCarrierFacts => "element satisfies the struct carrier and equivalent facts",
            Self::CartesianCoordinates => "tuple/cart dimensions and coordinate memberships hold",
            Self::GeneralCartesianPointwiseMembership => {
                "function carrier and pointwise general-cart membership hold"
            }
            Self::GeneralCartesianFamilyNonempty => "every member of the family set is nonempty",
            Self::GeneralCartesianPointwiseNonempty => "every indexed factor is nonempty",
            Self::IntegerSumPointwiseOrder => {
                "summation bounds agree and summands are pointwise ordered"
            }
            Self::FiniteSetSumPointwiseOrder => {
                "finite index sets agree and summands are pointwise ordered"
            }
            Self::FiniteSetSummandNonnegative => {
                "term belongs to the index set and every summand is nonnegative"
            }
            Self::TupleCoordinatesEqual => {
                "tuple dimensions and all corresponding coordinates agree"
            }
            Self::FiniteSetSumSubstitution => {
                "summands agree pointwise on one index set, or by pullback along a bijection"
            }
            Self::BijectiveFiniteSetEnumerations => {
                "both summations enumerate the same finite set bijectively"
            }
            Self::ArgumentSetSubsetOfReals => "the argument set is a subset of R",
            Self::ArgumentSetIsNonempty => "the argument set is nonempty",
            Self::SuppliedUpperBoundBelongsToReals => "the supplied upper bound belongs to R",
            Self::SuppliedValueBoundsEverySetMember => {
                "every member of the argument set is at most the supplied value"
            }
            Self::CandidateBelongsToReals => "the extremum candidate belongs to R",
            Self::CandidateIsRealLeastUpperBound => {
                "the candidate carries a real least-upper-bound certificate"
            }
            Self::SuppliedLowerBoundBelongsToReals => "the supplied lower bound belongs to R",
            Self::SuppliedValueIsLowerBoundForEverySetMember => {
                "the supplied value is at most every member of the argument set"
            }
            Self::CandidateIsRealGreatestLowerBound => {
                "the candidate carries a real greatest-lower-bound certificate"
            }
            Self::ArgumentBelongsToReals => "the argument belongs to R",
            Self::ArgumentIsMemberOfSet => "the argument is a member of the set",
            Self::LeftArgumentBelongsToReals => "the left argument belongs to R",
            Self::RightArgumentBelongsToReals => "the right argument belongs to R",
            Self::RealArgumentsStrictlyOrdered => "the real arguments are strictly ordered",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinTheoremProvenance {
    AxiomOfChoice,
}

impl BuiltinTheoremProvenance {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AxiomOfChoice => "axiom_of_choice",
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifyLitexTheoremApplicationResult {
    /// Exact stored identity of the source theorem/axiom being instantiated.
    pub source_fact_id: Option<FactId>,
    pub mode: SuccessVerifyLitexTheoremApplicationMode,
}

#[derive(Debug)]
pub enum SuccessVerifyLitexTheoremApplicationMode {
    ForallInstantiation {
        argument_verification: Option<Box<SuccessVerifyArgsSatisfyParamDefResult>>,
        domain_facts: Vec<Fact>,
        domain_checks: Vec<VerifyFactResult>,
    },
    DirectFactCitation,
}

#[derive(Debug)]
pub struct SuccessVerifyBuiltinTheoremApplicationResult {
    pub theorem_id: BuiltinTheoremId,
    pub requirement_facts: Vec<Fact>,
    pub requirement_roles: Vec<BuiltinTheoremRequirementRole>,
    pub requirement_checks: Vec<VerifyFactResult>,
    /// Dedicated builtin theorems whose conclusion differs from every
    /// requirement retain the exact conclusion WD tree here.
    pub conclusion_well_definedness: Option<WellDefinedFactResult>,
    pub provenance: Option<BuiltinTheoremProvenance>,
}

#[derive(Debug)]
pub enum SuccessVerifyTheoremApplicationSourceResult {
    Litex(SuccessVerifyLitexTheoremApplicationResult),
    Builtin(SuccessVerifyBuiltinTheoremApplicationResult),
}

pub struct SuccessVerifyTheoremApplicationResult {
    pub theorem: String,
    /// Exact source objects, not display strings. Consumers compare these by
    /// structural object identity before compiling an application.
    pub arguments: Vec<Obj>,
    /// Exact instantiated direct conclusions returned by theorem execution.
    pub direct_conclusions: Vec<Fact>,
    pub source: SuccessVerifyTheoremApplicationSourceResult,
}

impl fmt::Debug for SuccessVerifyTheoremApplicationResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyTheoremApplicationResult")
            .field("theorem", &self.theorem)
            .field(
                "arguments",
                &self
                    .arguments
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("direct_conclusions", &self.direct_conclusions)
            .field("source", &self.source)
            .finish()
    }
}

/// Successful `by thm ... => fact` execution keeps the temporary theorem
/// application as a complete child statement Result. Its conclusion stores
/// own the exact local FactIds cited by `selected_fact_check`; only the
/// selected fact's outer store belongs to the parent statement.
pub struct SuccessVerifyByTheoremSelectionResult {
    pub temporary_application: Box<StmtResult>,
    pub selected_fact: AtomicFact,
    pub selected_fact_check: Box<VerifyFactResult>,
}

impl fmt::Debug for SuccessVerifyByTheoremSelectionResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyByTheoremSelectionResult")
            .field("temporary_application", &self.temporary_application)
            .field("selected_fact", &self.selected_fact.to_string())
            .field("selected_fact_check", &self.selected_fact_check)
            .finish()
    }
}

impl SuccessVerifyTheoremApplicationResult {
    pub fn new_forall_instantiation(
        theorem: String,
        source_fact_id: Option<FactId>,
        arguments: Vec<Obj>,
        domain_facts: Vec<Fact>,
        direct_conclusions: Vec<Fact>,
        argument_verification: Option<SuccessVerifyArgsSatisfyParamDefResult>,
        domain_checks: Vec<VerifyFactResult>,
    ) -> Self {
        SuccessVerifyTheoremApplicationResult {
            theorem,
            arguments,
            direct_conclusions,
            source: SuccessVerifyTheoremApplicationSourceResult::Litex(
                SuccessVerifyLitexTheoremApplicationResult {
                    source_fact_id,
                    mode: SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation {
                        argument_verification: argument_verification.map(Box::new),
                        domain_facts,
                        domain_checks,
                    },
                },
            ),
        }
    }

    pub fn new_direct_fact_citation(
        theorem: String,
        source_fact_id: FactId,
        direct_conclusion: Fact,
    ) -> Self {
        SuccessVerifyTheoremApplicationResult {
            theorem,
            arguments: Vec::new(),
            direct_conclusions: vec![direct_conclusion],
            source: SuccessVerifyTheoremApplicationSourceResult::Litex(
                SuccessVerifyLitexTheoremApplicationResult {
                    source_fact_id: Some(source_fact_id),
                    mode: SuccessVerifyLitexTheoremApplicationMode::DirectFactCitation,
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
        requirement_checks: Vec<VerifyFactResult>,
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
        requirement_checks: Vec<VerifyFactResult>,
        conclusion_well_definedness: WellDefinedFactResult,
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
        selected_fact_check: VerifyFactResult,
    ) -> Self {
        Self {
            temporary_application: Box::new(temporary_application),
            selected_fact,
            selected_fact_check: Box::new(selected_fact_check),
        }
    }
}
