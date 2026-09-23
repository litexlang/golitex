use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    AtomicExceptEqualityFactSearchProofByBuiltinRule, AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
    AtomicExceptEqualityFactSearchProofByKnownRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::FactId;

pub enum VerifyAtomicExceptEqualityFactResult {
    Success(VerifyAtomicExceptEqualityFactSuccess),
    Failed(VerifyAtomicExceptEqualityFactFailed),
}

pub struct VerifyAtomicExceptEqualityFactSuccess {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: AtomicExceptEqualityFactSearchedProof,
}

pub enum VerifyAtomicExceptEqualityFactFailed {
    FailToVerifyWellDefined(FailToVerifyAtomicFactWellDefinedResult),
    FailToSearchProof {
        fact: AtomicFact,
        well_defined_proof: AtomicFactWellDefinedProof,
    },
}

impl VerifyAtomicExceptEqualityFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// Mirrors search_atomic_except_equality_fact_proof stage order.
pub enum AtomicExceptEqualityFactSearchedProof {
    ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(AtomicExceptEqualityFactSearchProofByKnownAtomicFact),
    ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy),
    ByDefinition(AtomicExceptEqualityFactSearchProofByDefinition),
    ByKnownForallFact(SearchProofByKnownForallFact),
    ByBuiltinRewrite(AtomicExceptEqualityFactSearchProofByBuiltinRewrite),
    ByKnownRewrite(AtomicExceptEqualityFactSearchProofByKnownRewrite),
}

pub struct AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    // Per argument: prove known_arg = goal_arg via equality search
    // (forall/rewrite off). Same ObjIR usually lands on ByEqualIr.
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<EqualFactSearchedProof>,
}

// By-definition fork: user `prop` vs builtin predicate definitions.
pub enum AtomicExceptEqualityFactSearchProofByDefinition {
    UserDefinedProp(UserDefinedPropDefinitionProof),
    BuiltinProp(BuiltinPropDefinitionProof),
}

pub struct UserDefinedPropDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// One builtin predicate definition ↔ one dedicated evidence struct.
pub enum BuiltinPropDefinitionProof {
    Subset(BuiltinSubsetDefinitionProof),
    Superset(BuiltinSupersetDefinitionProof),
    ProperSubset(BuiltinProperSubsetDefinitionProof),
    ProperSuperset(BuiltinProperSupersetDefinitionProof),
    Injective(BuiltinInjectiveDefinitionProof),
    Surjective(BuiltinSurjectiveDefinitionProof),
    Bijective(BuiltinBijectiveDefinitionProof),
    IsChoiceFunctionFor(BuiltinIsChoiceFunctionForDefinitionProof),
    Prime(BuiltinPrimeDefinitionProof),
    Coprime(BuiltinCoprimeDefinitionProof),
    Dvd(BuiltinDvdDefinitionProof),
}

pub struct BuiltinSubsetDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinSupersetDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinProperSubsetDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinProperSupersetDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinInjectiveDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinSurjectiveDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinBijectiveDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinIsChoiceFunctionForDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinPrimeDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinCoprimeDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct BuiltinDvdDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub fn atomic_except_equality_fact_result_from_wd_fail(
    reason: FailToVerifyAtomicFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::AtomicExceptEquality(Box::new(
        VerifyAtomicExceptEqualityFactResult::Failed(
            VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(reason),
        ),
    ))
}

pub fn atomic_except_equality_fact_result_from_search_fail(
    fact: &AtomicFact,
    well_defined_proof: AtomicFactWellDefinedProof,
) -> VerifyFactResult {
    VerifyFactResult::AtomicExceptEquality(Box::new(
        VerifyAtomicExceptEqualityFactResult::Failed(
            VerifyAtomicExceptEqualityFactFailed::FailToSearchProof {
                fact: fact.clone(),
                well_defined_proof,
            },
        ),
    ))
}

pub fn atomic_except_equality_fact_result_from_success(
    fact: &AtomicFact,
    well_defined_proof: AtomicFactWellDefinedProof,
    searched_proof: AtomicExceptEqualityFactSearchedProof,
) -> VerifyFactResult {
    VerifyFactResult::AtomicExceptEquality(Box::new(
        VerifyAtomicExceptEqualityFactResult::Success(VerifyAtomicExceptEqualityFactSuccess {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        }),
    ))
}
