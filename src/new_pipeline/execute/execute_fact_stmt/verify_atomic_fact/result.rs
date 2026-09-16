use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByKnownRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    AtomicExceptEqualityFactSearchProofByBuiltinRule, AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
    AtomicExceptEqualityFactSearchProofByKnownRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_well_defined::AtomicFactWellDefinedProof;
use crate::new_pipeline::runtime::runtime_ids::FactId;

pub struct VerifyEqualityResult {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: EqualFactSearchedProof,
}

// Mirrors search_equal_fact_proof stage order.
// Rewrite stages replace legacy opaque resolve_obj: rewrites must be
// explicit certificates (see ByBuiltinRewrite / ByKnownRewrite).
pub enum EqualFactSearchedProof {
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(SearchProofByKnownForallFact),
    ByBuiltinRewrite(EqualitySearchProofByBuiltinRewrite),
    ByKnownRewrite(EqualitySearchProofByKnownRewrite),
}

// Oriented cite chain from goal.left to goal.right over generating equality
// edges only. Each entry: (from, to, cited_equal_fact_id). Empty <=> reflexive.
// FactIds must come from KnownEqualityMemory.generating_edges, never from a
// class-id handle alone.
pub struct EqualFactSearchedProofByKnownEquality {
    pub path: Vec<(Obj, Obj, FactId)>,
}

pub struct VerifyAtomicExceptEqualityFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: AtomicExceptEqualityFactSearchedProof,
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
    // One justification per argument: EqualIr when ObjIR already matches,
    // otherwise a generating-edge path through known_equality.
    pub why_parameters_of_known_fact_are_equal_to_givens:
        Vec<WhyKnownAtomicParameterMatchesGiven>,
}

// Why a stored known-atomic argument matches the goal argument.
pub enum WhyKnownAtomicParameterMatchesGiven {
    EqualIr,
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
}

pub struct AtomicExceptEqualityFactSearchProofByDefinition {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Shared known-forall application certificate (equality and non-equality).
// `cite` is the same handle as in KnownForallConclusionMemory.
pub struct SearchProofByKnownForallFact {
    pub cite: crate::new_pipeline::exec_env::ForallConclusionCite,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
