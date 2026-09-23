//! Statement execution results for new_pipeline.
//!
//! Top level dispatches by stmt kind only. Soft Success|Failed lives inside
//! each leaf `*Result`. Session-stopping bugs stay in `RuntimeResult::Err`.
//!
//! Shared ParamType-indexed shells live here so `have` / `witness` / later
//! args:type checks reuse one shape.
//!
//! Leaf Success payloads that open a local proof / binder / instantiation
//! scope often carry `local_env: Box<ExecEnv>`: the taken FactId/WdId → entity
//! table for that scope. Resolve id cites through it; do not scrape it to
//! rediscover the proof route (see `execute_by_stmt/result.rs`).

use crate::new_pipeline::execute::execute_by_stmt::ExecByStmtResult;
use crate::new_pipeline::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::new_pipeline::execute::execute_def_abstract_prop_stmt::ExecDefAbstractPropStmtSuccessResult;
use crate::new_pipeline::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::new_pipeline::execute::execute_def_struct_stmt::ExecDefStructStmtResult;
use crate::new_pipeline::execute::execute_def_template_stmt::ExecDefTemplateStmtResult;
use crate::new_pipeline::execute::execute_def_thm_stmt::ExecDefThmStmtResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, VerifyFactResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_have_fn_by_forall_exist_unique_stmt::ExecHaveFnByForallExistUniqueStmtResult;
use crate::new_pipeline::execute::execute_have_fn_by_induc_stmt::ExecHaveFnByInducStmtResult;
use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::ExecHaveFnEqualCaseByCaseStmtResult;
use crate::new_pipeline::execute::execute_have_fn_equal_stmt::ExecHaveFnEqualStmtResult;
use crate::new_pipeline::execute::execute_have_obj_by_exist_facts_stmt::ExecHaveObjByExistFactsStmtResult;
use crate::new_pipeline::execute::execute_have_by_fn_preimage_stmt::ExecHaveByFnPreimageStmtResult;
use crate::new_pipeline::execute::execute_have_by_replacement_axiom_stmt::ExecHaveByReplacementAxiomStmtResult;
use crate::new_pipeline::execute::execute_obtain_obj_from_atomic_fact_stmt::ExecObtainObjFromAtomicFactStmtResult;
use crate::new_pipeline::execute::execute_obtain_obj_from_exist_fact_stmt::ExecObtainObjFromExistFactStmtResult;
use crate::new_pipeline::execute::execute_have_obj_equal_stmt::ExecHaveObjEqualStmtResult;
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::ExecHaveObjInNonemptySetStmtResult;
use crate::new_pipeline::execute::execute_let_stmt::ExecLetObjStmtResult;
use crate::new_pipeline::execute::execute_release_struct_def_stmt::ExecReleaseStructDefStmtResult;
use crate::new_pipeline::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult;
use crate::new_pipeline::execute::execute_unsafe_stmt::ExecUnsafeStmtResult;
use crate::new_pipeline::execute::execute_witness_stmt::ExecWitnessStmtResult;

// WD of one parameter-type annotation (not a Fact).
// Example: `x R` → Obj(WD of `R`); bare `set` → Set.
pub enum ParamTypeWellDefinedProof {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyObjWellDefinedResult),
}

// Fact obligation indexed by ParamType.
// Example: `have x S` nonempty check; `witness … from w` with `w $in S`.
pub enum ParamTypeFactCheckResult {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyFactResult),
}

impl ParamTypeWellDefinedProof {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Obj(wd) => wd.is_failed(),
            Self::Set | Self::NonemptySet | Self::FiniteSet => false,
        }
    }
}

impl ParamTypeFactCheckResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Obj(r) => r.is_failed(),
            Self::Set | Self::NonemptySet | Self::FiniteSet => false,
        }
    }
}

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
    Witness(ExecWitnessStmtResult),
    Unsafe(ExecUnsafeStmtResult),
    By(ExecByStmtResult),
    ReleaseThm(ExecReleaseThmStmtResult),
    ReleaseStructDef(ExecReleaseStructDefStmtResult),
    ReleaseObjDef(ExecReleaseObjDefStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult),
    HaveObjEqual(ExecHaveObjEqualStmtResult),
    HaveObjByExistFacts(ExecHaveObjByExistFactsStmtResult),
    ObtainObjFromExistFact(ExecObtainObjFromExistFactStmtResult),
    ObtainObjFromAtomicFact(ExecObtainObjFromAtomicFactStmtResult),
    HaveByFnPreimage(ExecHaveByFnPreimageStmtResult),
    HaveByReplacementAxiom(ExecHaveByReplacementAxiomStmtResult),
    HaveFnEqual(ExecHaveFnEqualStmtResult),
    HaveFnEqualCaseByCase(ExecHaveFnEqualCaseByCaseStmtResult),
    HaveFnByForallExistUnique(ExecHaveFnByForallExistUniqueStmtResult),
    HaveFnByInduc(ExecHaveFnByInducStmtResult),
    DefProp(ExecDefPropStmtResult),
    DefAbstractProp(ExecDefAbstractPropStmtSuccessResult),
    DefStruct(ExecDefStructStmtResult),
    DefTemplate(ExecDefTemplateStmtResult),
    DefThm(ExecDefThmStmtResult),
}

impl ExecStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Fact(r) => r.is_failed(),
            Self::Definition(r) => r.is_failed(),
            Self::Witness(r) => r.is_failed(),
            Self::Unsafe(r) => r.is_failed(),
            Self::By(r) => r.is_failed(),
            Self::ReleaseThm(r) => r.is_failed(),
            Self::ReleaseStructDef(r) => r.is_failed(),
            Self::ReleaseObjDef(r) => r.is_failed(),
        }
    }
}

impl ExecDefinitionStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::LetObj(r) => r.is_failed(),
            Self::HaveObjInNonemptySet(r) => r.is_failed(),
            Self::HaveObjEqual(r) => r.is_failed(),
            Self::HaveObjByExistFacts(r) => r.is_failed(),
            Self::ObtainObjFromExistFact(r) => r.is_failed(),
            Self::ObtainObjFromAtomicFact(r) => r.is_failed(),
            Self::HaveByFnPreimage(r) => r.is_failed(),
            Self::HaveByReplacementAxiom(r) => r.is_failed(),
            Self::HaveFnEqual(r) => r.is_failed(),
            Self::HaveFnEqualCaseByCase(r) => r.is_failed(),
            Self::HaveFnByForallExistUnique(r) => r.is_failed(),
            Self::HaveFnByInduc(r) => r.is_failed(),
            Self::DefProp(r) => r.is_failed(),
            Self::DefAbstractProp(_) => false,
            Self::DefStruct(r) => r.is_failed(),
            Self::DefTemplate(r) => r.is_failed(),
            Self::DefThm(r) => r.is_failed(),
        }
    }
}
