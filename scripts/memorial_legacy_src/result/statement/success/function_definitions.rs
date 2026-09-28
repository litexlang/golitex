//! Successful function definition and induction-check outcomes.

use crate::prelude::*;
use std::rc::Rc;

pub struct SuccessHaveFnEqualStmtResult {
    pub statement: HaveFnEqualStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyFunctionDefinitionResult>,
}

pub struct SuccessHaveFnEqualCaseByCaseStmtResult {
    pub statement: HaveFnEqualCaseByCaseStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyCaseFunctionDefinitionResult>,
}

pub struct SuccessHaveFnByInducStmtResult {
    pub statement: HaveFnByInducStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyHaveFnByInducResult>,
}

pub struct SuccessVerifyHaveFnByInducResult {
    pub well_definedness_run_in_local_env: SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult,
    pub verification_run_in_local_env: SuccessVerifyHaveFnByInducLocalEnvResult,
}

pub struct SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult {
    pub function_binding: SymbolBinding,
    pub function_set: FnSet,
    pub function_set_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub parameters_and_domain: SuccessVerifyHaveFnByInducParametersAndDomainResult,
    pub measure_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub lower_bound_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
}

pub struct SuccessVerifyHaveFnByInducParametersAndDomainResult {
    pub parameter_groups: Vec<SuccessVerifyHaveFnByInducParameterGroupResult>,
    pub domain_facts: Vec<SuccessVerifyHaveFnByInducDomainFactResult>,
}

pub struct SuccessVerifyHaveFnByInducParameterGroupResult {
    pub group_index: usize,
    pub definition: SetBoundParameterGroup,
    pub infers: SuccessInferResult,
}

pub struct SuccessVerifyHaveFnByInducDomainFactResult {
    pub domain_index: usize,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyHaveFnByInducLocalEnvResult {
    pub parameters_and_domain: SuccessVerifyHaveFnByInducParametersAndDomainResult,
    pub measure: SuccessVerifyHaveFnByInducMeasureResult,
    pub recursive_function: SuccessVerifyHaveFnByInducRecursiveFunctionResult,
    pub cases: SuccessVerifyHaveFnByInducCaseListResult,
}

pub struct SuccessVerifyHaveFnByInducMeasureResult {
    pub measure_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub lower_bound_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub measure_integer_check: Box<VerifyFactResult>,
    pub lower_bound_integer_check: Box<VerifyFactResult>,
    pub lower_bound_check: Box<VerifyFactResult>,
}

pub struct SuccessVerifyHaveFnByInducRecursiveFunctionResult {
    pub function_set: FnSet,
    pub membership_store: SuccessStoreFactResult,
}

pub struct SuccessVerifyHaveFnByInducCaseListResult {
    pub coverage_fact: Fact,
    pub coverage_check: Box<VerifyFactResult>,
    pub mutual_exclusions: Vec<SuccessVerifyCaseDisjointnessResult>,
    pub cases: Vec<SuccessVerifyHaveFnByInducCaseResult>,
}

pub struct SuccessVerifyHaveFnByInducCaseResult {
    pub case_index: usize,
    pub case_fact: Fact,
    pub assumption_store: SuccessStoreFactResult,
    pub body: SuccessVerifyHaveFnByInducCaseBodyResult,
}

pub enum SuccessVerifyHaveFnByInducCaseBodyResult {
    EqualTo(Box<SuccessVerifyHaveFnByInducEqualToResult>),
    NestedCases(Box<SuccessVerifyHaveFnByInducCaseListResult>),
}

pub struct SuccessVerifyHaveFnByInducEqualToResult {
    pub value: Obj,
    pub well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub return_membership_fact: AtomicFact,
    pub return_membership_check: Box<VerifyFactResult>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaseDisjointnessOrientation {
    LeftImpliesNotRight,
    RightImpliesNotLeft,
}

/// The one successful orientation selected while checking that two case
/// conditions cannot hold together. Failed search attempts are not successful
/// proof evidence and are deliberately absent.
pub struct SuccessVerifyCaseDisjointnessResult {
    pub left_case_index: usize,
    pub right_case_index: usize,
    pub orientation: CaseDisjointnessOrientation,
    pub assumed_case: Fact,
    pub assumption_store: SuccessStoreFactResult,
    pub contradicted_atom: AtomicFact,
    pub negated_atom: AtomicFact,
    pub negated_atom_check: Box<VerifyFactResult>,
}
