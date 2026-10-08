//! `have fn f(...) R by induc measure from lower:` — inductive function definition.
//!
//! Stages: FnSet WD → introduce params → measure/lower in Z + measure >= lower →
//! register restricted recursive f → coverage/disjoint/returns →
//! parent keeps HaveFnByInduc + store piecewise case foralls.
//!
//! Example:
//! ```text
//! have fn countdown(n N) N by induc n from 0:
//!     case n = 0: 0
//!     case n >= 1: countdown(n - 1)
//! ```

use std::collections::HashMap;

use crate::ast::fact::{
    and_chain_as_fact, negate_atomic_fact, AndChainAtomicFact, AndFact, AtomicFact, Fact,
    GreaterEqualFact, InFact, LessFact, OrFact, QuantifierFreeFact,
};
use crate::ast::obj::{FnSet, FunctionSpace, IdentifierObj, Obj, StandardSet};
use crate::ast::param::{ParamType, SetBoundParameterGroup, TypedParameterList};
use crate::ast::stmt::{
    FnSetClause, HaveFnByInducCase, HaveFnByInducCaseBody, HaveFnByInducStmt,
    HaveFnEqualCaseByCaseStmt,
};
use crate::exec_env::{ExecEnv, StoredIdentifierDefinition};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_fn_equal_case_by_case_stmt::StoreHaveFnCaseByCaseAndInferResult;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;
use std::rc::Rc;

pub enum ExecHaveFnByInducStmtFailed {
    EmptyCases,
    FnSetWellDefined(VerifyObjWellDefinedResult),
    MeasureWellDefined(VerifyObjWellDefinedResult),
    LowerBoundWellDefined(VerifyObjWellDefinedResult),
    MeasureNotInteger(VerifyFactResult),
    LowerBoundNotInteger(VerifyFactResult),
    MeasureBelowLower(VerifyFactResult),
    Coverage(VerifyFactResult),
    Disjoint {
        i: usize,
        j: usize,
    },
    CaseBodyWellDefined(usize, VerifyObjWellDefinedResult),
    CaseBodyInRetSet(usize, VerifyFactResult),
    NestedCase {
        index: usize,
        failed: Box<ExecHaveFnByInducStmtFailed>,
    },
    Shape(String),
}

pub struct ExecHaveFnByInducStmtSuccessResult {
    pub statement: HaveFnByInducStmt,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub measure_in_z: VerifyFactResult,
    pub lower_in_z: VerifyFactResult,
    pub measure_ge_lower: VerifyFactResult,
    pub case_checks: InducCaseListSuccess,
    pub store_and_infer_result: StoreHaveFnCaseByCaseAndInferResult,
    pub local_env: Box<ExecEnv>,
}

pub struct InducCaseListSuccess {
    pub coverage: VerifyFactResult,
    pub disjoint: Vec<InducCasesDisjointSuccess>,
    pub cases: Vec<InducCaseSuccess>,
}

pub struct InducCasesDisjointSuccess {
    pub i: usize,
    pub j: usize,
    pub assumption_stored: StoreFactAndInferResult,
    pub negated_component: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub struct InducCaseSuccess {
    pub assumption_stored: StoreFactAndInferResult,
    pub body: InducCaseBodySuccess,
    pub local_env: Box<ExecEnv>,
}

pub enum InducCaseBodySuccess {
    EqualTo {
        well_defined: VerifyObjWellDefinedResult,
        in_ret_set: VerifyFactResult,
    },
    NestedCases(InducCaseListSuccess),
}

pub enum ExecHaveFnByInducStmtResult {
    Success(ExecHaveFnByInducStmtSuccessResult),
    Failed(ExecHaveFnByInducStmtFailed),
}

impl ExecHaveFnByInducStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    pub(super) fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> RuntimeResult<ExecHaveFnByInducStmtResult> {
        let verify_state = VerifyState::top_level();

        if stmt.cases.is_empty() {
            return Ok(ExecHaveFnByInducStmtResult::Failed(
                ExecHaveFnByInducStmtFailed::EmptyCases,
            ));
        }

        let fn_set = fn_set_from_clause(&stmt.fn_set_clause);
        let fn_set_well_defined = self.verify_obj_well_definedness(
            &Obj::FunctionSpace(FunctionSpace::FnSet(fn_set.clone())),
            verify_state.clone(),
        )?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnByInducStmtResult::Failed(
                ExecHaveFnByInducStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.introduce_fn_set_clause_binders(
                &stmt.fn_set_clause,
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;

            let measure_wd = rt.verify_obj_well_definedness(&stmt.measure, verify_state.clone())?;
            if measure_wd.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::MeasureWellDefined(
                    measure_wd,
                )));
            }
            let lower_wd =
                rt.verify_obj_well_definedness(&stmt.lower_bound, verify_state.clone())?;
            if lower_wd.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::LowerBoundWellDefined(
                    lower_wd,
                )));
            }

            let measure_in_z =
                rt.verify_in_z(&stmt.measure, &stmt.line_file, verify_state.clone())?;
            if measure_in_z.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::MeasureNotInteger(
                    measure_in_z,
                )));
            }
            let lower_in_z =
                rt.verify_in_z(&stmt.lower_bound, &stmt.line_file, verify_state.clone())?;
            if lower_in_z.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::LowerBoundNotInteger(
                    lower_in_z,
                )));
            }

            let ge = Fact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                left: stmt.measure.clone(),
                right: stmt.lower_bound.clone(),
                line_file: Some(stmt.line_file.clone()),
            }));
            let measure_ge_lower = rt.verify_fact(&ge, verify_state.clone())?;
            if measure_ge_lower.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::MeasureBelowLower(
                    measure_ge_lower,
                )));
            }

            if let Err(msg) = rt.register_restricted_recursive_fn(
                stmt,
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            ) {
                return Ok(Err(ExecHaveFnByInducStmtFailed::Shape(msg)));
            }

            let case_checks =
                match rt.verify_induc_case_list(stmt, &stmt.cases, verify_state.clone())? {
                    Ok(checks) => checks,
                    Err(failed) => return Ok(Err(failed)),
                };

            Ok(Ok((
                measure_in_z,
                lower_in_z,
                measure_ge_lower,
                case_checks,
            )))
        })?;

        let (measure_in_z, lower_in_z, measure_ge_lower, case_checks) = match inner {
            Ok(v) => v,
            Err(failed) => return Ok(ExecHaveFnByInducStmtResult::Failed(failed)),
        };

        let store_and_infer_result = match self.store_have_fn_by_induc_facts(
            stmt,
            &fn_set,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        ) {
            Ok(r) => r,
            Err(RuntimeError::InternalBug(msg)) if msg.starts_with("flatten induc:") => {
                return Ok(ExecHaveFnByInducStmtResult::Failed(
                    ExecHaveFnByInducStmtFailed::Shape(
                        msg.strip_prefix("flatten induc: ")
                            .unwrap_or(&msg)
                            .to_string(),
                    ),
                ));
            }
            Err(e) => return Err(e),
        };

        Ok(ExecHaveFnByInducStmtResult::Success(
            ExecHaveFnByInducStmtSuccessResult {
                statement: stmt.clone(),
                fn_set_well_defined,
                measure_in_z,
                lower_in_z,
                measure_ge_lower,
                case_checks,
                store_and_infer_result,
                local_env,
            },
        ))
    }

    // Parent definition identity is HaveFnByInduc; leaf case equations are still
    // stored as foralls (flatten only for those facts, not for the definition row).
    pub(crate) fn store_have_fn_by_induc_facts(
        &mut self,
        stmt: &HaveFnByInducStmt,
        fn_set: &FnSet,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<StoreHaveFnCaseByCaseAndInferResult> {
        if self.identifier_defined_in_stack(&stmt.name.name) {
            return Err(crate::runtime::RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            stmt.name.name.clone(),
            StoredIdentifierDefinition::HaveFnByInduc((
                stmt.name.name.clone(),
                Rc::new(stmt.clone()),
            )),
        );

        let flat = flatten_induc_to_case_by_case(self, stmt).map_err(|msg| {
            crate::runtime::RuntimeError::InternalBug(format!("flatten induc: {msg}"))
        })?;
        self.store_piecewise_fn_membership_and_case_foralls(&flat, fn_set, verify_state)
    }

    fn verify_in_z(
        &mut self,
        obj: &Obj,
        line_file: &crate::ast::line_file::SourceLine,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: Some(line_file.clone()),
        }));
        self.verify_fact(&fact, verify_state)
    }

    fn register_restricted_recursive_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> Result<(), String> {
        if self.identifier_defined_in_stack(&stmt.name.name) {
            // Already occupied at parse; ensure ExecEnv definition row exists.
        } else {
            self.top_exec_env_mut().definitions.identifiers.insert(
                stmt.name.name.clone(),
                StoredIdentifierDefinition::HaveFnByInduc((
                    stmt.name.name.clone(),
                    Rc::new(stmt.clone()),
                )),
            );
        }

        let (fresh_params, subst) = fresh_set_bound_params(self, &stmt.fn_set_clause)?;
        let mut dom_facts = Vec::new();
        for dom in &stmt.fn_set_clause.dom_facts {
            let inst = self
                .inst_quantifier_free_fact(dom, &subst)
                .map_err(|e| format!("recursive dom instantiate: {e}"))?;
            dom_facts.push(inst);
        }
        let generated_measure = self
            .inst_obj(&stmt.measure, &subst)
            .map_err(|e| format!("recursive measure instantiate: {e}"))?;
        let generated_ret = self
            .inst_obj(&stmt.fn_set_clause.ret_set, &subst)
            .map_err(|e| format!("recursive ret instantiate: {e}"))?;

        dom_facts.push(QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(
            LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: generated_measure.clone(),
                right: stmt.measure.clone(),
                line_file: Some(stmt.line_file.clone()),
            },
        )));
        dom_facts.push(QuantifierFreeFact::AtomicFact(
            AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: generated_measure,
                right: stmt.lower_bound.clone(),
                line_file: Some(stmt.line_file.clone()),
            }),
        ));

        let restricted = FnSet {
            set_bound_parameters: crate::ast::param::SetBoundParameterList {
                groups: fresh_params,
            },
            dom_facts,
            ret_set: Box::new(generated_ret),
        };
        // Only this declaration receives the induction hypothesis. Same-name
        // functions in other exports/modules retain their own signatures.
        let function_obj = Obj::Identifier(self.identifier_obj_for_stored_mention(&stmt.name));
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: function_obj,
            set: Obj::FunctionSpace(FunctionSpace::FnSet(restricted)),
            line_file: Some(stmt.line_file.clone()),
        }));
        let _ = self
            .store_fact_and_infer(&membership, verify_state)
            .map_err(|e| format!("recursive membership store: {e:?}"))?;
        Ok(())
    }

    // Every sibling list must be total and disjoint in its enclosing guard.
    // Example: under n = 0, cases n = 0 / n >= 0 overlap and cannot define a function.
    fn verify_induc_case_list(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<InducCaseListSuccess, ExecHaveFnByInducStmtFailed>> {
        if cases.is_empty() {
            return Ok(Err(ExecHaveFnByInducStmtFailed::EmptyCases));
        }
        let coverage_fact = Fact::OrFact(OrFact {
            fact_id: self.global_ids.allocate_fact_id(),
            facts: cases.iter().map(|case| case.case_fact.clone()).collect(),
            line_file: Some(stmt.line_file.clone()),
        });
        let coverage = self.verify_fact(&coverage_fact, verify_state.clone())?;
        if coverage.is_failed() {
            return Ok(Err(ExecHaveFnByInducStmtFailed::Coverage(coverage)));
        }
        let mut disjoint = Vec::new();
        for i in 0..cases.len() {
            for j in (i + 1)..cases.len() {
                let Some(proof) = self.have_fn_induc_case_pair_disjoint(
                    stmt,
                    &cases[i].case_fact,
                    &cases[j].case_fact,
                    i,
                    j,
                    verify_state.clone(),
                )?
                else {
                    return Ok(Err(ExecHaveFnByInducStmtFailed::Disjoint { i, j }));
                };
                disjoint.push(proof);
            }
        }
        let returns = match self.verify_induc_case_list_returns(stmt, cases, verify_state)? {
            Ok(returns) => returns,
            Err(failed) => return Ok(Err(failed)),
        };
        Ok(Ok(InducCaseListSuccess {
            coverage,
            disjoint,
            cases: returns,
        }))
    }

    fn have_fn_induc_case_pair_disjoint(
        &mut self,
        stmt: &HaveFnByInducStmt,
        left: &AndChainAtomicFact,
        right: &AndChainAtomicFact,
        i: usize,
        j: usize,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InducCasesDisjointSuccess>> {
        if let Some(proof) =
            self.induc_case_implies_not_other(stmt, left, right, i, j, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        self.induc_case_implies_not_other(stmt, right, left, i, j, verify_state)
    }

    // Nested under the outer induc local that already introduced binders.
    // Do not re-introduce: `identifier_defined_in_stack` is name-based and
    // would InternalBug on the same param names.
    fn induc_case_implies_not_other(
        &mut self,
        _stmt: &HaveFnByInducStmt,
        assumed: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
        i: usize,
        j: usize,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InducCasesDisjointSuccess>> {
        let (proof, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let assumption_stored =
                rt.store_fact_and_infer(&and_chain_as_fact(assumed), verify_state)?;
            for atom in flatten_and_chain_atoms(rt, other)? {
                let Some(negated) = negate_atomic_fact(&atom, rt.global_ids.allocate_fact_id())
                else {
                    continue;
                };
                let checked = rt.verify_fact(&Fact::AtomicFact(negated), verify_state.clone())?;
                if !checked.is_failed() {
                    return Ok(Some((assumption_stored, checked)));
                }
            }
            Ok(None)
        })?;
        Ok(proof.map(
            |(assumption_stored, negated_component)| InducCasesDisjointSuccess {
                i,
                j,
                assumption_stored,
                negated_component,
                local_env,
            },
        ))
    }

    fn verify_induc_case_list_returns(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<InducCaseSuccess>, ExecHaveFnByInducStmtFailed>> {
        let mut returns = Vec::new();
        for (case_index, case) in cases.iter().enumerate() {
            let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
                let assumption_stored =
                    rt.store_fact_and_infer(&and_chain_as_fact(&case.case_fact), verify_state)?;
                let body = match &case.body {
                    HaveFnByInducCaseBody::EqualTo(equal_to) => {
                        // Binders already live on the outer induc local; only
                        // assume this case in a nested env.
                        let body_wd =
                            rt.verify_obj_well_definedness(equal_to, verify_state.clone())?;
                        if body_wd.is_failed() {
                            return Ok(Err(ExecHaveFnByInducStmtFailed::CaseBodyWellDefined(
                                case_index, body_wd,
                            )));
                        }
                        let in_fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
                            fact_id: rt.global_ids.allocate_fact_id(),
                            element: equal_to.clone(),
                            set: stmt.fn_set_clause.ret_set.clone(),
                            line_file: Some(stmt.line_file.clone()),
                        }));
                        let in_ret = rt.verify_fact(&in_fact, verify_state.clone())?;
                        if in_ret.is_failed() {
                            return Ok(Err(ExecHaveFnByInducStmtFailed::CaseBodyInRetSet(
                                case_index, in_ret,
                            )));
                        }
                        InducCaseBodySuccess::EqualTo {
                            well_defined: body_wd,
                            in_ret_set: in_ret,
                        }
                    }
                    HaveFnByInducCaseBody::NestedCases(nested) => {
                        match rt.verify_induc_case_list(stmt, nested, verify_state.clone())? {
                            Ok(checks) => InducCaseBodySuccess::NestedCases(checks),
                            Err(failed) => {
                                return Ok(Err(ExecHaveFnByInducStmtFailed::NestedCase {
                                    index: case_index,
                                    failed: Box::new(failed),
                                }))
                            }
                        }
                    }
                };
                Ok(Ok((assumption_stored, body)))
            })?;
            match inner {
                Ok((assumption_stored, body)) => returns.push(InducCaseSuccess {
                    assumption_stored,
                    body,
                    local_env,
                }),
                Err(failed) => return Ok(Err(failed)),
            }
        }
        Ok(Ok(returns))
    }
}

fn fn_set_from_clause(clause: &FnSetClause) -> FnSet {
    FnSet {
        set_bound_parameters: clause.set_bound_parameters.clone(),
        dom_facts: clause.dom_facts.clone(),
        ret_set: Box::new(clause.ret_set.clone()),
    }
}

fn fresh_set_bound_params(
    runtime: &mut Runtime,
    clause: &FnSetClause,
) -> Result<(Vec<SetBoundParameterGroup>, HashMap<IdentifierId, Obj>), String> {
    let mut subst = HashMap::new();
    let mut groups = Vec::new();
    for group in &clause.set_bound_parameters.groups {
        let mut params = Vec::new();
        for p in &group.params {
            let fresh = runtime.fresh_internal_param();
            subst.insert(
                p.id,
                Obj::Identifier(IdentifierObj::from_bound_name(&fresh)),
            );
            params.push(fresh);
        }
        let param_type = runtime
            .inst_obj(group.param_type.as_ref(), &subst)
            .map_err(|e| format!("fresh param type: {e}"))?;
        groups.push(SetBoundParameterGroup {
            params,
            param_type: Box::new(param_type),
        });
    }
    Ok((groups, subst))
}

pub(crate) fn flatten_induc_to_case_by_case(
    runtime: &mut Runtime,
    stmt: &HaveFnByInducStmt,
) -> Result<HaveFnEqualCaseByCaseStmt, String> {
    let mut cases = Vec::new();
    let mut equal_tos = Vec::new();
    flatten_case_list(
        runtime,
        &stmt.cases,
        None,
        &mut cases,
        &mut equal_tos,
        &stmt.line_file,
    )?;
    Ok(HaveFnEqualCaseByCaseStmt {
        name: stmt.name.clone(),
        fn_set_clause: stmt.fn_set_clause.clone(),
        cases,
        equal_tos,
        line_file: stmt.line_file.clone(),
    })
}

fn flatten_case_list(
    runtime: &mut Runtime,
    source: &[HaveFnByInducCase],
    prefix: Option<AndChainAtomicFact>,
    cases: &mut Vec<AndChainAtomicFact>,
    equal_tos: &mut Vec<Obj>,
    line_file: &crate::ast::line_file::SourceLine,
) -> Result<(), String> {
    for c in source {
        let merged = match &prefix {
            Some(p) => merge_and_chains(runtime, p, &c.case_fact, line_file)?,
            None => c.case_fact.clone(),
        };
        match &c.body {
            HaveFnByInducCaseBody::EqualTo(eq) => {
                cases.push(merged);
                equal_tos.push(eq.clone());
            }
            HaveFnByInducCaseBody::NestedCases(nested) => {
                flatten_case_list(runtime, nested, Some(merged), cases, equal_tos, line_file)?;
            }
        }
    }
    Ok(())
}

fn merge_and_chains(
    runtime: &mut Runtime,
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
    line_file: &crate::ast::line_file::SourceLine,
) -> Result<AndChainAtomicFact, String> {
    let mut atoms =
        flatten_and_chain_atoms(runtime, left).map_err(|e| format!("case chain: {e:?}"))?;
    atoms
        .extend(flatten_and_chain_atoms(runtime, right).map_err(|e| format!("case chain: {e:?}"))?);
    if atoms.is_empty() {
        return Err("merged induc case has no atomic facts".to_string());
    }
    if atoms.len() == 1 {
        return Ok(AndChainAtomicFact::AtomicFact(atoms.remove(0)));
    }
    Ok(AndChainAtomicFact::AndFact(AndFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        facts: atoms,
        line_file: Some(line_file.clone()),
    }))
}

fn flatten_and_chain_atoms(
    runtime: &mut Runtime,
    fact: &AndChainAtomicFact,
) -> RuntimeResult<Vec<AtomicFact>> {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => Ok(vec![a.clone()]),
        AndChainAtomicFact::AndFact(a) => Ok(a.facts.clone()),
        AndChainAtomicFact::ChainFact(c) => runtime.chain_adjacent_atomics(c),
    }
}
