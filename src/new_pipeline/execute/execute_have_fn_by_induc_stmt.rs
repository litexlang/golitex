//! `have fn f(...) R by induc measure from lower:` — inductive function definition.
//!
//! Stages: FnSet WD → introduce params → measure/lower in Z + measure >= lower →
//! register restricted recursive f → coverage/disjoint/returns → flatten+store.
//!
//! Example:
//! ```text
//! have fn countdown(n N) N by induc n from 0:
//!     case n = 0: 0
//!     case n >= 1: countdown(n - 1)
//! ```

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    and_chain_as_fact, negate_atomic_fact, AndChainAtomicFact, AndFact, AtomicFact, Fact,
    GreaterEqualFact, InFact, LessFact, OrFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{FnSet, IdentifierObj, Obj, StandardSet};
use crate::new_pipeline::ast::param::{ParamType, SetBoundParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::{
    FnSetClause, HaveFnByInducCase, HaveFnByInducCaseBody, HaveFnByInducStmt,
    HaveFnEqualCaseByCaseStmt,
};
use crate::new_pipeline::exec_env::{ExecEnv, StoredIdentifierDefinition};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::StoreHaveFnCaseByCaseAndInferResult;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
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
    Disjoint { i: usize, j: usize },
    CaseBodyWellDefined(usize, VerifyObjWellDefinedResult),
    CaseBodyInRetSet(usize, VerifyFactResult),
    Shape(String),
}

pub struct ExecHaveFnByInducStmtSuccessResult {
    pub statement: HaveFnByInducStmt,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub measure_in_z: VerifyFactResult,
    pub lower_in_z: VerifyFactResult,
    pub measure_ge_lower: VerifyFactResult,
    pub coverage: VerifyFactResult,
    pub store_and_infer_result: StoreHaveFnCaseByCaseAndInferResult,
    pub local_env: Box<ExecEnv>,
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
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        if stmt.cases.is_empty() {
            return Ok(ExecHaveFnByInducStmtResult::Failed(
                ExecHaveFnByInducStmtFailed::EmptyCases,
            ));
        }

        let fn_set = fn_set_from_clause(&stmt.fn_set_clause);
        let fn_set_well_defined =
            self.verify_obj_well_definedness(&Obj::FnSet(fn_set.clone()), verify_state.clone())?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnByInducStmtResult::Failed(
                ExecHaveFnByInducStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.introduce_fn_set_clause_binders(&stmt.fn_set_clause)?;

            let measure_wd =
                rt.verify_obj_well_definedness(&stmt.measure, verify_state.clone())?;
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

            let measure_in_z = rt.verify_in_z(&stmt.measure, &stmt.line_file, verify_state.clone())?;
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
                fact_id: rt.ids.allocate_fact_id(),
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

            if let Err(msg) = rt.register_restricted_recursive_fn(stmt) {
                return Ok(Err(ExecHaveFnByInducStmtFailed::Shape(msg)));
            }

            let top_cases: Vec<AndChainAtomicFact> =
                stmt.cases.iter().map(|c| c.case_fact.clone()).collect();
            let coverage_fact = Fact::OrFact(OrFact {
                fact_id: rt.ids.allocate_fact_id(),
                facts: top_cases,
                line_file: Some(stmt.line_file.clone()),
            });
            let coverage = rt.verify_fact(&coverage_fact, verify_state.clone())?;
            if coverage.is_failed() {
                return Ok(Err(ExecHaveFnByInducStmtFailed::Coverage(coverage)));
            }

            if let Some((i, j)) =
                rt.verify_induc_cases_disjoint(stmt, &stmt.cases, verify_state.clone())?
            {
                return Ok(Err(ExecHaveFnByInducStmtFailed::Disjoint { i, j }));
            }

            if let Err(failed) =
                rt.verify_induc_case_list_returns(stmt, &stmt.cases, 0, verify_state.clone())?
            {
                return Ok(Err(failed));
            }

            Ok(Ok((
                measure_in_z,
                lower_in_z,
                measure_ge_lower,
                coverage,
            )))
        })?;

        let (measure_in_z, lower_in_z, measure_ge_lower, coverage) = match inner {
            Ok(v) => v,
            Err(failed) => return Ok(ExecHaveFnByInducStmtResult::Failed(failed)),
        };

        let flat = match flatten_induc_to_case_by_case(self, stmt) {
            Ok(f) => f,
            Err(msg) => {
                return Ok(ExecHaveFnByInducStmtResult::Failed(
                    ExecHaveFnByInducStmtFailed::Shape(msg),
                ));
            }
        };
        let store_and_infer_result = self.store_have_fn_case_by_case_facts(&flat, &fn_set)?;

        Ok(ExecHaveFnByInducStmtResult::Success(
            ExecHaveFnByInducStmtSuccessResult {
                statement: stmt.clone(),
                fn_set_well_defined,
                measure_in_z,
                lower_in_z,
                measure_ge_lower,
                coverage,
                store_and_infer_result,
                local_env,
            },
        ))
    }

    fn verify_in_z(
        &mut self,
        obj: &Obj,
        line_file: &crate::new_pipeline::ast::line_file::LineFile,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: Some(line_file.clone()),
        }));
        self.verify_fact(&fact, verify_state)
    }

    fn register_restricted_recursive_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), String> {
        if self.identifier_defined_in_stack(&stmt.name) {
            // Already occupied at parse; ensure ExecEnv definition row exists.
        } else {
            self.top_exec_env_mut().definitions.identifiers.insert(
                stmt.name.clone(),
                StoredIdentifierDefinition::HaveFnByInduc((
                    stmt.name.clone(),
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
                fact_id: self.ids.allocate_fact_id(),
                left: generated_measure.clone(),
                right: stmt.measure.clone(),
                line_file: Some(stmt.line_file.clone()),
            },
        )));
        dom_facts.push(QuantifierFreeFact::AtomicFact(
            AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: generated_measure,
                right: stmt.lower_bound.clone(),
                line_file: Some(stmt.line_file.clone()),
            }),
        ));

        let restricted = FnSet {
            set_bound_parameters: crate::new_pipeline::ast::param::SetBoundParameterList {
                groups: fresh_params,
            },
            dom_facts,
            ret_set: Box::new(generated_ret),
        };
        let function_obj =
            Obj::Identifier(self.identifier_obj_for_file_root_symbol(stmt.name.clone()));
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.ids.allocate_fact_id(),
            element: function_obj,
            set: Obj::FnSet(restricted),
            line_file: Some(stmt.line_file.clone()),
        }));
        let _ = self
            .store_fact_and_infer(&membership)
            .map_err(|e| format!("recursive membership store: {e:?}"))?;
        Ok(())
    }

    fn verify_induc_cases_disjoint(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(usize, usize)>> {
        for i in 0..cases.len() {
            for j in (i + 1)..cases.len() {
                if !self.have_fn_induc_case_pair_disjoint(
                    stmt,
                    &cases[i].case_fact,
                    &cases[j].case_fact,
                    verify_state.clone(),
                )? {
                    return Ok(Some((i, j)));
                }
            }
        }
        Ok(None)
    }

    fn have_fn_induc_case_pair_disjoint(
        &mut self,
        stmt: &HaveFnByInducStmt,
        left: &AndChainAtomicFact,
        right: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<bool> {
        if self.induc_case_implies_not_other(stmt, left, right, verify_state.clone())? {
            return Ok(true);
        }
        self.induc_case_implies_not_other(stmt, right, left, verify_state)
    }

    // Nested under the outer induc local that already introduced binders.
    // Do not re-introduce: `identifier_defined_in_stack` is name-based and
    // would InternalBug on the same param names.
    fn induc_case_implies_not_other(
        &mut self,
        _stmt: &HaveFnByInducStmt,
        assumed: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<bool> {
        let (ok, _env) = self.run_in_local_env_and_take_env(|rt| {
            let _ = rt.store_fact_and_infer(&and_chain_as_fact(assumed))?;
            for atom in flatten_and_chain_atoms(other) {
                let Some(negated) = negate_atomic_fact(&atom, rt.ids.allocate_fact_id()) else {
                    continue;
                };
                let checked =
                    rt.verify_fact(&Fact::AtomicFact(negated), verify_state.clone())?;
                if !checked.is_failed() {
                    return Ok(true);
                }
            }
            Ok(false)
        })?;
        Ok(ok)
    }

    fn verify_induc_case_list_returns(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
        index_base: usize,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<(), ExecHaveFnByInducStmtFailed>> {
        for (offset, case) in cases.iter().enumerate() {
            let case_index = index_base + offset;
            match &case.body {
                HaveFnByInducCaseBody::EqualTo(equal_to) => {
                    // Binders already live on the outer induc local; only
                    // assume this case in a nested env.
                    let (inner, _env) = self.run_in_local_env_and_take_env(|rt| {
                        let _ = rt.store_fact_and_infer(&and_chain_as_fact(&case.case_fact))?;
                        let body_wd =
                            rt.verify_obj_well_definedness(equal_to, verify_state.clone())?;
                        if body_wd.is_failed() {
                            return Ok(Err(
                                ExecHaveFnByInducStmtFailed::CaseBodyWellDefined(
                                    case_index,
                                    body_wd,
                                ),
                            ));
                        }
                        let in_fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
                            fact_id: rt.ids.allocate_fact_id(),
                            element: equal_to.clone(),
                            set: stmt.fn_set_clause.ret_set.clone(),
                            line_file: Some(stmt.line_file.clone()),
                        }));
                        let in_ret = rt.verify_fact(&in_fact, verify_state.clone())?;
                        if in_ret.is_failed() {
                            return Ok(Err(ExecHaveFnByInducStmtFailed::CaseBodyInRetSet(
                                case_index,
                                in_ret,
                            )));
                        }
                        Ok(Ok(()))
                    })?;
                    if let Err(failed) = inner {
                        return Ok(Err(failed));
                    }
                }
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    let (inner, _env) = self.run_in_local_env_and_take_env(|rt| {
                        let _ = rt.store_fact_and_infer(&and_chain_as_fact(&case.case_fact))?;
                        rt.verify_induc_case_list_returns(
                            stmt,
                            nested,
                            case_index * 1000,
                            verify_state.clone(),
                        )
                    })?;
                    if let Err(failed) = inner {
                        return Ok(Err(failed));
                    }
                }
            }
        }
        Ok(Ok(()))
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
            let fresh = BoundName::new(
                runtime.ids.allocate_identifier_id(),
                format!("_{}", p.name),
            );
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

fn flatten_induc_to_case_by_case(
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
    line_file: &crate::new_pipeline::ast::line_file::LineFile,
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
                flatten_case_list(
                    runtime,
                    nested,
                    Some(merged),
                    cases,
                    equal_tos,
                    line_file,
                )?;
            }
        }
    }
    Ok(())
}

fn merge_and_chains(
    runtime: &mut Runtime,
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
    line_file: &crate::new_pipeline::ast::line_file::LineFile,
) -> Result<AndChainAtomicFact, String> {
    let mut atoms = flatten_and_chain_atoms(left);
    atoms.extend(flatten_and_chain_atoms(right));
    if atoms.is_empty() {
        return Err("merged induc case has no atomic facts".to_string());
    }
    if atoms.len() == 1 {
        return Ok(AndChainAtomicFact::AtomicFact(atoms.remove(0)));
    }
    Ok(AndChainAtomicFact::AndFact(AndFact {
        fact_id: runtime.ids.allocate_fact_id(),
        facts: atoms,
        line_file: Some(line_file.clone()),
    }))
}

fn flatten_and_chain_atoms(fact: &AndChainAtomicFact) -> Vec<AtomicFact> {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => vec![a.clone()],
        AndChainAtomicFact::AndFact(a) => a.facts.clone(),
        AndChainAtomicFact::ChainFact(_) => Vec::new(),
    }
}

// Silence unused TypedParameterList import path if needed via ParamType.
#[allow(dead_code)]
fn _typed_touch(_: &TypedParameterList, _: &ParamType) {}
