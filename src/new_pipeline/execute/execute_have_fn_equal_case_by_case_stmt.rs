//! `have fn f(...) R by cases:` — FnSet WD, coverage, disjoint, case returns, store.
//!
//! Example:
//!   have fn sign(x R) Z by cases:
//!       case x > 0: 1
//!       case x = 0: 0
//!       case x < 0: (-1)

use crate::new_pipeline::ast::fact::{
    and_chain_as_fact, negate_atomic_fact, AndChainAtomicFact, AtomicFact, EqualFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, OrFact,
};
use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, FnSet, IdentifierObj, Obj};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::{FnSetClause, HaveFnEqualCaseByCaseStmt};
use crate::new_pipeline::exec_env::{ExecEnv, StoredIdentifierDefinition};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveFnEqualCaseByCaseStmtFailed {
    CaseCountMismatch,
    EmptyCases,
    FnSetWellDefined(VerifyObjWellDefinedResult),
    Coverage(VerifyFactResult),
    Disjoint { i: usize, j: usize },
    CaseBodyWellDefined(usize, VerifyObjWellDefinedResult),
    CaseBodyInRetSet(usize, VerifyFactResult),
}

pub struct HaveFnCasesCoverageSuccess {
    pub coverage_check: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub struct HaveFnCaseReturnCheckSuccess {
    pub case_index: usize,
    pub body_well_defined: VerifyObjWellDefinedResult,
    pub body_in_ret_set: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub struct StoreHaveFnCaseByCaseAndInferResult {
    pub membership_fact_id: FactId,
    pub case_defining_fact_ids: Vec<FactId>,
    pub stored_fact_ids: Vec<FactId>,
}

pub struct ExecHaveFnEqualCaseByCaseStmtSuccessResult {
    pub statement: HaveFnEqualCaseByCaseStmt,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub coverage: HaveFnCasesCoverageSuccess,
    pub case_return_checks: Vec<HaveFnCaseReturnCheckSuccess>,
    pub store_and_infer_result: StoreHaveFnCaseByCaseAndInferResult,
}

pub enum ExecHaveFnEqualCaseByCaseStmtResult {
    Success(ExecHaveFnEqualCaseByCaseStmtSuccessResult),
    Failed(ExecHaveFnEqualCaseByCaseStmtFailed),
}

impl ExecHaveFnEqualCaseByCaseStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: cases cover the domain, are pairwise exclusive, and
    // each branch value is well-defined in the return set; then f is callable.
    pub(super) fn exec_have_fn_equal_case_by_case_stmt(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> RuntimeResult<ExecHaveFnEqualCaseByCaseStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        if stmt.cases.is_empty() {
            return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(
                ExecHaveFnEqualCaseByCaseStmtFailed::EmptyCases,
            ));
        }
        if stmt.cases.len() != stmt.equal_tos.len() {
            return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(
                ExecHaveFnEqualCaseByCaseStmtFailed::CaseCountMismatch,
            ));
        }

        let fn_set = fn_set_from_clause(&stmt.fn_set_clause);
        let fn_set_well_defined =
            self.verify_obj_well_definedness(&Obj::FnSet(fn_set.clone()), verify_state.clone())?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(
                ExecHaveFnEqualCaseByCaseStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let coverage = match self.verify_have_fn_cases_coverage(stmt, verify_state.clone())? {
            Ok(c) => c,
            Err(failed) => {
                return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed));
            }
        };

        if let Some((i, j)) = self.verify_have_fn_cases_disjoint(stmt, verify_state.clone())? {
            return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(
                ExecHaveFnEqualCaseByCaseStmtFailed::Disjoint { i, j },
            ));
        }

        let mut case_return_checks = Vec::with_capacity(stmt.cases.len());
        for (case_index, (case_fact, equal_to)) in
            stmt.cases.iter().zip(stmt.equal_tos.iter()).enumerate()
        {
            match self.verify_have_fn_case_return(
                stmt,
                case_index,
                case_fact,
                equal_to,
                verify_state.clone(),
            )? {
                Ok(check) => case_return_checks.push(check),
                Err(failed) => {
                    return Ok(ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed));
                }
            }
        }

        let store_and_infer_result = self.store_have_fn_case_by_case_facts(stmt, &fn_set)?;

        Ok(ExecHaveFnEqualCaseByCaseStmtResult::Success(
            ExecHaveFnEqualCaseByCaseStmtSuccessResult {
                statement: stmt.clone(),
                fn_set_well_defined,
                coverage,
                case_return_checks,
                store_and_infer_result,
            },
        ))
    }

    fn verify_have_fn_cases_coverage(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<HaveFnCasesCoverageSuccess, ExecHaveFnEqualCaseByCaseStmtFailed>>
    {
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.introduce_fn_set_clause_binders(&stmt.fn_set_clause)?;
            let or_fact = Fact::OrFact(OrFact {
                fact_id: rt.ids.allocate_fact_id(),
                facts: stmt.cases.clone(),
                line_file: Some(stmt.line_file.clone()),
            });
            let coverage_check = rt.verify_fact(&or_fact, verify_state.clone())?;
            if coverage_check.is_failed() {
                return Ok(Err(ExecHaveFnEqualCaseByCaseStmtFailed::Coverage(
                    coverage_check,
                )));
            }
            Ok(Ok(coverage_check))
        })?;
        match inner {
            Ok(coverage_check) => Ok(Ok(HaveFnCasesCoverageSuccess {
                coverage_check,
                local_env,
            })),
            Err(failed) => Ok(Err(failed)),
        }
    }

    fn verify_have_fn_cases_disjoint(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(usize, usize)>> {
        for i in 0..stmt.cases.len() {
            for j in (i + 1)..stmt.cases.len() {
                if !self.have_fn_case_pair_is_disjoint(
                    stmt,
                    &stmt.cases[i],
                    &stmt.cases[j],
                    verify_state.clone(),
                )? {
                    return Ok(Some((i, j)));
                }
            }
        }
        Ok(None)
    }

    fn have_fn_case_pair_is_disjoint(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        left: &AndChainAtomicFact,
        right: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<bool> {
        if self.have_fn_case_implies_not_other(stmt, left, right, verify_state.clone())? {
            return Ok(true);
        }
        self.have_fn_case_implies_not_other(stmt, right, left, verify_state)
    }

    fn have_fn_case_implies_not_other(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        assumed: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<bool> {
        let (ok, _env) = self.run_in_local_env_and_take_env(|rt| {
            rt.introduce_fn_set_clause_binders(&stmt.fn_set_clause)?;
            let assumed_fact = and_chain_as_fact(assumed);
            let _ = rt.store_fact_and_infer(&assumed_fact)?;
            for atom in flatten_and_chain_atoms(other) {
                let Some(negated) = negate_atomic_fact(&atom, rt.ids.allocate_fact_id()) else {
                    continue;
                };
                let checked = rt.verify_fact(
                    &Fact::AtomicFact(negated.clone()),
                    verify_state.clone(),
                )?;
                if !checked.is_failed() {
                    return Ok(true);
                }
                // Strict order implies the weak opposite of the other branch.
                // Example: assumed `x > 0`, other `x < 0` → prove `x >= 0` (= not x < 0).
                if let Some(weak) = weak_order_from_strict_assumption(assumed, &atom, rt.ids.allocate_fact_id())
                {
                    let weak_checked =
                        rt.verify_fact(&Fact::AtomicFact(weak), verify_state.clone())?;
                    if !weak_checked.is_failed() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        })?;
        Ok(ok)
    }

    fn verify_have_fn_case_return(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        case_index: usize,
        case_fact: &AndChainAtomicFact,
        equal_to: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<HaveFnCaseReturnCheckSuccess, ExecHaveFnEqualCaseByCaseStmtFailed>>
    {
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.introduce_fn_set_clause_binders(&stmt.fn_set_clause)?;
            let _ = rt.store_fact_and_infer(&and_chain_as_fact(case_fact))?;

            let body_well_defined =
                rt.verify_obj_well_definedness(equal_to, verify_state.clone())?;
            if body_well_defined.is_failed() {
                return Ok(Err(
                    ExecHaveFnEqualCaseByCaseStmtFailed::CaseBodyWellDefined(
                        case_index,
                        body_well_defined,
                    ),
                ));
            }

            let in_fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: rt.ids.allocate_fact_id(),
                element: equal_to.clone(),
                set: stmt.fn_set_clause.ret_set.clone(),
                line_file: Some(stmt.line_file.clone()),
            }));
            let body_in_ret_set = rt.verify_fact(&in_fact, verify_state.clone())?;
            if body_in_ret_set.is_failed() {
                return Ok(Err(
                    ExecHaveFnEqualCaseByCaseStmtFailed::CaseBodyInRetSet(
                        case_index,
                        body_in_ret_set,
                    ),
                ));
            }

            Ok(Ok((body_well_defined, body_in_ret_set)))
        })?;
        match inner {
            Ok((body_well_defined, body_in_ret_set)) => Ok(Ok(HaveFnCaseReturnCheckSuccess {
                case_index,
                body_well_defined,
                body_in_ret_set,
                local_env,
            })),
            Err(failed) => Ok(Err(failed)),
        }
    }

    pub(crate) fn introduce_fn_set_clause_binders(
        &mut self,
        clause: &FnSetClause,
    ) -> RuntimeResult<()> {
        let typed = set_bound_to_typed(&clause.set_bound_parameters);
        let _ = self.define_typed_parameters_in_current_env(&typed, None)?;
        for dom in &clause.dom_facts {
            let _ = self.store_fact_and_infer(&quantifier_free_fact_to_fact(dom.clone()))?;
        }
        Ok(())
    }

    pub(crate) fn store_have_fn_case_by_case_facts(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set: &FnSet,
    ) -> RuntimeResult<StoreHaveFnCaseByCaseAndInferResult> {
        if self.identifier_defined_in_stack(&stmt.name) {
            return Err(RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            stmt.name.clone(),
            StoredIdentifierDefinition::HaveFnEqualCaseByCase((
                stmt.name.clone(),
                Rc::new(stmt.clone()),
            )),
        );
        self.store_piecewise_fn_membership_and_case_foralls(stmt, fn_set)
    }

    // Shared by `by cases` and `by induc`: membership + one forall equation per leaf case.
    // Caller must already have occupied the name in the definition table.
    pub(crate) fn store_piecewise_fn_membership_and_case_foralls(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set: &FnSet,
    ) -> RuntimeResult<StoreHaveFnCaseByCaseAndInferResult> {
        let function_ident =
            self.identifier_obj_for_file_root_symbol(stmt.name.clone());
        let function_obj = Obj::Identifier(function_ident.clone());

        let membership_fact_id = self.ids.allocate_fact_id();
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: membership_fact_id,
            element: function_obj.clone(),
            set: Obj::FnSet(fn_set.clone()),
            line_file: Some(stmt.line_file.clone()),
        }));
        let mut stored_fact_ids = self.store_fact_and_infer(&membership)?.stored_fact_ids();

        let typed = set_bound_to_typed(&stmt.fn_set_clause.set_bound_parameters);
        let mut args = Vec::new();
        for group in &typed.groups {
            for param in &group.params {
                args.push(Box::new(Obj::Identifier(IdentifierObj::from_bound_name(
                    param,
                ))));
            }
        }
        let applied = Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(function_ident)),
            body: vec![args],
        });

        let base_dom: Vec<Fact> = stmt
            .fn_set_clause
            .dom_facts
            .iter()
            .map(|d| quantifier_free_fact_to_fact(d.clone()))
            .collect();

        let mut case_defining_fact_ids = Vec::with_capacity(stmt.cases.len());
        for (case_fact, equal_to) in stmt.cases.iter().zip(stmt.equal_tos.iter()) {
            let mut dom_facts = base_dom.clone();
            dom_facts.push(and_chain_as_fact(case_fact));

            let equal_fact_id = self.ids.allocate_fact_id();
            let equal_atomic = AtomicFact::EqualFact(EqualFact {
                fact_id: equal_fact_id,
                left: applied.clone(),
                right: equal_to.clone(),
                line_file: Some(stmt.line_file.clone()),
            });

            let forall_id = self.ids.allocate_fact_id();
            let forall = Fact::ForallFact(ForallFact {
                fact_id: forall_id,
                typed_parameters: typed.clone(),
                dom_facts,
                then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equal_atomic)],
                line_file: Some(stmt.line_file.clone()),
            });
            let stored = self.store_fact_and_infer(&forall)?;
            case_defining_fact_ids.push(forall_id);
            stored_fact_ids.extend(stored.stored_fact_ids());
        }

        Ok(StoreHaveFnCaseByCaseAndInferResult {
            membership_fact_id,
            case_defining_fact_ids,
            stored_fact_ids,
        })
    }
}

fn fn_set_from_clause(clause: &FnSetClause) -> FnSet {
    FnSet {
        set_bound_parameters: clause.set_bound_parameters.clone(),
        dom_facts: clause.dom_facts.clone(),
        ret_set: Box::new(clause.ret_set.clone()),
    }
}

fn set_bound_to_typed(list: &SetBoundParameterList) -> TypedParameterList {
    TypedParameterList {
        groups: list
            .groups
            .iter()
            .map(|group| TypedParameterGroup {
                params: group.params.clone(),
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            })
            .collect(),
    }
}

fn flatten_and_chain_atoms(fact: &AndChainAtomicFact) -> Vec<AtomicFact> {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => vec![a.clone()],
        AndChainAtomicFact::AndFact(a) => a.facts.clone(),
        AndChainAtomicFact::ChainFact(_) => Vec::new(),
    }
}

// If `assumed` is a strict comparison, try the weak fact that blocks `other`.
// assumed `a > b` vs other `a < b` → `a >= b`; assumed `a < b` vs other `a > b` → `a <= b`.
fn weak_order_from_strict_assumption(
    assumed: &AndChainAtomicFact,
    other_atom: &AtomicFact,
    new_fact_id: FactId,
) -> Option<AtomicFact> {
    use crate::new_pipeline::ast::fact::{
        GreaterEqualFact, LessEqualFact,
    };
    let AndChainAtomicFact::AtomicFact(assumed_atom) = assumed else {
        return None;
    };
    match (assumed_atom, other_atom) {
        (AtomicFact::GreaterFact(g), AtomicFact::LessFact(l))
            if g.left == l.left && g.right == l.right =>
        {
            Some(
                GreaterEqualFact {
                    fact_id: new_fact_id,
                    left: g.left.clone(),
                    right: g.right.clone(),
                    line_file: g.line_file.clone(),
                }
                .into(),
            )
        }
        (AtomicFact::LessFact(l), AtomicFact::GreaterFact(g))
            if l.left == g.left && l.right == g.right =>
        {
            Some(
                LessEqualFact {
                    fact_id: new_fact_id,
                    left: l.left.clone(),
                    right: l.right.clone(),
                    line_file: l.line_file.clone(),
                }
                .into(),
            )
        }
        _ => None,
    }
}
