//! `have by fn_preimage: names from z $in fn_range(f)` — name preimage witnesses.
//!
//! After `z $in fn_range(f)` is known and `f` has a visible FnSet body, introduce
//! one name per input coordinate of `f`, store their domain memberships (and
//! any extra domain facts of `f`), and store `z = f(names…)`.
//!
//! Example:
//!   have fn shift(x Z) Z = x + 1
//!   shift(2) $in fn_range(shift)
//!   have by fn_preimage: source from shift(2) $in fn_range(shift)
//!   // stores `source $in Z` and `shift(2) = shift(source)`

use std::collections::HashMap;

use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::names::BoundName;
use crate::ast::obj::{
    FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj,
};
use crate::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::ast::stmt::HaveByPreimageStmt;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{IdentifierId, Runtime, RuntimeError, RuntimeResult};

pub enum ExecHaveByFnPreimageStmtFailed {
    NotFnRange(String),
    NoFnSetBody(String),
    ArityMismatch { expected: usize, got: usize },
    SourceMembership(VerifyFactResult),
}

pub struct ExecHaveByFnPreimageStmtSuccessResult {
    pub statement: HaveByPreimageStmt,
    pub source_membership: VerifyFactResult,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecHaveByFnPreimageStmtResult {
    Success(ExecHaveByFnPreimageStmtSuccessResult),
    Failed(ExecHaveByFnPreimageStmtFailed),
}

impl ExecHaveByFnPreimageStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Example: `have by fn_preimage: source from shift(2) $in fn_range(shift)`
    pub(super) fn exec_have_by_fn_preimage_stmt(
        &mut self,
        stmt: &HaveByPreimageStmt,
    ) -> RuntimeResult<ExecHaveByFnPreimageStmtResult> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(fn_range)) = &stmt.range_membership.set
        else {
            return Ok(ExecHaveByFnPreimageStmtResult::Failed(
                ExecHaveByFnPreimageStmtFailed::NotFnRange(
                    "have by fn_preimage: `from` expects `… $in fn_range(…)`".to_string(),
                ),
            ));
        };
        let function = fn_range.function.as_ref().clone();
        let Some(body) = self.resolve_fn_set_body_for_fn_preimage(&function) else {
            return Ok(ExecHaveByFnPreimageStmtResult::Failed(
                ExecHaveByFnPreimageStmtFailed::NoFnSetBody(format!(
                    "have by fn_preimage: function `{}` has no known function set",
                    function.ir()
                )),
            ));
        };

        let expected = set_bound_parameter_count(&body.set_bound_parameters);
        let got = stmt.preimage_names.len();
        if expected != got {
            return Ok(ExecHaveByFnPreimageStmtResult::Failed(
                ExecHaveByFnPreimageStmtFailed::ArityMismatch { expected, got },
            ));
        }

        let verify_state = VerifyState {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
                    builtin_strategy_depth_remaining: VerifyState::BUILTIN_STRATEGY_DEPTH_LIMIT,
};
        let source_membership = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(stmt.range_membership.clone())),
            verify_state,
        )?;
        if source_membership.is_failed() {
            return Ok(ExecHaveByFnPreimageStmtResult::Failed(
                ExecHaveByFnPreimageStmtFailed::SourceMembership(source_membership),
            ));
        }

        let (renamed_params, subst, preimage_objs) =
            self.build_fn_preimage_params_and_subst(stmt, &body)?;

        let mut store_and_infer_result =
            self.define_typed_parameters_in_current_env(&renamed_params, None)?;

        for dom_fact in &body.dom_facts {
            let instantiated = self.inst_quantifier_free_fact(dom_fact, &subst).map_err(|e| {
                RuntimeError::InternalBug(format!(
                    "have by fn_preimage: failed to instantiate domain fact: {e}"
                ))
            })?;
            let as_fact = quantifier_free_fact_to_fact(instantiated);
            let stored = self.store_fact_and_infer(&as_fact)?;
            store_and_infer_result
                .stored_fact_ids
                .extend(stored.stored_fact_ids());
        }

        let Some(application) = fn_preimage_application_obj(&function, &preimage_objs) else {
            return Err(RuntimeError::InternalBug(format!(
                "have by fn_preimage: cannot build application for `{}`",
                function.ir()
            )));
        };
        let equality = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: stmt.range_membership.element.clone(),
            right: application,
            line_file: stmt.range_membership.line_file.clone(),
        }));
        let stored = self.store_fact_and_infer(&equality)?;
        store_and_infer_result
            .stored_fact_ids
            .extend(stored.stored_fact_ids());

        Ok(ExecHaveByFnPreimageStmtResult::Success(
            ExecHaveByFnPreimageStmtSuccessResult {
                statement: stmt.clone(),
                source_membership,
                store_and_infer_result,
            },
        ))
    }

    fn resolve_fn_set_body_for_fn_preimage(&self, function: &Obj) -> Option<FnSet> {
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function {
            return Some(anon.body.clone());
        }
        self.collect_in_function_set_candidates(function)
            .into_iter()
            .next()
            .map(|(fn_set, _)| fn_set)
    }

    fn build_fn_preimage_params_and_subst(
        &mut self,
        stmt: &HaveByPreimageStmt,
        body: &FnSet,
    ) -> RuntimeResult<(TypedParameterList, HashMap<IdentifierId, Obj>, Vec<Obj>)> {
        let mut subst = HashMap::new();
        let mut groups = Vec::new();
        let mut preimage_objs = Vec::new();
        let mut name_index = 0usize;

        for group in &body.set_bound_parameters.groups {
            let param_type_obj = self
                .inst_obj(group.param_type.as_ref(), &subst)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!(
                        "have by fn_preimage: failed to instantiate parameter type: {e}"
                    ))
                })?;
            let mut params = Vec::new();
            for old in &group.params {
                let name = stmt.preimage_names[name_index].clone();
                name_index += 1;
                let id = self.resolve_plain_atom(&name)?;
                let bound = BoundName::new(id, name);
                let obj = Obj::Identifier(self.identifier_obj_for_stored_mention(&bound));
                subst.insert(old.id, obj.clone());
                preimage_objs.push(obj);
                params.push(bound);
            }
            groups.push(TypedParameterGroup {
                params,
                param_type: ParamType::Obj(param_type_obj),
            });
        }

        Ok((TypedParameterList { groups }, subst, preimage_objs))
    }
}

fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

fn fn_preimage_application_obj(function: &Obj, args: &[Obj]) -> Option<Obj> {
    let head = match function {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))
        }
        Obj::InstantiatedTemplateObj(inst) => FnObjHead::InstantiatedTemplateObj(inst.clone()),
        _ => return None,
    };
    let group = args.iter().cloned().map(Box::new).collect();
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![group],
    }))
}
