//! `have fn f(...) R = expr` — WD anon + WD FnSet, then store membership and equality.
//!
//! Example:
//!   have fn successor(x Z) Z = x + 1

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{FnSet, Obj};
use crate::new_pipeline::ast::stmt::HaveFnEqualStmt;
use crate::new_pipeline::exec_env::{DefinedIdentifierInfo, StoredIdentifierDefinition};
use crate::new_pipeline::execute::execute_fact_stmt::{VerifyObjWellDefinedResult, VerifyState};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveFnEqualStmtFailed {
    AnonymousFnWellDefined(VerifyObjWellDefinedResult),
    FnSetWellDefined(VerifyObjWellDefinedResult),
}

pub struct StoreHaveFnEqualAndInferResult {
    pub membership_fact_id: FactId,
    pub defining_equal_fact_id: FactId,
    pub stored_fact_ids: Vec<FactId>,
}

// Pipeline: AnonFn WD → FnSet WD → occupy name + store f∈FnSet and f=anon.
pub struct ExecHaveFnEqualStmtSuccessResult {
    pub statement: HaveFnEqualStmt,
    pub anonymous_fn_well_defined: VerifyObjWellDefinedResult,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub store_and_infer_result: StoreHaveFnEqualAndInferResult,
}

pub enum ExecHaveFnEqualStmtResult {
    Success(ExecHaveFnEqualStmtSuccessResult),
    Failed(ExecHaveFnEqualStmtFailed),
}

impl ExecHaveFnEqualStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: the anonymous defining function is well-formed and
    // return-typed; its FnSet carrier is well-formed; then the name is callable.
    pub(super) fn exec_have_fn_equal_stmt(
        &mut self,
        stmt: &HaveFnEqualStmt,
    ) -> RuntimeResult<ExecHaveFnEqualStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let anon_obj = Obj::AnonymousFn(stmt.equal_to_anonymous_fn.clone());
        let anonymous_fn_well_defined =
            self.verify_obj_well_definedness(&anon_obj, verify_state.clone())?;
        if anonymous_fn_well_defined.is_failed() {
            return Ok(ExecHaveFnEqualStmtResult::Failed(
                ExecHaveFnEqualStmtFailed::AnonymousFnWellDefined(anonymous_fn_well_defined),
            ));
        }

        let fn_set: FnSet = stmt.equal_to_anonymous_fn.body.clone();
        let fn_set_obj = Obj::FnSet(fn_set.clone());
        let fn_set_well_defined =
            self.verify_obj_well_definedness(&fn_set_obj, verify_state)?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnEqualStmtResult::Failed(
                ExecHaveFnEqualStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let store_and_infer_result = self.store_have_fn_equal_facts(stmt, &fn_set)?;

        Ok(ExecHaveFnEqualStmtResult::Success(
            ExecHaveFnEqualStmtSuccessResult {
                statement: stmt.clone(),
                anonymous_fn_well_defined,
                fn_set_well_defined,
                store_and_infer_result,
            },
        ))
    }

    fn store_have_fn_equal_facts(
        &mut self,
        stmt: &HaveFnEqualStmt,
        fn_set: &FnSet,
    ) -> RuntimeResult<StoreHaveFnEqualAndInferResult> {
        if self.identifier_defined_in_stack(&stmt.name) {
            return Err(RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            stmt.name.clone(),
            DefinedIdentifierInfo {
                identifier: stmt.name.clone(),
                definition: StoredIdentifierDefinition::HaveFnEqual(Rc::new(stmt.clone())),
            },
        );

        // HaveFnEqualStmt carries `name: String`; file-root mention uses qualified form.
        let function_obj = Obj::Identifier(self.identifier_obj_for_file_root_symbol(stmt.name.clone()));

        let membership_fact_id = self.ids.allocate_fact_id();
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: membership_fact_id,
            element: function_obj.clone(),
            set: Obj::FnSet(fn_set.clone()),
            line_file: Some(stmt.line_file.clone()),
        }));
        let mut stored_fact_ids = self.store_fact_and_infer(&membership)?.stored_fact_ids();

        let defining_equal_fact_id = self.ids.allocate_fact_id();
        let defining_equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: defining_equal_fact_id,
            left: function_obj,
            right: Obj::AnonymousFn(stmt.equal_to_anonymous_fn.clone()),
            line_file: Some(stmt.line_file.clone()),
        }));
        stored_fact_ids.extend(
            self.store_fact_and_infer(&defining_equal)?
                .stored_fact_ids(),
        );

        Ok(StoreHaveFnEqualAndInferResult {
            membership_fact_id,
            defining_equal_fact_id,
            stored_fact_ids,
        })
    }
}
