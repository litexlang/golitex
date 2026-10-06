//! Publish the complete exact-domain Cartesian function-set definition.
use crate::ast::fact::{EqualFact, Fact};
use crate::ast::obj::{Obj, ProductShape};
use crate::ast::stmt::ReleaseCartDefStmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    VerifyEqualityFailed, VerifyEqualityResult, VerifyEqualitySuccess,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecReleaseCartDefStmtResult {
    Success(ExecReleaseCartDefStmtSuccess),
    Failed(VerifyEqualityFailed),
}

pub struct ExecReleaseCartDefStmtSuccess {
    pub statement: ReleaseCartDefStmt,
    pub verification: VerifyEqualitySuccess,
    pub store_and_infer: StoreFactAndInferResult,
}

impl ExecReleaseCartDefStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    pub(in crate::execute) fn exec_release_cart_def_stmt(
        &mut self,
        stmt: &ReleaseCartDefStmt,
    ) -> RuntimeResult<ExecReleaseCartDefStmtResult> {
        let definition = self.cart_function_set_definition(&stmt.cart);
        let equation = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::Cart(stmt.cart.clone())),
            right: definition,
            line_file: Some(stmt.line_file.clone()),
        };
        let VerifyFactResult::Equality(result) =
            self.verify_equal_fact(&equation, VerifyState::top_level())?
        else {
            unreachable!("equality verification branch");
        };
        let verification = match *result {
            VerifyEqualityResult::Success(proof) => proof,
            VerifyEqualityResult::Failed(reason) => {
                return Ok(ExecReleaseCartDefStmtResult::Failed(reason))
            }
        };
        let store_and_infer =
            self.store_fact_and_infer(&Fact::from(equation), VerifyState::top_level())?;
        Ok(ExecReleaseCartDefStmtResult::Success(
            ExecReleaseCartDefStmtSuccess {
                statement: stmt.clone(),
                verification,
                store_and_infer,
            },
        ))
    }
}
