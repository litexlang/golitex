//! Explicitly publish a checked tuple's exact finite-function contract.
//! Construction length comes from a value or a checked membership, never from
//! the identity of a Cartesian set. Publication uses the exec_stmt transaction.
use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{FiniteSeqSet, Literal, Number, Obj, SetFormer};
use crate::ast::stmt::ReleaseTupleDefStmt;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::function_domain::{
    function_application, FunctionDomainMatchFailure, FunctionDomainMatchProof,
};
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, VerifyFactResult, VerifyFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecReleaseTupleDefStmtResult {
    Success(ExecReleaseTupleDefStmtSuccess),
    Failed(ExecReleaseTupleDefStmtFailed),
}

// Stages: checked shape -> exact domain -> all return premises -> membership
// WD -> all coordinates -> publication. No conclusion is stored during checks.
pub struct ExecReleaseTupleDefStmtSuccess {
    pub statement: ReleaseTupleDefStmt,
    pub shape: FiniteFunctionSignatureProof,
    pub domain: FunctionDomainMatchProof,
    pub membership_rule: BuiltinThmApplication,
    pub return_proofs: Vec<VerifyFactResult>,
    pub membership_wd: FactWellDefinedProof,
    pub coordinate_proofs: Vec<VerifyFactResult>,
    pub stored: Vec<StoreFactAndInferResult>,
}

pub enum ExecReleaseTupleDefStmtFailed {
    Shape,
    Domain(FunctionDomainMatchFailure),
    Requirements(String),
    Return { fact: Fact, result: VerifyFactResult },
    MembershipWd(VerifyFactWellDefinedResult),
    Coordinate { fact: Fact, result: VerifyFactResult },
}

impl ExecReleaseTupleDefStmtResult {
    pub fn is_failed(&self) -> bool { matches!(self, Self::Failed(_)) }
}

impl Runtime {
    pub(in crate::execute) fn exec_release_tuple_def_stmt(
        &mut self, stmt: &ReleaseTupleDefStmt,
    ) -> RuntimeResult<ExecReleaseTupleDefStmtResult> {
        use ExecReleaseTupleDefStmtFailed as Failed;
        let Some(shape) = self.finite_function_signatures(&stmt.obj).into_iter().next() else {
            return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::Shape));
        };
        let ctx = VerifyState::top_level();
        let domain = match self.verify_complete_function_domain(&stmt.obj, &shape.signature, ctx)? {
            Ok(proof) => proof,
            Err(reason) => return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::Domain(reason))),
        };
        let carrier = Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
            set: shape.signature.ret_set.clone(),
            n: Box::new(number(shape.source.dimension())),
        }));
        let membership: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: stmt.obj.clone(),
            set: carrier.clone(), line_file: Some(stmt.line_file.clone()),
        }.into();
        // The registered fn_set_member rule requires exact domain matching
        // plus every return bound. Use its existing requirement builder and
        // top-level checker, without widening implicit membership search.
        let requirements = match self.build_function_return_requirements(&stmt.obj, &shape.signature) {
            Ok(facts) => facts,
            Err(reason) => return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::Requirements(reason))),
        };
        let mut return_proofs = Vec::new();
        for fact in &requirements {
            let result = self.verify_fact(fact, ctx)?;
            if result.is_failed() {
                return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::Return { fact: fact.clone(), result }));
            }
            return_proofs.push(result);
        }
        let membership_wd = match self.verify_fact_well_definedness(&membership, ctx)? {
            VerifyFactWellDefinedResult::Success(proof) => proof,
            failed => return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::MembershipWd(failed))),
        };
        let mut coordinates = Vec::new();
        let mut coordinate_proofs = Vec::new();
        for index in 0..shape.source.dimension() {
            // Preserve an actual call even for literal tuples; `1 = 1`
            // would not be a reusable coordinate equation for `(1,2)`.
            let coordinate = function_application(&stmt.obj, vec![Box::new(number(index + 1))])
                .expect("ordinary object application has no construction failure");
            let fact: Fact = match &shape.source {
                KnownTupleShapeProof::TupleEquality(value) => EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(), left: coordinate,
                    right: value.value.args[index].as_ref().clone(), line_file: Some(stmt.line_file.clone()),
                }.into(),
                source => InFact {
                    fact_id: self.global_ids.allocate_fact_id(), element: coordinate,
                    set: source.cart().expect("nonliteral shape has a checked Cartesian contract").args[index].as_ref().clone(),
                    line_file: Some(stmt.line_file.clone()),
                }.into(),
            };
            let result = self.verify_fact(&fact, ctx)?;
            if result.is_failed() {
                return Ok(ExecReleaseTupleDefStmtResult::Failed(Failed::Coordinate { fact, result }));
            }
            coordinates.push(fact);
            coordinate_proofs.push(result);
        }
        let membership_rule = BuiltinThmApplication {
            theorem: BuiltinTheoremId::FunctionSetMember,
            arguments: vec![stmt.obj.clone(), carrier], requirements,
            conclusions: vec![membership.clone()],
        };
        let mut stored = Vec::new();
        for fact in std::iter::once(&membership).chain(coordinates.iter()) {
            stored.push(self.store_fact_and_infer(fact, ctx)?);
        }
        Ok(ExecReleaseTupleDefStmtResult::Success(ExecReleaseTupleDefStmtSuccess {
            statement: stmt.clone(), shape, domain, membership_rule, return_proofs,
            membership_wd, coordinate_proofs, stored,
        }))
    }
}

fn number(value: usize) -> Obj {
    Obj::Literal(Literal::Number(Number { normalized_value: value.to_string() }))
}

#[cfg(test)]
#[path = "../../tests/unit/execute/release_tuple_def/tests.rs"]
mod release_tuple_def_tests;
