use crate::new_pipeline::ast::fact::IsTupleFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// A literal tuple with at least two components is a tuple.
// Example: prove `$is_tuple((a, b))`.
pub enum IsTupleFactSearchProofByBuiltinRule {
    TupleLiteral(TupleLiteralBuiltinRuleProof),
}

pub struct TupleLiteralBuiltinRuleProof {}

impl Runtime {
    // Builtin: a tuple literal with arity >= 2 is a tuple.
    // Example: prove `$is_tuple((a, b))`.
    pub fn search_is_tuple_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsTupleFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsTupleFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::Tuple(tuple) if tuple.args.len() >= 2 => Ok(Some(
                IsTupleFactSearchProofByBuiltinRule::TupleLiteral(TupleLiteralBuiltinRuleProof {}),
            )),
            _ => Ok(None),
        }
    }
}
