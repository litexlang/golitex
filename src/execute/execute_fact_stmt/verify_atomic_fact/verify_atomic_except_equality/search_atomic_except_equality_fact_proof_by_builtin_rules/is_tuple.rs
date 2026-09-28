use crate::ast::fact::IsTupleFact;
use crate::ast::obj::{Obj, ProductShape};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

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
            Obj::ProductShape(ProductShape::Tuple(tuple)) if tuple.args.len() >= 2 => Ok(Some(
                IsTupleFactSearchProofByBuiltinRule::TupleLiteral(TupleLiteralBuiltinRuleProof {}),
            )),
            _ => Ok(None),
        }
    }
}
