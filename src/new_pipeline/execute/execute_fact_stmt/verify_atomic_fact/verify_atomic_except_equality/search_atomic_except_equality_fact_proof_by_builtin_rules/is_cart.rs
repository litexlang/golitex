use crate::new_pipeline::ast::fact::IsCartFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Any `cart(...)` object is a cartesian product.
// Example: prove `$is_cart(cart(A, B))`.
pub enum IsCartFactSearchProofByBuiltinRule {
    CartConstructor(CartConstructorBuiltinRuleProof),
}

pub struct CartConstructorBuiltinRuleProof {}

impl Runtime {
    // Builtin: a cart constructor is a cart.
    // Example: prove `$is_cart(cart(A, B))`.
    pub fn search_is_cart_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsCartFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsCartFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::Cart(_) => Ok(Some(IsCartFactSearchProofByBuiltinRule::CartConstructor(
                CartConstructorBuiltinRuleProof {},
            ))),
            _ => Ok(None),
        }
    }
}
