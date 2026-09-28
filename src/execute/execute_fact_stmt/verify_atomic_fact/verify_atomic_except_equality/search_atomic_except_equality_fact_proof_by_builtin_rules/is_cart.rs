use crate::ast::fact::IsCartFact;
use crate::ast::obj::{Obj, ProductShape};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

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
            Obj::ProductShape(ProductShape::Cart(_)) => Ok(Some(IsCartFactSearchProofByBuiltinRule::CartConstructor(
                CartConstructorBuiltinRuleProof {},
            ))),
            _ => Ok(None),
        }
    }
}
