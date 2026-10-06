//! Empty complete domains have one graph, independently of return bounds.
use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnSet, Obj, ProductShape, SetFormer};
use crate::execute::execute_fact_stmt::function_domain::{CompleteFunctionDomainProof, FunctionDomainEmptyProof};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct EmptyFunctionGraphBuiltinRuleProof {
    pub source: CompleteFunctionDomainProof,
    pub domain_empty: FunctionDomainEmptyProof,
}

pub struct EmptyDomainFunctionSpaceSingletonBuiltinRuleProof {
    pub source_space: Obj,
    pub signature: FnSet,
    pub domain_empty: FunctionDomainEmptyProof,
}

impl Runtime {
    pub(super) fn search_empty_function_graph(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<EmptyFunctionGraphBuiltinRuleProof>> {
        for (function, empty) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::SetFormer(SetFormer::ListSet(set)) = empty else { continue; };
            if !set.list.is_empty() { continue; }
            for source in self.complete_function_domains(function, state)? {
                if let Some(domain_empty) = self.verify_function_domain_empty(&source.signature, state)? {
                    return Ok(Some(EmptyFunctionGraphBuiltinRuleProof { source, domain_empty }));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn search_empty_domain_function_space_singleton(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<EmptyDomainFunctionSpaceSingletonBuiltinRuleProof>> {
        for (space, singleton) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::SetFormer(SetFormer::ListSet(set)) = singleton else { continue; };
            if set.list.len() != 1 || !is_empty_graph_literal(&set.list[0]) { continue; }
            let signature = match space {
                Obj::ProductShape(ProductShape::Cart(cart)) => Some(self.cart_function_signature(cart)),
                _ => self.function_space_signature(space),
            };
            let Some(signature) = signature else { continue; };
            let Some(domain_empty) = self.verify_function_domain_empty(&signature, state)? else { continue; };
            return Ok(Some(EmptyDomainFunctionSpaceSingletonBuiltinRuleProof {
                source_space: space.clone(), signature, domain_empty,
            }));
        }
        Ok(None)
    }
}

fn is_empty_graph_literal(object: &Obj) -> bool {
    match object {
        Obj::ProductShape(ProductShape::Tuple(tuple)) => tuple.args.is_empty(),
        Obj::SetFormer(SetFormer::ListSet(set)) => set.list.is_empty(),
        _ => false,
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/cart_empty_function_boundaries/tests.rs"]
mod cart_empty_function_boundaries_tests;
