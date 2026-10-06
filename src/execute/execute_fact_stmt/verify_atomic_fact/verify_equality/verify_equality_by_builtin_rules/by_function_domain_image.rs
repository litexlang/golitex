//! Image emptiness consumes a checked complete function domain.
use crate::ast::fact::EqualFact;
use crate::ast::obj::{FunctionSpace, Obj, SetFormer};
use crate::execute::execute_fact_stmt::function_domain::{CompleteFunctionDomainProof, FunctionDomainEmptyProof};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct FnRangeOfEmptyDomainBuiltinRuleProof {
    pub source: CompleteFunctionDomainProof,
    pub domain_empty: FunctionDomainEmptyProof,
}

impl Runtime {
    pub(super) fn search_fn_range_of_empty_domain(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<FnRangeOfEmptyDomainBuiltinRuleProof>> {
        for (image, empty) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = image else { continue; };
            let Obj::SetFormer(SetFormer::ListSet(set)) = empty else { continue; };
            if !set.list.is_empty() { continue; }
            for source in self.complete_function_domains(&range.function, state)? {
                if let Some(domain_empty) = self.verify_function_domain_empty(&source.signature, state)? {
                    return Ok(Some(FnRangeOfEmptyDomainBuiltinRuleProof { source, domain_empty }));
                }
            }
        }
        Ok(None)
    }
}
