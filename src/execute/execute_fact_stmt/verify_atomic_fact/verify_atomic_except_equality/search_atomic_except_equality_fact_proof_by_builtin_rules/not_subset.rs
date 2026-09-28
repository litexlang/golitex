use crate::ast::fact::{AtomicFact, NotSubsetFact};
use crate::ast::names::AtomicName;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::parse::keywords::SUPERSET;
use crate::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `not A $subset B`.
pub enum NotSubsetFactSearchProofByBuiltinRule {
    // Duality: known `not B $superset A` proves `not A $subset B`.
    // Example: trust `not {2} $superset {1}`; prove `not {1} $subset {2}`.
    FromKnownNotSuperset(FromKnownNotSupersetBuiltinRuleProof),
}

pub struct FromKnownNotSupersetBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub fn search_not_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSubsetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSubsetFactSearchProofByBuiltinRule>> {
        if let Some(cite_fact_id) = self.known_not_superset_fact_id(&fact.right, &fact.left) {
            return Ok(Some(
                NotSubsetFactSearchProofByBuiltinRule::FromKnownNotSuperset(
                    FromKnownNotSupersetBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
        Ok(None)
    }

    pub(crate) fn known_not_superset_fact_id(
        &self,
        left: &crate::ast::obj::Obj,
        right: &crate::ast::obj::Obj,
    ) -> Option<FactId> {
        let key = (
            AtomicName::Plain {
                name: SUPERSET.into(),
            },
            false,
        );
        let left_ir = left.ir();
        let right_ir = right.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::NotSupersetFact(f) = known {
                    if f.left.ir() == left_ir && f.right.ir() == right_ir {
                        return Some(f.fact_id);
                    }
                }
            }
        }
        None
    }
}
