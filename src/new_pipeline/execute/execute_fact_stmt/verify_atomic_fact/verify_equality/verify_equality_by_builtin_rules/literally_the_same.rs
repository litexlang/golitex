use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin: left and right are the same atom (same IdentifierId).
// Example: prove `a = a` when both sides are Identifier with equal identifier_id.
pub enum LiterallyTheSameBuiltinRuleProof {
    SameIdentifierId(LiterallyTheSameBySameIdentifierIdProof),
}

pub struct LiterallyTheSameBySameIdentifierIdProof {
    pub identifier_id: IdentifierId,
}

impl Runtime {
    // Builtin: same Obj atom family and equal IdentifierId ⇒ equality.
    // Example: after `have x R`, prove `x = x`.
    pub fn search_equal_fact_proof_by_literally_the_same(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LiterallyTheSameBuiltinRuleProof>> {
        let _ = verify_state;
        match (&fact.left, &fact.right) {
            (Obj::Atom(AtomObj::Identifier(left)), Obj::Atom(AtomObj::Identifier(right)))
                if left.identifier_id == right.identifier_id =>
            {
                Ok(Some(LiterallyTheSameBuiltinRuleProof::SameIdentifierId(
                    LiterallyTheSameBySameIdentifierIdProof {
                        identifier_id: left.identifier_id,
                    },
                )))
            }
            (
                Obj::Atom(AtomObj::IdentifierWithMod(left)),
                Obj::Atom(AtomObj::IdentifierWithMod(right)),
            ) if left.identifier_id == right.identifier_id => {
                Ok(Some(LiterallyTheSameBuiltinRuleProof::SameIdentifierId(
                    LiterallyTheSameBySameIdentifierIdProof {
                        identifier_id: left.identifier_id,
                    },
                )))
            }
            _ => Ok(None),
        }
    }
}
