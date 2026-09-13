use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::AtomId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin: left and right are the same atom (same AtomId).
// Example: prove `a = a` when both sides are Identifier with equal atom_id.
pub enum LiterallyTheSameBuiltinRuleProof {
    SameAtomId(LiterallyTheSameBySameAtomIdProof),
}

pub struct LiterallyTheSameBySameAtomIdProof {
    pub atom_id: AtomId,
}

impl Runtime {
    // Builtin: same Obj atom family and equal AtomId ⇒ equality.
    // Example: after `have x R`, prove `x = x`.
    pub fn search_equal_fact_proof_by_literally_the_same(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LiterallyTheSameBuiltinRuleProof>> {
        let _ = verify_state;
        match (&fact.left, &fact.right) {
            (Obj::Atom(AtomObj::Identifier(left)), Obj::Atom(AtomObj::Identifier(right)))
                if left.atom_id == right.atom_id =>
            {
                Ok(Some(LiterallyTheSameBuiltinRuleProof::SameAtomId(
                    LiterallyTheSameBySameAtomIdProof {
                        atom_id: left.atom_id,
                    },
                )))
            }
            (
                Obj::Atom(AtomObj::IdentifierWithMod(left)),
                Obj::Atom(AtomObj::IdentifierWithMod(right)),
            ) if left.atom_id == right.atom_id => Ok(Some(
                LiterallyTheSameBuiltinRuleProof::SameAtomId(LiterallyTheSameBySameAtomIdProof {
                    atom_id: left.atom_id,
                }),
            )),
            _ => Ok(None),
        }
    }
}
