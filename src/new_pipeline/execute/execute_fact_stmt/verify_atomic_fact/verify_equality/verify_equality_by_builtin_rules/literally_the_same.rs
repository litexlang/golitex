use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin: left and right are the same atom (same name identity).
// Example: prove `a = a` when both sides are Identifier with equal name.
pub enum LiterallyTheSameBuiltinRuleProof {
    SameName(LiterallyTheSameBySameNameProof),
}

pub struct LiterallyTheSameBySameNameProof {
    pub name: String,
}

impl Runtime {
    // Builtin: same Obj atom family and equal name identity ⇒ equality.
    // Example: after `have x R`, prove `x = x`.
    pub fn search_equal_fact_proof_by_literally_the_same(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LiterallyTheSameBuiltinRuleProof>> {
        let _ = verify_state;
        match (&fact.left, &fact.right) {
            (Obj::Atom(AtomObj::Identifier(left)), Obj::Atom(AtomObj::Identifier(right)))
                if left.name == right.name =>
            {
                Ok(Some(LiterallyTheSameBuiltinRuleProof::SameName(
                    LiterallyTheSameBySameNameProof {
                        name: left.name.clone(),
                    },
                )))
            }
            (
                Obj::Atom(AtomObj::IdentifierWithMod(left)),
                Obj::Atom(AtomObj::IdentifierWithMod(right)),
            ) if left.mod_name == right.mod_name && left.name == right.name => {
                Ok(Some(LiterallyTheSameBuiltinRuleProof::SameName(
                    LiterallyTheSameBySameNameProof {
                        name: format!("{}::{}", left.mod_name, left.name),
                    },
                )))
            }
            _ => Ok(None),
        }
    }
}
