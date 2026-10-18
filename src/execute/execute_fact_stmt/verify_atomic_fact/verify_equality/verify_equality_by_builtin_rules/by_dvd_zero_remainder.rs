//! Compatibility: a zero-remainder goal uses the same native divisibility
//! rules and inherited premise ceiling. Modulo WD supplies exactly Dvd's domain.
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::dvd::DvdFactSearchProofByBuiltinRule;

pub struct DvdZeroRemainderProof {
    pub divisibility_fact: DvdFact,
    pub divisibility: Box<DvdFactSearchProofByBuiltinRule>,
}

impl Runtime {
    pub(super) fn search_dvd_zero_remainder(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<DvdZeroRemainderProof>> {
        for (remainder, zero) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if zero.ir() != Obj::Literal(Literal::Number(Number::new("0".into()))).ir() {
                continue;
            }
            let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = remainder else {
                continue;
            };
            let divisibility_fact = DvdFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *rem.left.clone(),
                right: *rem.right.clone(),
                line_file: fact.line_file.clone(),
            };
            if let Some(proof) =
                self.search_dvd_fact_proof_by_builtin_rule(&divisibility_fact, state)?
            {
                return Ok(Some(DvdZeroRemainderProof {
                    divisibility_fact,
                    divisibility: Box::new(proof),
                }));
            }
        }
        Ok(None)
    }
}
