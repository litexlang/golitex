use super::helper::corresponding_arg_pairs;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Pointwise / constructor-wise equality: same outer shape ⇒ prove each
// corresponding child equal. Port of legacy same_shape_and_corresponding_args_match
// over new_pipeline Obj (except binder shapes: SetBuilder / AnonymousFn / FnSet).
//
// Mathematical property: congruence of constructors —
// if corresponding children are equal, the constructed terms are equal.
//
// Examples:
//   have a R = 1
//   have b R = a
//   a + 1 = b + 1
// peels Add → prove a = b and 1 = 1.
//
//   have a R = 1
//   have b R = a
//   have f set
//   f(a) = f(b)
// peels FnObj → prove a = b and f = f (prefix).
//
//   f(x)(a) = h(y)(b) with f = h, x = y, a = b
// peels shared application layers then prefixes in one certificate.
//
// Child searches use can_use_forall_fact = false, can_use_rewrite = false
// (this stage itself is not a rewrite). Nested peel is still available because
// MatchingOneArgByOne is scheduled before the rewrite gate.
pub struct EqualFactSearchedProofByMatchingOneArgByOne {
    pub corresponding_arg_equal_proofs: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn search_equal_fact_proof_by_matching_one_arg_by_one(
        &mut self,
        fact: &EqualFact,
        child_verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByMatchingOneArgByOne>> {
        let Some(pairs) = corresponding_arg_pairs(&fact.left, &fact.right) else {
            return Ok(None);
        };
        if pairs.is_empty() {
            return Ok(None);
        }

        let mut corresponding_arg_equal_proofs = Vec::with_capacity(pairs.len());
        for (left_arg, right_arg) in pairs {
            let child = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: left_arg,
                right: right_arg,
                line_file: fact.line_file.clone(),
            };
            let proof = self.verify_equal_fact(&child, child_verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            corresponding_arg_equal_proofs.push(proof);
        }

        Ok(Some(EqualFactSearchedProofByMatchingOneArgByOne {
            corresponding_arg_equal_proofs,
        }))
    }
}
