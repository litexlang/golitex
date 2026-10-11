//! An exact finite sequence is determined by its ordered calls.
use crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize;
use crate::prelude::*;

pub struct FiniteSeqReconstructionBuiltinRuleProof {
    pub membership: InFact,
    pub reversed: bool,
}

impl Runtime {
    // x in finite_seq(S,n) => x=(x(1),...,x(n)). No new premise search.
    // Both sides have passed WD; only a stored complete-domain fact is used.
    pub(super) fn search_finite_seq_reconstruction(
        &self,
        fact: &EqualFact,
    ) -> Option<FiniteSeqReconstructionBuiltinRuleProof> {
        for (subject, value, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ProductShape(ProductShape::Tuple(tuple)) = value else {
                continue;
            };
            let mut ordered = true;
            for (i, item) in tuple.args.iter().enumerate() {
                let Obj::FnObj(call) = item.as_ref() else {
                    ordered = false;
                    break;
                };
                let Some(receiver) = self.finite_function_application_receiver(call) else {
                    ordered = false;
                    break;
                };
                let args = call.body.last().unwrap();
                if receiver.ir() != subject.ir()
                    || args.len() != 1
                    || literal_positive_usize(&args[0]) != Some(i + 1)
                {
                    ordered = false;
                    break;
                }
            }
            if !ordered {
                continue;
            }
            for membership in self.known_memberships_of(subject) {
                let Obj::SetFormer(SetFormer::FiniteSeqSet(space)) = &membership.set else {
                    continue;
                };
                let Obj::Literal(Literal::Number(length)) = space.n.as_ref() else {
                    continue;
                };
                if length.normalized_value.parse::<usize>().ok() == Some(tuple.args.len()) {
                    return Some(FiniteSeqReconstructionBuiltinRuleProof {
                        membership,
                        reversed,
                    });
                }
            }
        }
        None
    }
}
