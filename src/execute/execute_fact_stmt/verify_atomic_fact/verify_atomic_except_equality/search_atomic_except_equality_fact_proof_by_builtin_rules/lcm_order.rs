//! Every positive common multiple bounds the least common multiple.
use crate::ast::fact::{DvdFact, Fact, InFact, LessEqualFact};
use crate::ast::obj::{Abs, ArithmeticOperator, IntegerOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct LcmCommonMultipleBoundProof {
    pub domains: Vec<VerifyFactResult>,
    pub first_multiple: VerifyFactResult,
    pub second_multiple: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_lcm_common_multiple_bound(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LcmCommonMultipleBoundProof>> {
        // a,b in Z*, m in N+, $dvd(m,abs(a)), $dvd(m,abs(b)) imply lcm(a,b)<=m.
        let Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) = &fact.left else {
            return Ok(None);
        };
        let mut domains = Vec::new();
        for (obj, set) in [
            (&*lcm.left, StandardSet::ZStar),
            (&*lcm.right, StandardSet::ZStar),
            (&fact.right, StandardSet::NPos),
        ] {
            let premise: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: obj.clone(),
                set: Obj::StandardSet(set),
                line_file: fact.line_file.clone(),
            }
            .into();
            let proof = self.verify_builtin_rule_premise(&premise, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            domains.push(proof);
        }
        let mut multiples = Vec::new();
        for arg in [&lcm.left, &lcm.right] {
            let premise: Fact = DvdFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.right.clone(),
                right: Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: arg.clone() })),
                line_file: fact.line_file.clone(),
            }
            .into();
            let proof = self.verify_builtin_rule_premise(&premise, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            multiples.push(proof);
        }
        let second_multiple = multiples.pop().unwrap();
        let first_multiple = multiples.pop().unwrap();
        Ok(Some(LcmCommonMultipleBoundProof {
            domains,
            first_multiple,
            second_multiple,
        }))
    }
}
