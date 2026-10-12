use super::add_zero_from_equalities_builtin_rule_proof::{
    AddZeroLeftFromEqualitiesBuiltinRuleProof, AddZeroRightFromEqualitiesBuiltinRuleProof,
};
use crate::prelude::*;

impl Runtime {
    // Numeric additive identity with checked equality transport:
    // b=c and a=0 imply a+b=c; a=c and b=0 imply a+b=c.
    // Example: (0,0)(1)+x(1)=x(1). Parent WD checks the numeric sum.
    // At most four fixed alternatives; premises inherit the builtin ceiling.
    pub(super) fn search_add_zero_from_equalities(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".into(),
        }));
        for (sum, target, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = sum else {
                continue;
            };

            let remaining = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: add.right.as_ref().clone(),
                right: target.clone(),
                line_file: fact.line_file.clone(),
            };
            let remaining_equal = self.verify_equal_fact(&remaining, state)?;
            if !remaining_equal.is_failed() {
                let zero_fact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: add.left.as_ref().clone(),
                    right: zero.clone(),
                    line_file: fact.line_file.clone(),
                };
                let zero_equal = self.verify_equal_fact(&zero_fact, state)?;
                if !zero_equal.is_failed() {
                    return Ok(Some(
                        EqualitySearchProofByBuiltinRule::AddZeroLeftFromEqualities(
                            AddZeroLeftFromEqualitiesBuiltinRuleProof::new(
                                remaining_equal,
                                zero_equal,
                                reversed,
                            ),
                        ),
                    ));
                }
            }

            let remaining = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: add.left.as_ref().clone(),
                right: target.clone(),
                line_file: fact.line_file.clone(),
            };
            let remaining_equal = self.verify_equal_fact(&remaining, state)?;
            if !remaining_equal.is_failed() {
                let zero_fact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: add.right.as_ref().clone(),
                    right: zero.clone(),
                    line_file: fact.line_file.clone(),
                };
                let zero_equal = self.verify_equal_fact(&zero_fact, state)?;
                if !zero_equal.is_failed() {
                    return Ok(Some(
                        EqualitySearchProofByBuiltinRule::AddZeroRightFromEqualities(
                            AddZeroRightFromEqualitiesBuiltinRuleProof::new(
                                remaining_equal,
                                zero_equal,
                                reversed,
                            ),
                        ),
                    ));
                }
            }
        }
        Ok(None)
    }
}
