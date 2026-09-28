use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Number, Obj, Sub};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin: prove `a = b` from a known fact `a - b = 0` (or `0 = a - b`).
//
// Mathematical property: if a - b = 0 then a = b.
// Example: have a R; have b R; trust a - b = 0; a = b.
//
// Scans the zero equivalence class for a Sub edge. No nested verify (avoids
// cycling with DiffZeroFromEqualOperands, which proves the opposite direction).
pub struct EqualFromKnownDifferenceZeroBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equal_from_known_difference_zero(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFromKnownDifferenceZeroBuiltinRuleProof>> {
        if fact.left.ir() == fact.right.ir() {
            return Ok(None);
        }
        let a_ir = fact.left.ir();
        let b_ir = fact.right.ir();
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".into(),
        }));
        let adjacency = self.visible_equivalence_class_adjacency();
        for key in self.equivalence_class_keys(&zero) {
            let Some(neighbors) = adjacency.get(&key) else {
                continue;
            };
            for (_peer, equal_fact) in neighbors.iter() {
                for side in [&equal_fact.left, &equal_fact.right] {
                    let Some((x, y)) = match_sub(side) else {
                        continue;
                    };
                    let xy = x.ir() == a_ir && y.ir() == b_ir;
                    let yx = x.ir() == b_ir && y.ir() == a_ir;
                    if xy || yx {
                        return Ok(Some(EqualFromKnownDifferenceZeroBuiltinRuleProof {
                            cite_fact_id: equal_fact.fact_id,
                        }));
                    }
                }
            }
        }
        Ok(None)
    }
}

fn match_sub(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}
