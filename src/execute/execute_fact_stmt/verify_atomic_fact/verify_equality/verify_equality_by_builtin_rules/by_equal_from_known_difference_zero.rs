use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, Literal, Number, Obj, Sub};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_path_in_adjacency;
use crate::prelude::KnownEqualityPathProof;
use crate::runtime::{FactId, Runtime, RuntimeResult};

// Builtin: prove `a = b` from a known fact `a - b = 0` (or `0 = a - b`).
//
// Mathematical property: if a - b = 0 then a = b.
// Example: have a R; have b R; trust a - b = 0; a = b.
//
// Scans the zero equivalence class for a Sub edge. No nested verify (avoids
// cycling with DiffZeroFromEqualOperands, which proves the opposite direction).
pub struct EqualFromKnownDifferenceZeroBuiltinRuleProof {
    pub cite_fact_id: FactId,
    pub difference_on_left: bool,
    pub zero_path: KnownEqualityPathProof,
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
                for (side, peer, difference_on_left) in [
                    (&equal_fact.left, &equal_fact.right, true),
                    (&equal_fact.right, &equal_fact.left, false),
                ] {
                    let Some((x, y)) = match_sub(side) else {
                        continue;
                    };
                    let xy = x.ir() == a_ir && y.ir() == b_ir;
                    let yx = x.ir() == b_ir && y.ir() == a_ir;
                    if xy || yx {
                        // The selected edge can end at another member of zero's
                        // class. Retain its remaining path from this same visible
                        // graph, without nested verification or new stored facts.
                        let Some(path) =
                            equivalence_class_path_in_adjacency(&adjacency, peer, &zero)
                        else {
                            continue;
                        };
                        return Ok(Some(EqualFromKnownDifferenceZeroBuiltinRuleProof {
                            cite_fact_id: equal_fact.fact_id,
                            difference_on_left,
                            zero_path: KnownEqualityPathProof::new(path),
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
