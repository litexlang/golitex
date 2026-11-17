use super::super::equivalence_class_graph::EquivalentObjectCandidates;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, Literal, Number, Obj, Sub};
use crate::execute::execute_fact_stmt::VerifyState;
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
        let mut candidates = EquivalentObjectCandidates::new(&zero);
        for scope in (0..self.execution_environments_stack.len()).rev() {
            while let Some(index) = candidates.next_in_scope(self, scope) {
                let Some((x, y)) = match_sub(&candidates.objects[index]) else {
                    continue;
                };
                let xy = x.ir() == a_ir && y.ir() == b_ir;
                let yx = x.ir() == b_ir && y.ir() == a_ir;
                if !xy && !yx {
                    continue;
                }
                let mut path = candidates.path(index);
                let (_, difference, cite_fact_id) = path.pop().expect("non-original class member");
                let Some(crate::ast::fact::Fact::AtomicFact(
                    crate::ast::fact::AtomicFact::EqualFact(source),
                )) = self.fact_by_id_in_stack(cite_fact_id)
                else {
                    continue;
                };
                let difference_on_left = source.left.ir() == difference.ir();
                let zero_path = path
                    .into_iter()
                    .rev()
                    .map(|(from, to, id)| (to, from, id))
                    .collect();
                return Ok(Some(EqualFromKnownDifferenceZeroBuiltinRuleProof {
                    cite_fact_id,
                    difference_on_left,
                    zero_path: KnownEqualityPathProof::new(zero_path),
                }));
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
