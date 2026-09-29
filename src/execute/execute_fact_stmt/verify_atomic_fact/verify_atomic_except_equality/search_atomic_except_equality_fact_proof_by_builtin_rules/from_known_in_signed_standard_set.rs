//! Cite known signed/nonzero standard-set membership to prove sign facts.
//!
//! B1 boundary: carrier → sign is verify-time only (not eager infer).

use crate::ast::fact::{AtomicFact, InFact, LessEqualFact, LessFact, NotEqualFact};
use crate::ast::names::AtomicName;
use crate::ast::obj::{Literal, Number, Obj, StandardSet};
use crate::parse::keywords::IN;
use crate::runtime::{FactId, Runtime};

// Builtin: `0 < x` from known `x $in Q+` / `R+` / `N+`.
// Example: have a R+; 0 < a.
pub struct FromKnownInPositiveStandardSetBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

// Builtin: `x < 0` from known `x $in Q-` / `Z-` / `R-`.
// Example: have a R-; a < 0.
pub struct FromKnownInNegativeStandardSetBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

// Builtin: `x != 0` from known `x $in Q*` / `Z*` / `R*` / `C*`.
// Example: have a R*; a != 0.
pub struct FromKnownInNonzeroStandardSetBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub(crate) fn try_from_known_in_positive_standard_set(
        &self,
        fact: &LessFact,
    ) -> Option<FromKnownInPositiveStandardSetBuiltinRuleProof> {
        if !is_literal_zero(&fact.left) {
            return None;
        }
        let cite_fact_id = self.known_in_one_of_standard_sets(
            &fact.right,
            &[StandardSet::QPos, StandardSet::RPos, StandardSet::NPos],
        )?;
        Some(FromKnownInPositiveStandardSetBuiltinRuleProof { cite_fact_id })
    }

    pub(crate) fn try_from_known_in_negative_standard_set(
        &self,
        fact: &LessFact,
    ) -> Option<FromKnownInNegativeStandardSetBuiltinRuleProof> {
        if !is_literal_zero(&fact.right) {
            return None;
        }
        let cite_fact_id = self.known_in_one_of_standard_sets(
            &fact.left,
            &[StandardSet::QNeg, StandardSet::ZNeg, StandardSet::RNeg],
        )?;
        Some(FromKnownInNegativeStandardSetBuiltinRuleProof { cite_fact_id })
    }

    // `0 <= x` from known `x $in Q+` / `R+` / `N+`.
    // Dedicated LessEqual rule (do not share the LessFact proof struct).
    pub(crate) fn try_less_equal_from_known_in_positive_standard_set(
        &self,
        fact: &LessEqualFact,
    ) -> Option<FactId> {
        if !is_literal_zero(&fact.left) {
            return None;
        }
        self.known_in_one_of_standard_sets(
            &fact.right,
            &[StandardSet::QPos, StandardSet::RPos, StandardSet::NPos],
        )
    }

    // `x <= 0` from known `x $in Q-` / `Z-` / `R-`.
    pub(crate) fn try_less_equal_from_known_in_negative_standard_set(
        &self,
        fact: &LessEqualFact,
    ) -> Option<FactId> {
        if !is_literal_zero(&fact.right) {
            return None;
        }
        self.known_in_one_of_standard_sets(
            &fact.left,
            &[StandardSet::QNeg, StandardSet::ZNeg, StandardSet::RNeg],
        )
    }

    pub(crate) fn try_from_known_in_nonzero_standard_set(
        &self,
        fact: &NotEqualFact,
    ) -> Option<FromKnownInNonzeroStandardSetBuiltinRuleProof> {
        let (element, zero_side) = if is_literal_zero(&fact.right) {
            (&fact.left, &fact.right)
        } else if is_literal_zero(&fact.left) {
            (&fact.right, &fact.left)
        } else {
            return None;
        };
        let _ = zero_side;
        let cite_fact_id = self.known_in_one_of_standard_sets(
            element,
            &[
                StandardSet::QStar,
                StandardSet::ZStar,
                StandardSet::RStar,
                StandardSet::CStar,
            ],
        )?;
        Some(FromKnownInNonzeroStandardSetBuiltinRuleProof { cite_fact_id })
    }

    pub(crate) fn known_in_one_of_standard_sets(
        &self,
        element: &Obj,
        sets: &[StandardSet],
    ) -> Option<FactId> {
        let key = (AtomicName::Plain { name: IN.into() }, true);
        let element_ir = element.ir();
        let set_irs: Vec<_> = sets
            .iter()
            .map(|s| Obj::StandardSet(s.clone()).ir())
            .collect();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::InFact(InFact {
                    fact_id,
                    element: el,
                    set,
                    ..
                }) = known
                {
                    if el.ir() != element_ir {
                        continue;
                    }
                    let set_ir = set.ir();
                    if set_irs.iter().any(|s| s == &set_ir) {
                        return Some(*fact_id);
                    }
                }
            }
        }
        None
    }
}

fn is_literal_zero(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    )
}
