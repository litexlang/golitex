use crate::ast::fact::{
    AtomicFact, Fact, InFact, LessEqualFact, LessFact, NotEqualFact,
};
use crate::ast::obj::{Literal, Number, Obj, StandardSet};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactSignedStandardSetSignResult,
    StoreFactAndInferResult,
};

impl Runtime {
    // When: `x $in N` / `N+|Q+|R+` / `Q-|Z-|R-` / `Q*|Z*|R*|C*`.
    // Infers: nonnegativity / positivity(+weak) / negativity(+weak) / nonzero.
    // Example: `have a R+` ⇒ store `0 < a` and `0 <= a`.
    pub(super) fn infer_in_fact_signed_standard_set_rules(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let Obj::StandardSet(set) = &in_fact.set else {
            return Ok(Vec::new());
        };
        let Some(derived) = self.infer_signed_standard_set_sign(in_fact, set)? else {
            return Ok(Vec::new());
        };
        Ok(vec![
            InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(
                InferInFactSignedStandardSetSignResult { derived },
            ),
        ])
    }
}

impl Runtime {
    fn infer_signed_standard_set_sign(
        &mut self,
        in_fact: &InFact,
        set: &StandardSet,
    ) -> RuntimeResult<Option<Vec<StoreFactAndInferResult>>> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();
        let zero = zero_obj();
        let mut derived = Vec::new();

        match set {
            StandardSet::N => {
                // `x $in N` ⇒ `0 <= x`.
                let fact_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id,
                        left: zero,
                        right: element,
                        line_file: lf,
                    }),
                ))?);
            }
            StandardSet::NPos | StandardSet::QPos | StandardSet::RPos => {
                // `x $in R+` / `Q+` / `N+` ⇒ `0 < x` and `0 <= x`.
                let strict_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::LessFact(LessFact {
                        fact_id: strict_id,
                        left: zero.clone(),
                        right: element.clone(),
                        line_file: lf.clone(),
                    }),
                ))?);
                let weak_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id: weak_id,
                        left: zero,
                        right: element,
                        line_file: lf,
                    }),
                ))?);
            }
            StandardSet::QNeg | StandardSet::ZNeg | StandardSet::RNeg => {
                // `x $in R-` / `Q-` / `Z-` ⇒ `x < 0` and `x <= 0`.
                let strict_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::LessFact(LessFact {
                        fact_id: strict_id,
                        left: element.clone(),
                        right: zero.clone(),
                        line_file: lf.clone(),
                    }),
                ))?);
                let weak_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id: weak_id,
                        left: element,
                        right: zero,
                        line_file: lf,
                    }),
                ))?);
            }
            StandardSet::QStar | StandardSet::ZStar | StandardSet::RStar | StandardSet::CStar => {
                // `x $in R*` / … ⇒ `x != 0`.
                let fact_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(
                    AtomicFact::NotEqualFact(NotEqualFact {
                        fact_id,
                        left: element,
                        right: zero,
                        line_file: lf,
                    }),
                ))?);
            }
            StandardSet::Q | StandardSet::Z | StandardSet::R | StandardSet::C => {
                return Ok(None);
            }
        }

        Ok(Some(derived))
    }
}

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}
