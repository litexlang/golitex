use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, GreaterEqualFact, InFact, LessFact, NotEqualFact,
};
use crate::new_pipeline::ast::obj::{Literal, Number, Obj, StandardSet};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactNaturalNonnegativeResult,
    InferInFactNegativeStandardSetResult, InferInFactNonzeroStandardSetResult,
    InferInFactPositiveStandardSetResult,
};

impl Runtime {
    // When: `x $in N` / `Q+|R+|N+` / `Q-|Z-|R-` / `Q*|Z*|R*|C*`.
    // Infers: `x >= 0` / `0 < x` / `x < 0` / `x != 0`.
    // Example: `k $in N` ⇒ `k >= 0`; `a $in R+` ⇒ `0 < a`.
    pub(super) fn infer_in_fact_standard_set_rules(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let Obj::StandardSet(set) = &in_fact.set else {
            return Ok(Vec::new());
        };
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let lf = in_fact.line_file.clone();
        match set {
            StandardSet::N => {
                let fact_id = self.global_ids.allocate_fact_id();
                let atomic = AtomicFact::GreaterEqualFact(GreaterEqualFact {
                    fact_id,
                    left: in_fact.element.clone(),
                    right: zero,
                    line_file: lf,
                });
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
                Ok(vec![
                    InferAtomicExceptEqualityResult::InFactNaturalNonnegative(
                        InferInFactNaturalNonnegativeResult { derived },
                    ),
                ])
            }
            StandardSet::QPos | StandardSet::RPos | StandardSet::NPos => {
                let fact_id = self.global_ids.allocate_fact_id();
                let atomic = AtomicFact::LessFact(LessFact {
                    fact_id,
                    left: zero,
                    right: in_fact.element.clone(),
                    line_file: lf,
                });
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
                Ok(vec![
                    InferAtomicExceptEqualityResult::InFactPositiveStandardSet(
                        InferInFactPositiveStandardSetResult { derived },
                    ),
                ])
            }
            StandardSet::QNeg | StandardSet::ZNeg | StandardSet::RNeg => {
                let fact_id = self.global_ids.allocate_fact_id();
                let atomic = AtomicFact::LessFact(LessFact {
                    fact_id,
                    left: in_fact.element.clone(),
                    right: zero,
                    line_file: lf,
                });
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
                Ok(vec![
                    InferAtomicExceptEqualityResult::InFactNegativeStandardSet(
                        InferInFactNegativeStandardSetResult { derived },
                    ),
                ])
            }
            StandardSet::QStar | StandardSet::ZStar | StandardSet::RStar | StandardSet::CStar => {
                let fact_id = self.global_ids.allocate_fact_id();
                let atomic = AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id,
                    left: in_fact.element.clone(),
                    right: zero,
                    line_file: lf,
                });
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(atomic))?);
                Ok(vec![
                    InferAtomicExceptEqualityResult::InFactNonzeroStandardSet(
                        InferInFactNonzeroStandardSetResult { derived },
                    ),
                ])
            }
            StandardSet::Q | StandardSet::Z | StandardSet::R | StandardSet::C => Ok(Vec::new()),
        }
    }
}
