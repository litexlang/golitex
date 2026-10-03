//! Local scalar identities with checked domain and premise evidence.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator as A, Ceil, Floor, IntegerOperator, Lcm, Literal, Neg, Number,
    Obj, StandardSet, Sub,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub enum ScalarIdentityBuiltinRuleProof {
    AbsZeroArgument(AbsZeroArgumentBuiltinRuleProof),
    FloorNegation(FloorNegationBuiltinRuleProof),
    CeilNegation(CeilNegationBuiltinRuleProof),
    FloorIntegerTranslation(FloorIntegerTranslationBuiltinRuleProof),
    CeilIntegerTranslation(CeilIntegerTranslationBuiltinRuleProof),
    MinMaxAbsorption(MinMaxAbsorptionBuiltinRuleProof),
    MaxMinAbsorption(MaxMinAbsorptionBuiltinRuleProof),
    LcmZero(LcmZeroBuiltinRuleProof),
}
pub struct AbsZeroArgumentBuiltinRuleProof {
    pub premise_proof: Box<EqualFactSearchedProof>,
    pub real_proof: VerifyFactResult,
}
pub struct FloorNegationBuiltinRuleProof {}
pub struct CeilNegationBuiltinRuleProof {}
pub struct FloorIntegerTranslationBuiltinRuleProof {
    pub integer_proof: VerifyFactResult,
}
pub struct CeilIntegerTranslationBuiltinRuleProof {
    pub integer_proof: VerifyFactResult,
}
pub struct MinMaxAbsorptionBuiltinRuleProof {}
pub struct MaxMinAbsorptionBuiltinRuleProof {}
pub struct LcmZeroBuiltinRuleProof {}
impl ScalarIdentityBuiltinRuleProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::AbsZeroArgument(_) => "AbsZeroArgument",
            Self::FloorNegation(_) => "FloorNegation",
            Self::CeilNegation(_) => "CeilNegation",
            Self::FloorIntegerTranslation(_) => "FloorIntegerTranslation",
            Self::CeilIntegerTranslation(_) => "CeilIntegerTranslation",
            Self::MinMaxAbsorption(_) => "MinMaxAbsorption",
            Self::MaxMinAbsorption(_) => "MaxMinAbsorption",
            Self::LcmZero(_) => "LcmZero",
        }
    }
}
impl Runtime {
    pub(super) fn search_scalar_identity(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ScalarIdentityBuiltinRuleProof>> {
        use ScalarIdentityBuiltinRuleProof as P;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if is_zero(right) {
                let abs = Obj::ArithmeticOperator(A::Abs(Abs {
                    arg: Box::new(left.clone()),
                }));
                if let Some(premise_proof) = self.lookup_known_obj_equality(&abs, &zero()) {
                    let real_proof = self.scalar_member(left, StandardSet::R, state.clone())?;
                    if !real_proof.is_failed() {
                        return Ok(Some(P::AbsZeroArgument(AbsZeroArgumentBuiltinRuleProof {
                            premise_proof: Box::new(premise_proof),
                            real_proof,
                        })));
                    }
                }
                if let Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left: a, right: b })) = left
                {
                    if is_zero(a) || is_zero(b) {
                        return Ok(Some(P::LcmZero(LcmZeroBuiltinRuleProof {})));
                    }
                }
            }
            if let Some(arg) = rounded(left, true) {
                if let (Some(x), Some(inner)) = (negative_arg(arg), negative_arg(right)) {
                    if rounded(inner, false).is_some_and(|y| y.ir() == x.ir()) {
                        return Ok(Some(P::FloorNegation(FloorNegationBuiltinRuleProof {})));
                    }
                }
            }
            if let Some(arg) = rounded(left, false) {
                if let (Some(x), Some(inner)) = (negative_arg(arg), negative_arg(right)) {
                    if rounded(inner, true).is_some_and(|y| y.ir() == x.ir()) {
                        return Ok(Some(P::CeilNegation(CeilNegationBuiltinRuleProof {})));
                    }
                }
            }
            for floor in [true, false] {
                let Some(Obj::ArithmeticOperator(A::Add(Add { left: x, right: n }))) =
                    rounded(left, floor)
                else {
                    continue;
                };
                let Obj::ArithmeticOperator(A::Add(Add {
                    left: r1,
                    right: r2,
                })) = right
                else {
                    continue;
                };
                for (x, n) in [(x.as_ref(), n.as_ref()), (n.as_ref(), x.as_ref())] {
                    let shape = [(r1.as_ref(), r2.as_ref()), (r2.as_ref(), r1.as_ref())]
                        .iter()
                        .any(|(r, k)| {
                            k.ir() == n.ir()
                                && rounded(r, floor).is_some_and(|rx| rx.ir() == x.ir())
                        });
                    if !shape {
                        continue;
                    }
                    let integer_proof = self.scalar_member(n, StandardSet::Z, state.clone())?;
                    if !integer_proof.is_failed() {
                        return Ok(Some(if floor {
                            P::FloorIntegerTranslation(FloorIntegerTranslationBuiltinRuleProof {
                                integer_proof,
                            })
                        } else {
                            P::CeilIntegerTranslation(CeilIntegerTranslationBuiltinRuleProof {
                                integer_proof,
                            })
                        }));
                    }
                }
            }
            for minimum in [true, false] {
                let Some((a, b)) = extrema_args(left, minimum) else {
                    continue;
                };
                for (plain, nested) in [(a, b), (b, a)] {
                    if plain.ir() != right.ir() {
                        continue;
                    }
                    if let Some((x, y)) = extrema_args(nested, !minimum) {
                        if plain.ir() == x.ir() || plain.ir() == y.ir() {
                            return Ok(Some(if minimum {
                                P::MinMaxAbsorption(MinMaxAbsorptionBuiltinRuleProof {})
                            } else {
                                P::MaxMinAbsorption(MaxMinAbsorptionBuiltinRuleProof {})
                            }));
                        }
                    }
                }
            }
        }
        Ok(None)
    }
    fn scalar_member(
        &mut self,
        obj: &Obj,
        set: StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let premise = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(set),
            line_file: None,
        }));
        self.verify_builtin_rule_premise(&premise, state)
    }
}
fn rounded(obj: &Obj, floor: bool) -> Option<&Obj> {
    match (obj, floor) {
        (Obj::ArithmeticOperator(A::Floor(Floor { arg })), true)
        | (Obj::ArithmeticOperator(A::Ceil(Ceil { arg })), false) => Some(arg),
        _ => None,
    }
}
fn extrema_args(obj: &Obj, minimum: bool) -> Option<(&Obj, &Obj)> {
    match (obj, minimum) {
        (Obj::ArithmeticOperator(A::Min(m)), true) => Some((&m.left, &m.right)),
        (Obj::ArithmeticOperator(A::Max(m)), false) => Some((&m.left, &m.right)),
        _ => None,
    }
}
fn negative_arg(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(A::Neg(Neg { arg })) => Some(arg),
        Obj::ArithmeticOperator(A::Sub(Sub { left, right })) if is_zero(left) => Some(right),
        _ => None,
    }
}
fn zero() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }))
}
fn is_zero(obj: &Obj) -> bool {
    matches!(obj,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0")
}
