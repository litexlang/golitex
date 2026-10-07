//! Local scalar identities with checked domain and premise evidence.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator as A, Ceil, Floor, IntegerOperator, Lcm, Literal, Neg, Number,
    Obj, StandardSet, Sub, FiniteSetStat, SetFormer,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};
use crate::rational_expression::{exact_rational::EvalRational, NumberCompareResult};

pub enum ScalarIdentityBuiltinRuleProof {
    SignZeroReflection(SignZeroReflectionProof),
    FiniteSetMaxSelection(FiniteSetMaxSelectionBuiltinRuleProof),
    FiniteSetMinSelection(FiniteSetMinSelectionBuiltinRuleProof),
    AbsZeroArgument(AbsZeroArgumentBuiltinRuleProof),
    FloorNegation(FloorNegationBuiltinRuleProof),
    CeilNegation(CeilNegationBuiltinRuleProof),
    FloorIntegerTranslation(FloorIntegerTranslationBuiltinRuleProof),
    CeilIntegerTranslation(CeilIntegerTranslationBuiltinRuleProof),
    MinMaxAbsorption(MinMaxAbsorptionBuiltinRuleProof),
    MaxMinAbsorption(MaxMinAbsorptionBuiltinRuleProof),
    LcmZero(LcmZeroBuiltinRuleProof),
}
// sign(x)=0 implies x=0 for real x; retain the actual stored equality.
pub struct SignZeroReflectionProof {
    pub real_proof: VerifyFactResult,
    pub premise_proof: Box<EqualFactSearchedProof>,
}
impl SignZeroReflectionProof {
    pub fn new(real_proof: VerifyFactResult, premise_proof: EqualFactSearchedProof) -> Self {
        Self { real_proof, premise_proof: Box::new(premise_proof) }
    }
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
pub struct FiniteSetMaxSelectionBuiltinRuleProof {
    pub selected_index: usize,
    pub selected_member: Obj,
    pub comparisons: Vec<ExactExtremumComparison>,
}
pub struct FiniteSetMinSelectionBuiltinRuleProof {
    pub selected_index: usize,
    pub selected_member: Obj,
    pub comparisons: Vec<ExactExtremumComparison>,
}
pub struct ExactExtremumComparison {
    pub member: Obj,
    pub member_normal: Obj,
    pub selected_normal: Obj,
    pub ordering: NumberCompareResult,
}
impl ExactExtremumComparison {
    fn new(member: Obj, member_normal: Obj, selected_normal: Obj, ordering: NumberCompareResult) -> Self {
        Self { member, member_normal, selected_normal, ordering }
    }
}
impl ScalarIdentityBuiltinRuleProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SignZeroReflection(_) => "SignZeroReflection",
            Self::FiniteSetMaxSelection(_) => "FiniteSetMaxSelection",
            Self::FiniteSetMinSelection(_) => "FiniteSetMinSelection",
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
            // A displayed nonempty rational set has an extremal original member.
            // Example: finite_set_max({1/3,1/2}) = 1/2. Whole-object WD
            // retains finiteness, real membership and pairwise distinctness.
            if let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(extremum)) = left {
                if let Some((selected_index, selected_member, comparisons)) =
                    exact_extremum_selection(&extremum.set, right, NumberCompareResult::Greater)
                {
                    return Ok(Some(P::FiniteSetMaxSelection(FiniteSetMaxSelectionBuiltinRuleProof {
                        selected_index, selected_member, comparisons,
                    })));
                }
            }
            if let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(extremum)) = left {
                if let Some((selected_index, selected_member, comparisons)) =
                    exact_extremum_selection(&extremum.set, right, NumberCompareResult::Less)
                {
                    return Ok(Some(P::FiniteSetMinSelection(FiniteSetMinSelectionBuiltinRuleProof {
                        selected_index, selected_member, comparisons,
                    })));
                }
            }
            if is_zero(right) {
                let sign = Obj::ArithmeticOperator(A::Sign(crate::ast::obj::Sign { arg: Box::new(left.clone()) }));
                if let Some(premise_proof) = self.lookup_exact_property_obj_equality(&sign, right) {
                    let real_proof = self.scalar_member(left, StandardSet::R, state)?;
                    if !real_proof.is_failed() {
                        return Ok(Some(P::SignZeroReflection(SignZeroReflectionProof::new(real_proof, premise_proof))));
                    }
                }
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

fn exact_extremum_selection(
    set: &Obj,
    target: &Obj,
    preferred: NumberCompareResult,
) -> Option<(usize, Obj, Vec<ExactExtremumComparison>)> {
    let Obj::SetFormer(SetFormer::ListSet(list)) = set else { return None; };
    let first = list.list.first()?;
    let mut selected_index = 0;
    let mut selected_value = EvalRational::from_obj(first)?;
    for (index, member) in list.list.iter().enumerate().skip(1) {
        let value = EvalRational::from_obj(member)?;
        if value.compare(&selected_value)? == preferred {
            selected_index = index;
            selected_value = value;
        }
    }
    if EvalRational::from_obj(target)? != selected_value { return None; }
    let mut comparisons = Vec::new();
    for member in &list.list {
        let value = EvalRational::from_obj(member)?;
        let ordering = value.compare(&selected_value)?;
        if ordering == preferred { return None; }
        comparisons.push(ExactExtremumComparison::new(
            member.as_ref().clone(), value.to_obj(), selected_value.to_obj(), ordering,
        ));
    }
    Some((selected_index, list.list[selected_index].as_ref().clone(), comparisons))
}
