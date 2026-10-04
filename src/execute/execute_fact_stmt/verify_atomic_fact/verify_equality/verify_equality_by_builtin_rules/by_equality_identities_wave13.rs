//! Stage B wave 13: remaining basic Obj equality surfaces.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, QuantifierFreeFact};
use crate::ast::obj::{
    Abs, Add, AnonymousFn, ArithmeticOperator, Cart, ComplexAbs, ComplexOperator, Exp,
    ExpLogOperator, FamilyUnion, FiniteSeqSet, FnRange, FnSet, FunctionSpace, ImaginaryPart,
    Intersect, ListSet, Literal, Ln, Mul, Number, Obj, PowerSet, ProductShape, Range, ClosedRange,
    RealPart, SeqSet, SetFormer, SetMinus, SetOperator, StandardSet, Union,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin EulerEqualsExpOne: e = exp(1).
pub struct EulerEqualsExpOneBuiltinRuleProof {}

// Builtin LnOfEuler: ln(e) = 1.
pub struct LnOfEulerBuiltinRuleProof {}

// Builtin ReOfReal: re(a) = a when a $in R.
// Example: have a R; re(a) = a.
pub struct ReOfRealBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ImgOfReal: img(a) = 0 when a $in R.
// Example: have a R; img(a) = 0.
pub struct ImgOfRealBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ReOfRealPlusImagScaled: re(a + b * i) = a (a,b closed numerals or free with R).
// Example: re(2 + 3 * i) = 2.
pub struct ReOfRealPlusImagScaledBuiltinRuleProof {}

// Builtin ImgOfRealPlusImagScaled: img(a + b * i) = b.
// Example: img(2 + 3 * i) = 3.
pub struct ImgOfRealPlusImagScaledBuiltinRuleProof {}

// Builtin ComplexAbsOfReal: C_abs(a) = abs(a) for a real numeral (or equals a when a >= 0).
// Example: C_abs(3) = 3.
pub struct ComplexAbsOfNonnegRealBuiltinRuleProof {}

// Builtin ComplexAbsOfImagScaled: C_abs(a * i) = abs(a).
// Example: C_abs(3 * i) = 3.
pub struct ComplexAbsOfImagScaledBuiltinRuleProof {}

// Builtin ClosedRangeLiteralExpansion: closed_range(m, n) = {m,...,n} for integer literals.
// Example: closed_range(1, 3) = {1, 2, 3}.
pub struct ClosedRangeLiteralExpansionBuiltinRuleProof {}

// Builtin RangeLiteralExpansion: range(m, n) = {m,...,n-1} for integer literals.
// Example: range(1, 4) = {1, 2, 3}.
pub struct RangeLiteralExpansionBuiltinRuleProof {}

// Builtin PowerSetOfEmpty: power_set({}) = { {} }.
pub struct PowerSetOfEmptyBuiltinRuleProof {}

// Builtin PowerSetOfSingleton: power_set({a}) = { {}, {a} }.
// Example: power_set({1}) = { {}, {1} }.
pub struct PowerSetOfSingletonBuiltinRuleProof {}

// Builtin FamilyUnionOfEmpty: family_union({}) = {}.
pub struct FamilyUnionOfEmptyBuiltinRuleProof {}

// A family consisting of one set has exactly that set as its union.
pub struct FamilyUnionOfSingletonBuiltinRuleProof {}

// Every element of A occurs in its singleton subset; hence union(P(A))=A.
pub struct FamilyUnionOfPowerSetBuiltinRuleProof {}


// Builtin CartWithEmptyRight: cart(..., {}) = {}.
// Example: have A set; cart(A, {}) = {}.
pub struct CartWithEmptyFactorBuiltinRuleProof {}

// Builtin UnionOverIntersectDistributive:
//   union(A, intersect(B, C)) = intersect(union(A, B), union(A, C)).
pub struct UnionOverIntersectDistributiveBuiltinRuleProof {}

// Builtin SetMinusChainToUnion:
//   set_minus(set_minus(A, B), C) = set_minus(A, union(B, C)).
pub struct SetMinusChainToUnionBuiltinRuleProof {}

// Builtin FnRangeOfConstantAnonymousFn: fn_range(fn(...){c}) = {c} when body ignores params.
// Example: fn_range(fn(x R) R {1}) = {1}.
pub struct FnRangeOfConstantAnonymousFnBuiltinRuleProof {}

// Builtin SeqEqualsFnOnNPos: seq(S) = fn(x N+) S.
pub struct SeqEqualsFnOnNPosBuiltinRuleProof {}

// Builtin FiniteSeqEqualsFnOnOneBasedDomain:
//   finite_seq(S, n) = fn(x N+: x <= n) S.
// Also accepts the closed interval 1..n (and literal half-open 1..n+1).
// Example: finite_seq(R, 3) = fn(x closed_range(1, 3)) R.
pub struct FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {}

pub enum EqualityIdentitiesWave13BuiltinRuleProof {
    EulerEqualsExpOne(EulerEqualsExpOneBuiltinRuleProof),
    LnOfEuler(LnOfEulerBuiltinRuleProof),
    ReOfReal(ReOfRealBuiltinRuleProof),
    ImgOfReal(ImgOfRealBuiltinRuleProof),
    ReOfRealPlusImagScaled(ReOfRealPlusImagScaledBuiltinRuleProof),
    ImgOfRealPlusImagScaled(ImgOfRealPlusImagScaledBuiltinRuleProof),
    ComplexAbsOfNonnegReal(ComplexAbsOfNonnegRealBuiltinRuleProof),
    ComplexAbsOfImagScaled(ComplexAbsOfImagScaledBuiltinRuleProof),
    ClosedRangeLiteralExpansion(ClosedRangeLiteralExpansionBuiltinRuleProof),
    RangeLiteralExpansion(RangeLiteralExpansionBuiltinRuleProof),
    PowerSetOfEmpty(PowerSetOfEmptyBuiltinRuleProof),
    PowerSetOfSingleton(PowerSetOfSingletonBuiltinRuleProof),
    FamilyUnionOfEmpty(FamilyUnionOfEmptyBuiltinRuleProof),
    FamilyUnionOfSingleton(FamilyUnionOfSingletonBuiltinRuleProof),
    FamilyUnionOfPowerSet(FamilyUnionOfPowerSetBuiltinRuleProof),
    CartWithEmptyFactor(CartWithEmptyFactorBuiltinRuleProof),
    UnionOverIntersectDistributive(UnionOverIntersectDistributiveBuiltinRuleProof),
    SetMinusChainToUnion(SetMinusChainToUnionBuiltinRuleProof),
    FnRangeOfConstantAnonymousFn(FnRangeOfConstantAnonymousFnBuiltinRuleProof),
    SeqEqualsFnOnNPos(SeqEqualsFnOnNPosBuiltinRuleProof),
    FiniteSeqEqualsFnOnOneBasedDomain(FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave13(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave13BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if euler_equals_exp_one_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::EulerEqualsExpOne(
                        EulerEqualsExpOneBuiltinRuleProof {},
                    ),
                ));
            }
            if ln_of_euler_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave13BuiltinRuleProof::LnOfEuler(
                    LnOfEulerBuiltinRuleProof {},
                )));
            }
            if re_of_real_plus_imag_scaled_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::ReOfRealPlusImagScaled(
                        ReOfRealPlusImagScaledBuiltinRuleProof {},
                    ),
                ));
            }
            if img_of_real_plus_imag_scaled_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::ImgOfRealPlusImagScaled(
                        ImgOfRealPlusImagScaledBuiltinRuleProof {},
                    ),
                ));
            }
            if complex_abs_of_nonneg_real_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::ComplexAbsOfNonnegReal(
                        ComplexAbsOfNonnegRealBuiltinRuleProof {},
                    ),
                ));
            }
            if complex_abs_of_imag_scaled_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::ComplexAbsOfImagScaled(
                        ComplexAbsOfImagScaledBuiltinRuleProof {},
                    ),
                ));
            }
            if closed_range_literal_expansion_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::ClosedRangeLiteralExpansion(
                        ClosedRangeLiteralExpansionBuiltinRuleProof {},
                    ),
                ));
            }
            if range_literal_expansion_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::RangeLiteralExpansion(
                        RangeLiteralExpansionBuiltinRuleProof {},
                    ),
                ));
            }
            if power_set_of_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::PowerSetOfEmpty(
                        PowerSetOfEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if power_set_of_singleton_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::PowerSetOfSingleton(
                        PowerSetOfSingletonBuiltinRuleProof {},
                    ),
                ));
            }
            if family_union_of_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::FamilyUnionOfEmpty(
                        FamilyUnionOfEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if family_union_of_singleton_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave13BuiltinRuleProof::FamilyUnionOfSingleton(FamilyUnionOfSingletonBuiltinRuleProof {})));
            }
            if family_union_of_power_set_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave13BuiltinRuleProof::FamilyUnionOfPowerSet(FamilyUnionOfPowerSetBuiltinRuleProof {})));
            }
            if cart_with_empty_factor_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::CartWithEmptyFactor(
                        CartWithEmptyFactorBuiltinRuleProof {},
                    ),
                ));
            }
            if union_over_intersect_distributive_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::UnionOverIntersectDistributive(
                        UnionOverIntersectDistributiveBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_chain_to_union_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::SetMinusChainToUnion(
                        SetMinusChainToUnionBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_fn_range_of_constant(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::FnRangeOfConstantAnonymousFn(p),
                ));
            }
            if seq_equals_fn_on_n_pos_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::SeqEqualsFnOnNPos(
                        SeqEqualsFnOnNPosBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_seq_equals_fn_on_one_based_domain_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave13BuiltinRuleProof::FiniteSeqEqualsFnOnOneBasedDomain(
                        FiniteSeqEqualsFnOnOneBasedDomainBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_re_of_real(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave13BuiltinRuleProof::ReOfReal(p)));
            }
            if let Some(p) = self.try_img_of_real(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave13BuiltinRuleProof::ImgOfReal(p)));
            }
        }
        Ok(None)
    }

    fn try_re_of_real(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ReOfRealBuiltinRuleProof>> {
        let Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) = left else {
            return Ok(None);
        };
        if arg.ir() != right.ir() {
            return Ok(None);
        }
        let premise = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: arg.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ReOfRealBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_img_of_real(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ImgOfRealBuiltinRuleProof>> {
        let Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) = left
        else {
            return Ok(None);
        };
        if !is_zero_obj(right) {
            return Ok(None);
        }
        let premise = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: arg.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ImgOfRealBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_fn_range_of_constant(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<FnRangeOfConstantAnonymousFnBuiltinRuleProof>> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(FnRange { function })) = left else {
            return Ok(None);
        };
        let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = right else {
            return Ok(None);
        };
        if list.len() != 1 {
            return Ok(None);
        }
        let body = match function.as_ref() {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
                if !anonymous_fn_body_is_closed_literal(af) {
                    return Ok(None);
                }
                af.equal_to.as_ref().clone()
            }
            Obj::Identifier(id) => {
                let Some(af) = self.anonymous_fn_from_named_have_fn(id) else {
                    return Ok(None);
                };
                if !anonymous_fn_body_is_closed_literal(&af) {
                    return Ok(None);
                }
                af.equal_to.as_ref().clone()
            }
            _ => return Ok(None),
        };
        if list[0].ir() != body.ir() {
            return Ok(None);
        }
        Ok(Some(FnRangeOfConstantAnonymousFnBuiltinRuleProof {}))
    }

    fn anonymous_fn_from_named_have_fn(
        &self,
        head: &crate::ast::obj::IdentifierObj,
    ) -> Option<AnonymousFn> {
        use crate::exec_env::StoredIdentifierDefinition;
        let StoredIdentifierDefinition::HaveFnEqual((_, stmt)) =
            self.stored_identifier_definition_visible(head)?
        else {
            return None;
        };
        Some(stmt.equal_to_anonymous_fn.clone())
    }
}

fn is_empty_list_set(obj: &Obj) -> bool {
    matches!(obj, Obj::SetFormer(SetFormer::ListSet(ListSet { list })) if list.is_empty())
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_euler(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::EulerNumber(_)))
}

fn is_imaginary_unit(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::ImaginaryUnit(_)))
}

fn is_number_obj(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(_)))
}

fn literal_i128(obj: &Obj) -> Option<i128> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => {
            normalized_value.parse::<i128>().ok()
        }
        _ => None,
    }
}

fn number_obj(v: i128) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: v.to_string(),
    }))
}

fn list_set_of(objs: Vec<Obj>) -> Obj {
    Obj::SetFormer(SetFormer::ListSet(ListSet {
        list: objs.into_iter().map(Box::new).collect(),
    }))
}

fn euler_equals_exp_one_shape(left: &Obj, right: &Obj) -> bool {
    is_euler(left)
        && matches!(
            right,
            Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg })) if is_one_obj(arg.as_ref())
        )
}

fn ln_of_euler_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::ExpLogOperator(ExpLogOperator::Ln(ln)) if is_euler(ln.arg.as_ref())
    ) && is_one_obj(right)
}

fn match_imag_scaled_owned(obj: &Obj) -> Option<Obj> {
    if is_imaginary_unit(obj) {
        return Some(number_obj(1));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj else {
        return None;
    };
    if is_imaginary_unit(left.as_ref()) {
        return Some(right.as_ref().clone());
    }
    if is_imaginary_unit(right.as_ref()) {
        return Some(left.as_ref().clone());
    }
    None
}

fn match_real_plus_imag_scaled_owned(obj: &Obj) -> Option<(Obj, Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = obj else {
        return None;
    };
    for (real_side, imag_side) in [(left.as_ref(), right.as_ref()), (right.as_ref(), left.as_ref())]
    {
        if let Some(scale) = match_imag_scaled_owned(imag_side) {
            return Some((real_side.clone(), scale));
        }
    }
    None
}

fn re_of_real_plus_imag_scaled_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) = left else {
        return false;
    };
    let Some((real, _)) = match_real_plus_imag_scaled_owned(arg.as_ref()) else {
        return false;
    };
    real.ir() == right.ir()
}

fn img_of_real_plus_imag_scaled_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) = left else {
        return false;
    };
    let Some((_, scale)) = match_real_plus_imag_scaled_owned(arg.as_ref()) else {
        return false;
    };
    scale.ir() == right.ir()
}

fn complex_abs_of_nonneg_real_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs { arg })) = left else {
        return false;
    };
    let Some(v) = literal_i128(arg.as_ref()) else {
        return false;
    };
    if v < 0 {
        return false;
    }
    // C_abs(a) = a for a >= 0, or = abs(a)
    arg.ir() == right.ir()
        || matches!(
            right,
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: a })) if a.ir() == arg.ir()
        )
}

fn complex_abs_of_imag_scaled_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs { arg })) = left else {
        return false;
    };
    let Some(scale) = match_imag_scaled_owned(arg.as_ref()) else {
        return false;
    };
    let Some(v) = literal_i128(&scale) else {
        return false;
    };
    if v < 0 {
        // allow abs form only
        return matches!(
            right,
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: a })) if a.ir() == scale.ir()
        );
    }
    scale.ir() == right.ir()
        || matches!(
            right,
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: a })) if a.ir() == scale.ir()
        )
}

fn closed_range_literal_expansion_shape(range_side: &Obj, list_side: &Obj) -> bool {
    let Obj::SetFormer(SetFormer::ClosedRange(ClosedRange { start, end })) = range_side else {
        return false;
    };
    let Some(s) = literal_i128(start.as_ref()) else {
        return false;
    };
    let Some(e) = literal_i128(end.as_ref()) else {
        return false;
    };
    if s > e {
        return false;
    }
    let expected: Vec<Obj> = (s..=e).map(number_obj).collect();
    list_side.ir() == list_set_of(expected).ir()
}

fn range_literal_expansion_shape(range_side: &Obj, list_side: &Obj) -> bool {
    let Obj::SetFormer(SetFormer::Range(Range { start, end })) = range_side else {
        return false;
    };
    let Some(s) = literal_i128(start.as_ref()) else {
        return false;
    };
    let Some(e) = literal_i128(end.as_ref()) else {
        return false;
    };
    if s >= e {
        return false;
    }
    let expected: Vec<Obj> = (s..e).map(number_obj).collect();
    list_side.ir() == list_set_of(expected).ir()
}

fn power_set_of_empty_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::PowerSet(PowerSet { set })) = left else {
        return false;
    };
    if !is_empty_list_set(set.as_ref()) {
        return false;
    }
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = right else {
        return false;
    };
    list.len() == 1 && is_empty_list_set(list[0].as_ref())
}

fn power_set_of_singleton_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::PowerSet(PowerSet { set })) = left else {
        return false;
    };
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list: singleton })) = set.as_ref() else {
        return false;
    };
    if singleton.len() != 1 {
        return false;
    }
    let elem = singleton[0].as_ref();
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list: power })) = right else {
        return false;
    };
    if power.len() != 2 {
        return false;
    }
    let mut saw_empty = false;
    let mut saw_sing = false;
    for p in power {
        if is_empty_list_set(p.as_ref()) {
            saw_empty = true;
        } else if let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = p.as_ref() {
            if list.len() == 1 && list[0].ir() == elem.ir() {
                saw_sing = true;
            }
        }
    }
    saw_empty && saw_sing
}

// The outer equality WD has checked all children. Under Litex's set-coded
// foundation every WD object is a set, so these structural set identities
// have no additional truth premises and do not start recursive proof search.
fn family_union_of_singleton_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::FamilyUnion(union)) = left else { return false; };
    let Obj::SetFormer(SetFormer::ListSet(family)) = union.left.as_ref() else { return false; };
    let [set] = family.list.as_slice() else { return false; };
    set.ir() == right.ir()
}

fn family_union_of_power_set_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::FamilyUnion(union)) = left else { return false; };
    let Obj::SetOperator(SetOperator::PowerSet(power)) = union.left.as_ref() else { return false; };
    power.set.ir() == right.ir()
}

fn family_union_of_empty_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion { left: fam }))
            if is_empty_list_set(fam.as_ref())
    ) && is_empty_list_set(right)
}

fn cart_with_empty_factor_shape(cart_side: &Obj, empty_side: &Obj) -> bool {
    if !is_empty_list_set(empty_side) {
        return false;
    }
    let Obj::ProductShape(ProductShape::Cart(Cart { args })) = cart_side else {
        return false;
    };
    args.iter().any(|a| is_empty_list_set(a.as_ref()))
}

fn match_union(obj: &Obj) -> Option<&Union> {
    match obj {
        Obj::SetOperator(SetOperator::Union(u)) => Some(u),
        _ => None,
    }
}

fn match_intersect(obj: &Obj) -> Option<&Intersect> {
    match obj {
        Obj::SetOperator(SetOperator::Intersect(i)) => Some(i),
        _ => None,
    }
}

fn match_set_minus(obj: &Obj) -> Option<&SetMinus> {
    match obj {
        Obj::SetOperator(SetOperator::SetMinus(s)) => Some(s),
        _ => None,
    }
}

fn union_over_intersect_distributive_shape(left: &Obj, right: &Obj) -> bool {
    // union(A, intersect(B,C)) = intersect(union(A,B), union(A,C))
    let Some(u) = match_union(left) else {
        return false;
    };
    let Some(inter) = match_intersect(right) else {
        return false;
    };
    for (plain, inter_operand) in [(u.left.as_ref(), u.right.as_ref()), (u.right.as_ref(), u.left.as_ref())]
    {
        let Some(inner) = match_intersect(inter_operand) else {
            continue;
        };
        let b = inner.left.as_ref();
        let c = inner.right.as_ref();
        let Some(u1) = match_union(inter.left.as_ref()) else {
            continue;
        };
        let Some(u2) = match_union(inter.right.as_ref()) else {
            continue;
        };
        // each ui is union(plain, b) and union(plain, c) in some order
        let ok1 = (u1.left.ir() == plain.ir() && u1.right.ir() == b.ir())
            || (u1.right.ir() == plain.ir() && u1.left.ir() == b.ir())
            || (u1.left.ir() == plain.ir() && u1.right.ir() == c.ir())
            || (u1.right.ir() == plain.ir() && u1.left.ir() == c.ir());
        let ok2 = (u2.left.ir() == plain.ir() && u2.right.ir() == b.ir())
            || (u2.right.ir() == plain.ir() && u2.left.ir() == b.ir())
            || (u2.left.ir() == plain.ir() && u2.right.ir() == c.ir())
            || (u2.right.ir() == plain.ir() && u2.left.ir() == c.ir());
        if !(ok1 && ok2) {
            continue;
        }
        // cover both B and C
        let factors = [u1.left.ir(), u1.right.ir(), u2.left.ir(), u2.right.ir()];
        if factors.contains(&b.ir()) && factors.contains(&c.ir()) && factors.contains(&plain.ir())
        {
            return true;
        }
    }
    false
}

fn set_minus_chain_to_union_shape(left: &Obj, right: &Obj) -> bool {
    // set_minus(set_minus(A,B), C) = set_minus(A, union(B,C))
    let Some(outer) = match_set_minus(left) else {
        return false;
    };
    let Some(inner) = match_set_minus(outer.left.as_ref()) else {
        return false;
    };
    let Some(plain) = match_set_minus(right) else {
        return false;
    };
    if inner.left.ir() != plain.left.ir() {
        return false;
    }
    let Some(u) = match_union(plain.right.as_ref()) else {
        return false;
    };
    let b = inner.right.as_ref();
    let c = outer.right.as_ref();
    (u.left.ir() == b.ir() && u.right.ir() == c.ir())
        || (u.right.ir() == b.ir() && u.left.ir() == c.ir())
}

fn anonymous_fn_body_is_closed_literal(af: &AnonymousFn) -> bool {
    matches!(
        af.equal_to.as_ref(),
        Obj::Literal(_) | Obj::StandardSet(_)
    )
}

fn single_param_fn_set(fs: &FnSet) -> Option<(&Obj, &Obj)> {
    if !fs.dom_facts.is_empty() {
        return None;
    }
    if fs.set_bound_parameters.groups.len() != 1 {
        return None;
    }
    let g = &fs.set_bound_parameters.groups[0];
    if g.params.len() != 1 {
        return None;
    }
    Some((g.param_type.as_ref(), fs.ret_set.as_ref()))
}

fn seq_equals_fn_on_n_pos_shape(left: &Obj, right: &Obj) -> bool {
    let (seq_set, fn_set) = match (left, right) {
        (
            Obj::SetFormer(SetFormer::SeqSet(SeqSet { set })),
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
        ) => (set.as_ref(), fs),
        (
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
            Obj::SetFormer(SetFormer::SeqSet(SeqSet { set })),
        ) => (set.as_ref(), fs),
        _ => return false,
    };
    let Some((domain, ret)) = single_param_fn_set(fn_set) else {
        return false;
    };
    matches!(domain, Obj::StandardSet(StandardSet::NPos)) && ret.ir() == seq_set.ir()
}

fn finite_seq_equals_fn_on_one_based_domain_shape(left: &Obj, right: &Obj) -> bool {
    let (fseq, fs) = match (left, right) {
        (
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet { set, n })),
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
        ) => ( (set.as_ref(), n.as_ref()), fs),
        (
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet { set, n })),
        ) => ((set.as_ref(), n.as_ref()), fs),
        _ => return false,
    };
    let (carrier, n) = fseq;
    if fs.ret_set.ir() != carrier.ir() || fs.set_bound_parameters.groups.len() != 1 {
        return false;
    }
    let group = &fs.set_bound_parameters.groups[0];
    if group.params.len() != 1 {
        return false;
    }
    let domain = group.param_type.as_ref();
    if let Obj::StandardSet(StandardSet::NPos) = domain {
        let [QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(bound))] =
            fs.dom_facts.as_slice()
        else {
            return false;
        };
        let binder = Obj::Identifier(crate::ast::obj::IdentifierObj::from_bound_name(&group.params[0]));
        return bound.left.ir() == binder.ir() && bound.right.ir() == n.ir();
    }
    if !fs.dom_facts.is_empty() {
        return false;
    }
    match domain {
        Obj::SetFormer(SetFormer::ClosedRange(ClosedRange { start, end })) => {
            literal_i128(start.as_ref()) == Some(1) && end.ir() == n.ir()
        }
        Obj::SetFormer(SetFormer::Range(Range { start, end })) => {
            match (literal_i128(n), literal_i128(end.as_ref())) {
                (Some(length), Some(stop)) => literal_i128(start.as_ref()) == Some(1)
                    && length.checked_add(1) == Some(stop),
                _ => false,
            }
        }
        _ => false,
    }
}
