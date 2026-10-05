//! Stage B wave 14: P1/P2 Obj equality builtins (index_*, seq0, set_builder empty,
//! C_abs^2, exp add, log base-power, re/img product, trig add, reduce single).
//!
//! One matcher ↔ one dedicated proof struct.
//! No `family_intersect({}) = {}`: absolute empty ∩ is the universe class;
//! Litex keeps empty-index ∩ on `index_intersect({}, X, A) = X`.

use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, LessEqualFact, LessFact, QuantifierFreeFact,
};
use crate::ast::obj::{
    Add, AnonymousFn, ArithmeticOperator, ComplexAbs, ComplexOperator, Cos, Div, Exp,
    ExpLogOperator, FiniteSeqSet, FnObj, FnObjHead, FnSet, FunctionSpace, ImaginaryPart,
    IndexCart, IndexIntersect, IndexUnion, IteratedOperator, ListSet, Literal, Log, Mul, Number,
    Obj, Pow, RealPart, Reduce, SetFormer, SetOperator, Sin, StandardSet, Sub, TrigOperator,
};
use crate::ast::names::BoundName;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin IndexUnionEmptyIndex: index_union({}, X, A) = {}.
// Example: have A fn({}) power_set(N); index_union({}, N, A) = {}.
pub struct IndexUnionEmptyIndexBuiltinRuleProof {}

// Builtin IndexIntersectEmptyIndex: index_intersect({}, X, A) = X.
// Example: have A fn({}) power_set(N); index_intersect({}, N, A) = N.
pub struct IndexIntersectEmptyIndexBuiltinRuleProof {}

// Builtin IndexCartEmptyIndex: index_cart({}, S, g) = {{}}.
// Example: have g fn({}) power_set(N); index_cart({}, N, g) = { {} }.
pub struct IndexCartEmptyIndexBuiltinRuleProof {}

// Builtin IndexUnionSingleton: index_union({a}, X, A) = A(a).
// Example: have A fn(N) power_set(N); index_union({1}, N, A) = A(1).
pub struct IndexUnionSingletonBuiltinRuleProof {}

// Builtin FiniteSeqZeroEqualsFnOnEmpty: finite_seq(S, 0) = fn(x {}) S.
// Example: finite_seq(R, 0) = fn(x {}) R.
pub struct FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {}

// Builtin SetBuilderObviouslyEmpty: contradictory N-builder equals {}.
// Example: {x N: x < 0} = {}.
pub struct SetBuilderObviouslyEmptyBuiltinRuleProof {}

// Builtin ComplexAbsSquaredOfRectForm: C_abs(a + b*i)^2 = a^2 + b^2.
// Example: have a R; have b R; C_abs(a + b * i)^2 = a^2 + b^2.
pub struct ComplexAbsSquaredOfRectFormBuiltinRuleProof {}

// Builtin ExpOfSum: exp(a + b) = exp(a) * exp(b).
// Example: have a R; have b R; exp(a + b) = exp(a) * exp(b).
pub struct ExpOfSumBuiltinRuleProof {}

// Builtin LogBasePower: a>0, a!=1, real b!=0, c>0 => log(a^b,c)=log(a,c)/b.
// Example: have c N+; log(2^3, c) = log(2, c) / 3.
pub struct LogBasePowerBuiltinRuleProof {
    pub base_proof: super::log_algebra_base_proof::LogAlgebraBaseProof,
    pub exponent_real: VerifyFactResult,
    pub exponent_nonzero: VerifyFactResult,
    pub argument_positive_proof: VerifyFactResult,
}

// Builtin ReOfProduct: re(z*w) = re(z)*re(w) - img(z)*img(w).
pub struct ReOfProductBuiltinRuleProof {}

// Builtin ImgOfProduct: img(z*w) = re(z)*img(w) + img(z)*re(w).
pub struct ImgOfProductBuiltinRuleProof {}

// Builtin SinOfSum: sin(a+b) = sin(a)*cos(b) + cos(a)*sin(b).
pub struct SinOfSumBuiltinRuleProof {}

// Builtin CosOfSum: cos(a+b) = cos(a)*cos(b) - sin(a)*sin(b).
pub struct CosOfSumBuiltinRuleProof {}

// Builtin ReduceSingleTermWithAddZero:
//   start = end ⇒ reduce(s, s, f, add, 0) = f(s).
// Example: reduce(2, 2, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2.
pub struct ReduceSingleTermWithAddZeroBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave14BuiltinRuleProof {
    IndexUnionEmptyIndex(IndexUnionEmptyIndexBuiltinRuleProof),
    IndexIntersectEmptyIndex(IndexIntersectEmptyIndexBuiltinRuleProof),
    IndexCartEmptyIndex(IndexCartEmptyIndexBuiltinRuleProof),
    IndexUnionSingleton(IndexUnionSingletonBuiltinRuleProof),
    FiniteSeqZeroEqualsFnOnEmpty(FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof),
    SetBuilderObviouslyEmpty(SetBuilderObviouslyEmptyBuiltinRuleProof),
    ComplexAbsSquaredOfRectForm(ComplexAbsSquaredOfRectFormBuiltinRuleProof),
    ExpOfSum(ExpOfSumBuiltinRuleProof),
    LogBasePower(LogBasePowerBuiltinRuleProof),
    ReOfProduct(ReOfProductBuiltinRuleProof),
    ImgOfProduct(ImgOfProductBuiltinRuleProof),
    SinOfSum(SinOfSumBuiltinRuleProof),
    CosOfSum(CosOfSumBuiltinRuleProof),
    ReduceSingleTermWithAddZero(ReduceSingleTermWithAddZeroBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave14(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave14BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if index_union_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::IndexUnionEmptyIndex(
                        IndexUnionEmptyIndexBuiltinRuleProof {},
                    ),
                ));
            }
            if index_intersect_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::IndexIntersectEmptyIndex(
                        IndexIntersectEmptyIndexBuiltinRuleProof {},
                    ),
                ));
            }
            if index_cart_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::IndexCartEmptyIndex(
                        IndexCartEmptyIndexBuiltinRuleProof {},
                    ),
                ));
            }
            if index_union_singleton_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::IndexUnionSingleton(
                        IndexUnionSingletonBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_seq_zero_equals_fn_on_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::FiniteSeqZeroEqualsFnOnEmpty(
                        FiniteSeqZeroEqualsFnOnEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if set_builder_obviously_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::SetBuilderObviouslyEmpty(
                        SetBuilderObviouslyEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if complex_abs_squared_of_rect_form_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::ComplexAbsSquaredOfRectForm(
                        ComplexAbsSquaredOfRectFormBuiltinRuleProof {},
                    ),
                ));
            }
            if exp_of_sum_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::ExpOfSum(
                    ExpOfSumBuiltinRuleProof {},
                )));
            }
            if let Some(p) = self.try_log_base_power(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::LogBasePower(p)));
            }
            if re_of_product_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::ReOfProduct(
                    ReOfProductBuiltinRuleProof {},
                )));
            }
            if img_of_product_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::ImgOfProduct(
                    ImgOfProductBuiltinRuleProof {},
                )));
            }
            if sin_of_sum_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::SinOfSum(
                    SinOfSumBuiltinRuleProof {},
                )));
            }
            if cos_of_sum_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave14BuiltinRuleProof::CosOfSum(
                    CosOfSumBuiltinRuleProof {},
                )));
            }
            if let Some(p) = self.try_reduce_single_term_with_add_zero(left, right, child.clone())?
            {
                return Ok(Some(
                    EqualityIdentitiesWave14BuiltinRuleProof::ReduceSingleTermWithAddZero(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_log_base_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogBasePowerBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Some((pow_base, pow_exp)) = match_pow(base) else {
            return Ok(None);
        };
        let Some((quot_num, quot_den)) = match_div(right) else {
            return Ok(None);
        };
        let Some((log2_base, log2_arg)) = match_log(quot_num) else {
            return Ok(None);
        };
        if pow_base.ir() != log2_base.ir()
            || arg.ir() != log2_arg.ir()
            || pow_exp.ir() != quot_den.ir()
        {
            return Ok(None);
        }
        let Some(base_proof) = self.verify_log_algebra_base_guard(pow_base, verify_state)? else { return Ok(None); };
        let real: Fact = crate::ast::fact::InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: pow_exp.clone(),
            set: Obj::StandardSet(StandardSet::R), line_file: None,
        }.into();
        let exponent_real = self.verify_builtin_rule_premise(&real, verify_state)?;
        if exponent_real.is_failed() { return Ok(None); }
        let exponent_nonzero = self.verify_order_nonzero(pow_exp, verify_state)?;
        if exponent_nonzero.is_failed() { return Ok(None); }
        let argument_positive_proof = self.verify_log_algebra_positive(arg, verify_state)?;
        if argument_positive_proof.is_failed() { return Ok(None); }
        Ok(Some(LogBasePowerBuiltinRuleProof { base_proof, exponent_real, exponent_nonzero, argument_positive_proof }))
    }

    fn try_reduce_single_term_with_add_zero(
        &mut self,
        reduce_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ReduceSingleTermWithAddZeroBuiltinRuleProof>> {
        let Some(reduce) = match_reduce(reduce_side) else {
            return Ok(None);
        };
        if reduce.start.ir() != reduce.end.ir() {
            return Ok(None);
        }
        if !is_zero_obj(reduce.seed.as_ref()) {
            return Ok(None);
        }
        if !is_binary_add_anonymous_fn(reduce.op.as_ref()) {
            return Ok(None);
        }
        let Some(applied) = apply_fn_one_arg(reduce.func.as_ref(), reduce.start.as_ref().clone())
        else {
            return Ok(None);
        };
        let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: applied,
            right: other.clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ReduceSingleTermWithAddZeroBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }
}

fn index_union_empty_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::SetOperator(SetOperator::IndexUnion(IndexUnion { index_set, .. }))
            if is_empty_list_set(index_set.as_ref())
    ) && is_empty_list_set(right)
}

fn index_intersect_empty_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::IndexIntersect(IndexIntersect {
        index_set,
        ambient_set,
        ..
    })) = left
    else {
        return false;
    };
    is_empty_list_set(index_set.as_ref()) && ambient_set.ir() == right.ir()
}

fn index_cart_empty_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::IndexCart(IndexCart { index_set, .. })) = left else {
        return false;
    };
    if !is_empty_list_set(index_set.as_ref()) {
        return false;
    }
    // Unique empty choice function: singleton of the empty list-set.
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = right else {
        return false;
    };
    list.len() == 1 && is_empty_list_set(list[0].as_ref())
}

fn index_union_singleton_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::SetOperator(SetOperator::IndexUnion(IndexUnion {
        index_set,
        family_fn,
        ..
    })) = left
    else {
        return false;
    };
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = index_set.as_ref() else {
        return false;
    };
    if list.len() != 1 {
        return false;
    }
    let Some(applied) = apply_fn_one_arg(family_fn.as_ref(), list[0].as_ref().clone()) else {
        return false;
    };
    applied.ir() == right.ir()
}

fn finite_seq_zero_equals_fn_on_empty_shape(left: &Obj, right: &Obj) -> bool {
    let (fseq, fs) = match (left, right) {
        (
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet { set, n })),
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
        ) => ((set.as_ref(), n.as_ref()), fs),
        (
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)),
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet { set, n })),
        ) => ((set.as_ref(), n.as_ref()), fs),
        _ => return false,
    };
    let (carrier, n) = fseq;
    if !is_zero_obj(n) {
        return false;
    }
    if !fs.dom_facts.is_empty() || fs.set_bound_parameters.groups.len() != 1 {
        return false;
    }
    let g = &fs.set_bound_parameters.groups[0];
    if g.params.len() != 1 {
        return false;
    }
    is_empty_list_set(g.param_type.as_ref()) && fs.ret_set.ir() == carrier.ir()
}

fn set_builder_obviously_empty_shape(left: &Obj, right: &Obj) -> bool {
    if !is_empty_list_set(right) {
        return false;
    }
    let Obj::SetFormer(SetFormer::SetBuilder(builder)) = left else {
        return false;
    };
    let param_ok = matches!(
        builder.param_set.as_ref(),
        Obj::StandardSet(StandardSet::N | StandardSet::NPos)
    );
    if !param_ok || builder.facts.len() != 1 {
        return false;
    }
    let bound = bound_name_obj(&builder.param_binding);
    match &builder.facts[0] {
        QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(LessFact { left, right, .. })) => {
            left.ir() == bound.ir() && is_zero_obj(right)
        }
        QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
            left,
            right,
            ..
        })) => left.ir() == bound.ir() && is_neg_one_obj(right),
        _ => false,
    }
}

fn complex_abs_squared_of_rect_form_shape(left: &Obj, right: &Obj) -> bool {
    // C_abs(a + b * i)^2 = a^2 + b^2  (also a + i * b)
    let Some((abs_arg, two)) = match_pow(left) else {
        return false;
    };
    if !is_number_two(two) {
        return false;
    }
    let Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs { arg })) = abs_arg else {
        return false;
    };
    let Some((a, bi)) = match_add(arg) else {
        return false;
    };
    let Some(b) = imag_scaled_coeff(bi) else {
        return false;
    };
    let Some((a2, b2)) = match_add(right) else {
        return false;
    };
    square_of(a2) == Some(a) && square_of(b2) == Some(b)
        || square_of(a2) == Some(b) && square_of(b2) == Some(a)
}

fn imag_scaled_coeff(obj: &Obj) -> Option<&Obj> {
    let Some((l, r)) = match_mul(obj) else {
        return None;
    };
    if matches!(r, Obj::Literal(Literal::ImaginaryUnit(_))) {
        return Some(l);
    }
    if matches!(l, Obj::Literal(Literal::ImaginaryUnit(_))) {
        return Some(r);
    }
    None
}

fn exp_of_sum_shape(left: &Obj, right: &Obj) -> bool {
    let Some(exp_arg) = match_exp(left) else {
        return false;
    };
    let Some((a, b)) = match_add(exp_arg) else {
        return false;
    };
    let Some((l, r)) = match_mul(right) else {
        return false;
    };
    (match_exp(l) == Some(a) && match_exp(r) == Some(b))
        || (match_exp(l) == Some(b) && match_exp(r) == Some(a))
}

fn re_of_product_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) = left else {
        return false;
    };
    let Some((z, w)) = match_mul(arg) else {
        return false;
    };
    // re(z)*re(w) - img(z)*img(w)
    let Some((prod1, prod2)) = match_sub(right) else {
        return false;
    };
    let Some((z_re, w_re)) = match_mul(prod1) else {
        return false;
    };
    let Some((z_img, w_img)) = match_mul(prod2) else {
        return false;
    };
    is_re_of(z_re, z)
        && is_re_of(w_re, w)
        && is_img_of(z_img, z)
        && is_img_of(w_img, w)
}

fn img_of_product_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) = left else {
        return false;
    };
    let Some((z, w)) = match_mul(arg) else {
        return false;
    };
    // re(z)*img(w) + img(z)*re(w)
    let Some((prod1, prod2)) = match_add(right) else {
        return false;
    };
    let pairs = [
        (prod1, prod2),
        (prod2, prod1),
    ];
    for (p1, p2) in pairs {
        let Some((a, b)) = match_mul(p1) else {
            continue;
        };
        let Some((c, d)) = match_mul(p2) else {
            continue;
        };
        if is_re_of(a, z) && is_img_of(b, w) && is_img_of(c, z) && is_re_of(d, w) {
            return true;
        }
        if is_re_of(a, z) && is_img_of(b, w) && is_re_of(c, w) && is_img_of(d, z) {
            return true;
        }
    }
    false
}

fn sin_of_sum_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) = left else {
        return false;
    };
    let Some((a, b)) = match_add(arg) else {
        return false;
    };
    // sin(a)*cos(b) + cos(a)*sin(b)
    let Some((p1, p2)) = match_add(right) else {
        return false;
    };
    trig_add_product_pair(p1, p2, a, b, true) || trig_add_product_pair(p2, p1, a, b, true)
}

fn cos_of_sum_shape(left: &Obj, right: &Obj) -> bool {
    let Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) = left else {
        return false;
    };
    let Some((a, b)) = match_add(arg) else {
        return false;
    };
    // cos(a)*cos(b) - sin(a)*sin(b)
    let Some((p1, p2)) = match_sub(right) else {
        return false;
    };
    let Some((c1, c2)) = match_mul(p1) else {
        return false;
    };
    let Some((s1, s2)) = match_mul(p2) else {
        return false;
    };
    is_cos_of(c1, a)
        && is_cos_of(c2, b)
        && is_sin_of(s1, a)
        && is_sin_of(s2, b)
        || is_cos_of(c1, b)
            && is_cos_of(c2, a)
            && is_sin_of(s1, a)
            && is_sin_of(s2, b)
}

fn trig_add_product_pair(p1: &Obj, p2: &Obj, a: &Obj, b: &Obj, want_sin_cos: bool) -> bool {
    let Some((x, y)) = match_mul(p1) else {
        return false;
    };
    let Some((u, v)) = match_mul(p2) else {
        return false;
    };
    if !want_sin_cos {
        return false;
    }
    (is_sin_of(x, a) && is_cos_of(y, b) && is_cos_of(u, a) && is_sin_of(v, b))
        || (is_sin_of(x, a) && is_cos_of(y, b) && is_sin_of(u, b) && is_cos_of(v, a))
}

fn is_re_of(obj: &Obj, z: &Obj) -> bool {
    matches!(
        obj,
        Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) if arg.ir() == z.ir()
    )
}

fn is_img_of(obj: &Obj, z: &Obj) -> bool {
    matches!(
        obj,
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg }))
            if arg.ir() == z.ir()
    )
}

fn is_sin_of(obj: &Obj, arg: &Obj) -> bool {
    matches!(
        obj,
        Obj::TrigOperator(TrigOperator::Sin(Sin { arg: a })) if a.ir() == arg.ir()
    )
}

fn is_cos_of(obj: &Obj, arg: &Obj) -> bool {
    matches!(
        obj,
        Obj::TrigOperator(TrigOperator::Cos(Cos { arg: a })) if a.ir() == arg.ir()
    )
}

fn square_of(obj: &Obj) -> Option<&Obj> {
    let (base, exp) = match_pow(obj)?;
    if is_number_two(exp) {
        Some(base)
    } else {
        None
    }
}

fn match_log(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Log(Log { base, arg })) => {
            Some((base.as_ref(), arg.as_ref()))
        }
        _ => None,
    }
}

fn match_exp(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_pow(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) => {
            Some((base.as_ref(), exponent.as_ref()))
        }
        _ => None,
    }
}

fn match_add(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
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

fn match_mul(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_div(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_reduce(obj: &Obj) -> Option<&Reduce> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Reduce(r)) => Some(r),
        _ => None,
    }
}

fn is_empty_list_set(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::SetFormer(SetFormer::ListSet(ListSet { list })) if list.is_empty()
    )
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_neg_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "-1"
    )
}

fn is_number_two(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
}

fn bound_name_obj(name: &BoundName) -> Obj {
    Obj::Identifier(crate::ast::obj::IdentifierObj::from_bound_name(name))
}

fn is_binary_add_anonymous_fn(obj: &Obj) -> bool {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        equal_to,
        body,
    })) = obj
    else {
        return false;
    };
    let mut nparams = 0;
    for g in &body.set_bound_parameters.groups {
        nparams += g.params.len();
    }
    if nparams != 2 {
        return false;
    }
    matches!(
        equal_to.as_ref(),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(_))
    )
}

fn apply_fn_one_arg(f: &Obj, arg: Obj) -> Option<Obj> {
    match f {
        Obj::Identifier(id) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            if body.is_empty() {
                body.push(vec![Box::new(arg)]);
            } else {
                body[0].push(Box::new(arg));
            }
            Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }))
        }
        _ => None,
    }
}
