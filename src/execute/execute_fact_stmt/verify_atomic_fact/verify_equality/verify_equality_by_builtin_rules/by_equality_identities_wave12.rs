//! Stage B wave 12: remaining Obj equality leftovers.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::obj::{
    Add, ArithmeticOperator, ComplexAbs, ComplexOperator, FnObj, FnObjHead, FunctionSpace,
    ImaginaryPart, IntegerOperator, Intersect, IteratedOperator, ListSet, Literal, Mod, Mul,
    Number, Obj, Product, ProductOfFiniteSet, RealPart, SetFormer, SetMinus, SetOperator, Sum,
    SumOfFiniteSet, Union,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::anonymous_fns_alpha_equal;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin UnionSetMinusDecomposition: union(A, set_minus(B, A)) = union(A, B).
// Example: have A set; have B set; union(A, set_minus(B, A)) = union(A, B).
pub struct UnionSetMinusDecompositionBuiltinRuleProof {}

// Builtin SetMinusIntersectSelf: set_minus(B, intersect(A, B)) = set_minus(B, A).
// Example: have A set; have B set; set_minus(B, intersect(A, B)) = set_minus(B, A).
pub struct SetMinusIntersectSelfBuiltinRuleProof {}

// Builtin ReOfImaginaryUnit: re(i) = 0.
pub struct ReOfImaginaryUnitBuiltinRuleProof {}

// Builtin ImgOfImaginaryUnit: img(i) = 1.
pub struct ImgOfImaginaryUnitBuiltinRuleProof {}

// Builtin ReOfRealEmbedding: re(a) = a for a closed real numeral.
// Example: re(1) = 1.
pub struct ReOfRealEmbeddingBuiltinRuleProof {}

// Builtin ImgOfRealEmbedding: img(a) = 0 for a closed real numeral.
// Example: img(1) = 0.
pub struct ImgOfRealEmbeddingBuiltinRuleProof {}

// Builtin ReOfRealPlusI: re(a + i) = a for a closed real numeral.
// Example: re(1 + i) = 1.
pub struct ReOfRealPlusIBuiltinRuleProof {}

// Builtin ImgOfRealPlusI: img(a + i) = 1 for a closed real numeral.
// Example: img(1 + i) = 1.
pub struct ImgOfRealPlusIBuiltinRuleProof {}

// Builtin ComplexAbsOfImaginaryUnit: C_abs(i) = 1.
pub struct ComplexAbsOfImaginaryUnitBuiltinRuleProof {}

// Builtin ModNestedDivisibleAbsorption: (a % (k * m)) % m = a % m.
// Example: have a Z; have m N+; have k N+; trust m != 0; trust k != 0;
//          (a % (k * m)) % m = a % m.
pub struct ModNestedDivisibleAbsorptionBuiltinRuleProof {}

// Builtin SumSplitLastTerm: sum(s, e, f) = sum(s, e-1, f) + f(e).
// Example: sum(1, 3, fn(x Z) Z {x}) = sum(1, 2, fn(x Z) Z {x}) + 3.
pub struct SumSplitLastTermBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ProductSplitLastTerm: product(s, e, f) = product(s, e-1, f) * f(e).
// Example: product(1, 3, fn(x Z) Z {x}) = product(1, 2, fn(x Z) Z {x}) * 3.
pub struct ProductSplitLastTermBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin FiniteSetSumListExpansion: finite_set_sum({a1,...,an}, f) expands by left fold.
// Example: finite_set_sum({1, 2}, fn(x Z) Z {x}) = 1 + 2.
pub struct FiniteSetSumListExpansionBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin FiniteSetProductListExpansion: finite_set_product({a1,...,an}, f) expands by left fold.
// Example: finite_set_product({1, 2}, fn(x Z) Z {x}) = 1 * 2.
pub struct FiniteSetProductListExpansionBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave12BuiltinRuleProof {
    UnionSetMinusDecomposition(UnionSetMinusDecompositionBuiltinRuleProof),
    SetMinusIntersectSelf(SetMinusIntersectSelfBuiltinRuleProof),
    ReOfImaginaryUnit(ReOfImaginaryUnitBuiltinRuleProof),
    ImgOfImaginaryUnit(ImgOfImaginaryUnitBuiltinRuleProof),
    ReOfRealEmbedding(ReOfRealEmbeddingBuiltinRuleProof),
    ImgOfRealEmbedding(ImgOfRealEmbeddingBuiltinRuleProof),
    ReOfRealPlusI(ReOfRealPlusIBuiltinRuleProof),
    ImgOfRealPlusI(ImgOfRealPlusIBuiltinRuleProof),
    ComplexAbsOfImaginaryUnit(ComplexAbsOfImaginaryUnitBuiltinRuleProof),
    ModNestedDivisibleAbsorption(ModNestedDivisibleAbsorptionBuiltinRuleProof),
    SumSplitLastTerm(SumSplitLastTermBuiltinRuleProof),
    ProductSplitLastTerm(ProductSplitLastTermBuiltinRuleProof),
    FiniteSetSumListExpansion(FiniteSetSumListExpansionBuiltinRuleProof),
    FiniteSetProductListExpansion(FiniteSetProductListExpansionBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave12(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave12BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if union_set_minus_decomposition_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::UnionSetMinusDecomposition(
                        UnionSetMinusDecompositionBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_intersect_self_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::SetMinusIntersectSelf(
                        SetMinusIntersectSelfBuiltinRuleProof {},
                    ),
                ));
            }
            if re_of_imaginary_unit_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave12BuiltinRuleProof::ReOfImaginaryUnit(
                    ReOfImaginaryUnitBuiltinRuleProof {},
                )));
            }
            if img_of_imaginary_unit_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ImgOfImaginaryUnit(
                        ImgOfImaginaryUnitBuiltinRuleProof {},
                    ),
                ));
            }
            if re_of_real_embedding_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ReOfRealEmbedding(
                        ReOfRealEmbeddingBuiltinRuleProof {},
                    ),
                ));
            }
            if img_of_real_embedding_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ImgOfRealEmbedding(
                        ImgOfRealEmbeddingBuiltinRuleProof {},
                    ),
                ));
            }
            if re_of_real_plus_i_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave12BuiltinRuleProof::ReOfRealPlusI(
                    ReOfRealPlusIBuiltinRuleProof {},
                )));
            }
            if img_of_real_plus_i_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave12BuiltinRuleProof::ImgOfRealPlusI(
                    ImgOfRealPlusIBuiltinRuleProof {},
                )));
            }
            if complex_abs_of_imaginary_unit_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ComplexAbsOfImaginaryUnit(
                        ComplexAbsOfImaginaryUnitBuiltinRuleProof {},
                    ),
                ));
            }
            if mod_nested_divisible_absorption_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ModNestedDivisibleAbsorption(
                        ModNestedDivisibleAbsorptionBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_sum_split_last_term(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave12BuiltinRuleProof::SumSplitLastTerm(
                    p,
                )));
            }
            if let Some(p) = self.try_product_split_last_term(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::ProductSplitLastTerm(p),
                ));
            }
            if let Some(p) = self.try_finite_set_sum_list_expansion(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::FiniteSetSumListExpansion(p),
                ));
            }
            if let Some(p) = self.try_finite_set_product_list_expansion(left, right, child.clone())?
            {
                return Ok(Some(
                    EqualityIdentitiesWave12BuiltinRuleProof::FiniteSetProductListExpansion(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_sum_split_last_term(
        &mut self,
        full_side: &Obj,
        add_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SumSplitLastTermBuiltinRuleProof>> {
        let Some(full) = match_sum(full_side) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = add_side else {
            return Ok(None);
        };
        for (pre_side, tail) in [(left.as_ref(), right.as_ref()), (right.as_ref(), left.as_ref())] {
            let Some(pre) = match_sum(pre_side) else {
                continue;
            };
            if full.start.ir() != pre.start.ir() {
                continue;
            }
            if !funcs_match(full.func.as_ref(), pre.func.as_ref()) {
                continue;
            }
            if !end_is_predecessor_plus_one(full.end.as_ref(), pre.end.as_ref()) {
                continue;
            }
            let Some(applied) = apply_fn_one_arg(full.func.as_ref(), full.end.as_ref().clone()) else {
                continue;
            };
            let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: applied,
                right: tail.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(SumSplitLastTermBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }

    fn try_product_split_last_term(
        &mut self,
        full_side: &Obj,
        mul_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProductSplitLastTermBuiltinRuleProof>> {
        let Some(full) = match_product(full_side) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = mul_side else {
            return Ok(None);
        };
        for (pre_side, tail) in [(left.as_ref(), right.as_ref()), (right.as_ref(), left.as_ref())] {
            let Some(pre) = match_product(pre_side) else {
                continue;
            };
            if full.start.ir() != pre.start.ir() {
                continue;
            }
            if !funcs_match(full.func.as_ref(), pre.func.as_ref()) {
                continue;
            }
            if !end_is_predecessor_plus_one(full.end.as_ref(), pre.end.as_ref()) {
                continue;
            }
            let Some(applied) = apply_fn_one_arg(full.func.as_ref(), full.end.as_ref().clone()) else {
                continue;
            };
            let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: applied,
                right: tail.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(ProductSplitLastTermBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }

    fn try_finite_set_sum_list_expansion(
        &mut self,
        sum_side: &Obj,
        fold_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetSumListExpansionBuiltinRuleProof>> {
        let Some(sum) = match_sum_of_finite_set(sum_side) else {
            return Ok(None);
        };
        let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = sum.set.as_ref() else {
            return Ok(None);
        };
        if list.is_empty() {
            return Ok(None);
        }
        let leaves = collect_left_assoc_add_leaves(fold_side);
        if leaves.len() != list.len() {
            return Ok(None);
        }
        let mut proofs = Vec::with_capacity(list.len());
        for (elem, leaf) in list.iter().zip(leaves.iter()) {
            let Some(applied) = apply_fn_one_arg(sum.func.as_ref(), elem.as_ref().clone()) else {
                return Ok(None);
            };
            let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: applied,
                right: leaf.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(FiniteSetSumListExpansionBuiltinRuleProof {
            proof_of_requirement_facts: proofs,
        }))
    }

    fn try_finite_set_product_list_expansion(
        &mut self,
        product_side: &Obj,
        fold_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetProductListExpansionBuiltinRuleProof>> {
        let Some(product) = match_product_of_finite_set(product_side) else {
            return Ok(None);
        };
        let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = product.set.as_ref() else {
            return Ok(None);
        };
        if list.is_empty() {
            return Ok(None);
        }
        let leaves = collect_left_assoc_mul_leaves(fold_side);
        if leaves.len() != list.len() {
            return Ok(None);
        }
        let mut proofs = Vec::with_capacity(list.len());
        for (elem, leaf) in list.iter().zip(leaves.iter()) {
            let Some(applied) = apply_fn_one_arg(product.func.as_ref(), elem.as_ref().clone()) else {
                return Ok(None);
            };
            let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: applied,
                right: leaf.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(FiniteSetProductListExpansionBuiltinRuleProof {
            proof_of_requirement_facts: proofs,
        }))
    }
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

fn match_sum(obj: &Obj) -> Option<&Sum> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Sum(s)) => Some(s),
        _ => None,
    }
}

fn match_product(obj: &Obj) -> Option<&Product> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Product(p)) => Some(p),
        _ => None,
    }
}

fn match_sum_of_finite_set(obj: &Obj) -> Option<&SumOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => Some(s),
        _ => None,
    }
}

fn match_product_of_finite_set(obj: &Obj) -> Option<&ProductOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) => Some(p),
        _ => None,
    }
}

fn match_mod(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn is_imaginary_unit(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::ImaginaryUnit(_)))
}

fn is_number_obj(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(_)))
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

fn funcs_match(left: &Obj, right: &Obj) -> bool {
    if left.ir() == right.ir() {
        return true;
    }
    match (left, right) {
        (
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(l)),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(r)),
        ) => anonymous_fns_alpha_equal(l, r),
        _ => false,
    }
}

fn end_is_predecessor_plus_one(full_end: &Obj, pre_end: &Obj) -> bool {
    match full_end {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            (left.ir() == pre_end.ir() && is_one_obj(right.as_ref()))
                || (right.ir() == pre_end.ir() && is_one_obj(left.as_ref()))
        }
        _ => match (full_end, pre_end) {
            (
                Obj::Literal(Literal::Number(Number {
                    normalized_value: f,
                })),
                Obj::Literal(Literal::Number(Number {
                    normalized_value: p,
                })),
            ) => {
                let Ok(fv) = f.parse::<i128>() else {
                    return false;
                };
                let Ok(pv) = p.parse::<i128>() else {
                    return false;
                };
                fv == pv + 1
            }
            _ => false,
        },
    }
}

fn apply_fn_one_arg(f: &Obj, arg: Obj) -> Option<Obj> {
    match f {
        Obj::Identifier(id) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            body.push(vec![Box::new(arg)]);
            Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }))
        }
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(af.clone()))),
            body: vec![vec![Box::new(arg)]],
        })),
        _ => None,
    }
}

fn union_set_minus_decomposition_shape(decomposed: &Obj, original: &Obj) -> bool {
    let Some(d) = match_union(decomposed) else {
        return false;
    };
    let Some(o) = match_union(original) else {
        return false;
    };
    for (plain, difference) in [(d.left.as_ref(), d.right.as_ref()), (d.right.as_ref(), d.left.as_ref())]
    {
        let Some(diff) = match_set_minus(difference) else {
            continue;
        };
        if plain.ir() != diff.right.ir() {
            continue;
        }
        if (o.left.ir() == plain.ir() && o.right.ir() == diff.left.ir())
            || (o.right.ir() == plain.ir() && o.left.ir() == diff.left.ir())
        {
            return true;
        }
    }
    false
}

fn set_minus_intersect_self_shape(restricted: &Obj, plain: &Obj) -> bool {
    let Some(r) = match_set_minus(restricted) else {
        return false;
    };
    let Some(inter) = match_intersect(r.right.as_ref()) else {
        return false;
    };
    let Some(p) = match_set_minus(plain) else {
        return false;
    };
    if r.left.ir() != p.left.ir() {
        return false;
    }
    let retained = r.left.as_ref();
    (inter.left.ir() == retained.ir() && inter.right.ir() == p.right.ir())
        || (inter.right.ir() == retained.ir() && inter.left.ir() == p.right.ir())
}

fn re_of_imaginary_unit_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) if is_imaginary_unit(arg.as_ref())
    ) && is_zero_obj(right)
}

fn img_of_imaginary_unit_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) if is_imaginary_unit(arg.as_ref())
    ) && is_one_obj(right)
}

fn re_of_real_embedding_shape(left: &Obj, right: &Obj) -> bool {
    match left {
        Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) => {
            is_number_obj(arg.as_ref()) && arg.ir() == right.ir()
        }
        _ => false,
    }
}

fn img_of_real_embedding_shape(left: &Obj, right: &Obj) -> bool {
    match left {
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) => {
            is_number_obj(arg.as_ref()) && is_zero_obj(right)
        }
        _ => false,
    }
}

fn real_plus_i_real_part(arg: &Obj) -> Option<&Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = arg else {
        return None;
    };
    if is_number_obj(left.as_ref()) && is_imaginary_unit(right.as_ref()) {
        return Some(left.as_ref());
    }
    if is_imaginary_unit(left.as_ref()) && is_number_obj(right.as_ref()) {
        return Some(right.as_ref());
    }
    None
}

fn re_of_real_plus_i_shape(left: &Obj, right: &Obj) -> bool {
    match left {
        Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg })) => {
            let Some(real) = real_plus_i_real_part(arg.as_ref()) else {
                return false;
            };
            real.ir() == right.ir()
        }
        _ => false,
    }
}

fn img_of_real_plus_i_shape(left: &Obj, right: &Obj) -> bool {
    match left {
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg })) => {
            real_plus_i_real_part(arg.as_ref()).is_some() && is_one_obj(right)
        }
        _ => false,
    }
}

fn complex_abs_of_imaginary_unit_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs { arg })) if is_imaginary_unit(arg.as_ref())
    ) && is_one_obj(right)
}

fn mod_nested_divisible_absorption_shape(left: &Obj, right: &Obj) -> bool {
    let Some((inner_mod, outer_mod)) = match_mod(left) else {
        return false;
    };
    let Some((a_right, m_right)) = match_mod(right) else {
        return false;
    };
    if outer_mod.ir() != m_right.ir() {
        return false;
    }
    let Some((a_inner, km)) = match_mod(inner_mod) else {
        return false;
    };
    if a_inner.ir() != a_right.ir() {
        return false;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left: k, right: m })) = km else {
        return false;
    };
    m.ir() == outer_mod.ir() || k.ir() == outer_mod.ir()
}

fn collect_left_assoc_add_leaves(obj: &Obj) -> Vec<Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            let mut leaves = collect_left_assoc_add_leaves(left.as_ref());
            leaves.push(right.as_ref().clone());
            leaves
        }
        other => vec![other.clone()],
    }
}

fn collect_left_assoc_mul_leaves(obj: &Obj) -> Vec<Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            let mut leaves = collect_left_assoc_mul_leaves(left.as_ref());
            leaves.push(right.as_ref().clone());
            leaves
        }
        other => vec![other.clone()],
    }
}
