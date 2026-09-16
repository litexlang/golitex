mod arith;
mod atom;
mod binder_obj;
mod set;
mod struct_template;

use crate::new_pipeline::ast::obj::Obj;

use super::InstCtx;
use super::error::InstError;

pub fn inst_obj(ctx: &mut InstCtx<'_>, obj: &Obj) -> Result<Obj, InstError> {
    match obj {
        Obj::Identifier(_) => atom::inst_identifier(ctx, obj),
        Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_) => Ok(atom::inst_leaf(obj)),
        Obj::Add(a) => arith::inst_add(ctx, a),
        Obj::Sub(a) => arith::inst_sub(ctx, a),
        Obj::Mul(a) => arith::inst_mul(ctx, a),
        Obj::Div(a) => arith::inst_div(ctx, a),
        Obj::Mod(a) => arith::inst_mod(ctx, a),
        Obj::Quot(a) => arith::inst_quot(ctx, a),
        Obj::Gcd(a) => arith::inst_gcd(ctx, a),
        Obj::Lcm(a) => arith::inst_lcm(ctx, a),
        Obj::Min(a) => arith::inst_min(ctx, a),
        Obj::Max(a) => arith::inst_max(ctx, a),
        Obj::Pow(a) => arith::inst_pow(ctx, a),
        Obj::Log(a) => arith::inst_log(ctx, a),
        Obj::Floor(a) => arith::inst_floor(ctx, a),
        Obj::Ceil(a) => arith::inst_ceil(ctx, a),
        Obj::Exp(a) => arith::inst_exp(ctx, a),
        Obj::Ln(a) => arith::inst_ln(ctx, a),
        Obj::Sign(a) => arith::inst_sign(ctx, a),
        Obj::Factorial(a) => arith::inst_factorial(ctx, a),
        Obj::Abs(a) => arith::inst_abs(ctx, a),
        Obj::Sin(a) => arith::inst_sin(ctx, a),
        Obj::Arcsin(a) => arith::inst_arcsin(ctx, a),
        Obj::Cos(a) => arith::inst_cos(ctx, a),
        Obj::Tan(a) => arith::inst_tan(ctx, a),
        Obj::Cot(a) => arith::inst_cot(ctx, a),
        Obj::RealPart(a) => arith::inst_real_part(ctx, a),
        Obj::ImaginaryPart(a) => arith::inst_imaginary_part(ctx, a),
        Obj::ComplexAbs(a) => arith::inst_complex_abs(ctx, a),
        Obj::Sqrt(a) => arith::inst_sqrt(ctx, a),
        Obj::Union(a) => set::inst_union(ctx, a),
        Obj::Intersect(a) => set::inst_intersect(ctx, a),
        Obj::SetMinus(a) => set::inst_set_minus(ctx, a),
        Obj::BigUnion(a) => set::inst_big_union(ctx, a),
        Obj::BigIntersect(a) => set::inst_big_intersect(ctx, a),
        Obj::IndexUnion(a) => set::inst_index_union(ctx, a),
        Obj::IndexIntersect(a) => set::inst_index_intersect(ctx, a),
        Obj::PowerSet(a) => set::inst_power_set(ctx, a),
        Obj::GeneralCart(a) => set::inst_general_cart(ctx, a),
        Obj::ListSet(a) => set::inst_list_set(ctx, a),
        Obj::Cart(a) => set::inst_cart(ctx, a),
        Obj::Tuple(a) => set::inst_tuple(ctx, a),
        Obj::CartDim(a) => set::inst_cart_dim(ctx, a),
        Obj::Proj(a) => set::inst_proj(ctx, a),
        Obj::TupleDim(a) => set::inst_tuple_dim(ctx, a),
        Obj::FiniteSetSize(a) => set::inst_finite_set_size(ctx, a),
        Obj::FiniteSetMax(a) => set::inst_finite_set_max(ctx, a),
        Obj::FiniteSetMin(a) => set::inst_finite_set_min(ctx, a),
        Obj::FnRange(a) => set::inst_fn_range(ctx, a),
        Obj::Replacement(a) => set::inst_replacement(ctx, a),
        Obj::Sum(a) => set::inst_sum(ctx, a),
        Obj::SumOfFiniteSet(a) => set::inst_sum_of_finite_set(ctx, a),
        Obj::Product(a) => set::inst_product(ctx, a),
        Obj::ProductOfFiniteSet(a) => set::inst_product_of_finite_set(ctx, a),
        Obj::Reduce(a) => set::inst_reduce(ctx, a),
        Obj::FiniteSetReduce(a) => set::inst_finite_set_reduce(ctx, a),
        Obj::Range(a) => set::inst_range(ctx, a),
        Obj::ClosedRange(a) => set::inst_closed_range(ctx, a),
        Obj::FiniteSeqSet(a) => set::inst_finite_seq_set(ctx, a),
        Obj::SeqSet(a) => set::inst_seq_set(ctx, a),
        Obj::FiniteSeqListObj(a) => set::inst_finite_seq_list_obj(ctx, a),
        Obj::ObjAtIndex(a) => set::inst_obj_at_index(ctx, a),
        Obj::FnObj(f) => binder_obj::inst_fn_obj(ctx, f),
        Obj::SetBuilder(sb) => binder_obj::inst_set_builder(ctx, sb),
        Obj::FnSet(fs) => binder_obj::inst_fn_set(ctx, fs),
        Obj::AnonymousFn(af) => binder_obj::inst_anonymous_fn(ctx, af),
        Obj::StructObj(s) => Ok(Obj::StructObj(struct_template::inst_struct_obj(ctx, s)?)),
        Obj::ObjAsStructInstanceWithFieldAccess(a) => Ok(Obj::ObjAsStructInstanceWithFieldAccess(
            struct_template::inst_obj_as_struct(ctx, a)?,
        )),
        Obj::InstantiatedTemplateObj(a) => Ok(Obj::InstantiatedTemplateObj(
            struct_template::inst_instantiated_template(ctx, a)?,
        )),
        Obj::OneSideInfinityIntervalObj(i) => struct_template::inst_one_side_infinity_interval(ctx, i),
        Obj::IntervalObj(i) => struct_template::inst_interval(ctx, i),
    }
}
