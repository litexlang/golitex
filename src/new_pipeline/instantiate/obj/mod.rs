mod arith;
mod atom;
mod binder_obj;
mod set;
mod struct_template;

use std::collections::HashMap;

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::obj::{
    ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FunctionSpace,
    IntegerOperator, IteratedOperator, Literal, Obj, ProductShape, SetFormer, SetOperator,
    StructAndFieldAccessObj, TrigOperator,
};
use crate::new_pipeline::runtime::Runtime;

use super::error::InstError;

impl Runtime {
    pub(crate) fn inst_obj_rec(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Obj, InstError> {
        match obj {
            Obj::Identifier(_) => self.inst_identifier_obj(obj, param_to_arg_map),
            Obj::Literal(Literal::Number(_))
            | Obj::Literal(Literal::ImaginaryUnit(_))
            | Obj::Literal(Literal::EulerNumber(_))
            | Obj::Literal(Literal::Pi(_))
            | Obj::StandardSet(_) => Ok(Self::inst_leaf_obj(obj)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                self.inst_add_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                self.inst_sub_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                self.inst_mul_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                self.inst_div_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Mod(a)) => self.inst_mod_obj(a, param_to_arg_map),
            Obj::IntegerOperator(IntegerOperator::Quot(a)) => {
                self.inst_quot_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(a)) => self.inst_gcd_obj(a, param_to_arg_map),
            Obj::IntegerOperator(IntegerOperator::Lcm(a)) => self.inst_lcm_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Min(a)) => {
                self.inst_min_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(a)) => {
                self.inst_max_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
                self.inst_pow_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(a)) => self.inst_log_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)) => {
                self.inst_floor_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)) => {
                self.inst_ceil_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(a)) => self.inst_exp_obj(a, param_to_arg_map),
            Obj::ExpLogOperator(ExpLogOperator::Ln(a)) => self.inst_ln_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(a)) => {
                self.inst_sign_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(a)) => {
                self.inst_factorial_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                self.inst_abs_obj(a, param_to_arg_map)
            }
            Obj::TrigOperator(TrigOperator::Sin(a)) => self.inst_sin_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arcsin(a)) => self.inst_arcsin_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arccos(a)) => self.inst_arccos_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arctan(a)) => self.inst_arctan_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arccot(a)) => self.inst_arccot_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Cos(a)) => self.inst_cos_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Tan(a)) => self.inst_tan_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Cot(a)) => self.inst_cot_obj(a, param_to_arg_map),
            Obj::ComplexOperator(ComplexOperator::RealPart(a)) => {
                self.inst_real_part_obj(a, param_to_arg_map)
            }
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(a)) => {
                self.inst_imaginary_part_obj(a, param_to_arg_map)
            }
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(a)) => {
                self.inst_complex_abs_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)) => self.inst_sqrt_obj(a, param_to_arg_map),
            Obj::SetOperator(SetOperator::Union(a)) => self.inst_union_obj(a, param_to_arg_map),
            Obj::SetOperator(SetOperator::Intersect(a)) => {
                self.inst_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::SetMinus(a)) => {
                self.inst_set_minus_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::FamilyUnion(a)) => {
                self.inst_family_union_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::FamilyIntersect(a)) => {
                self.inst_family_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexUnion(a)) => {
                self.inst_index_union_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexIntersect(a)) => {
                self.inst_index_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::PowerSet(a)) => {
                self.inst_power_set_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexCart(a)) => {
                self.inst_index_cart_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::ListSet(a)) => self.inst_list_set_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::Cart(a)) => self.inst_cart_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::Tuple(a)) => self.inst_tuple_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::CartDim(a)) => {
                self.inst_cart_dim_obj(a, param_to_arg_map)
            }
            Obj::ProductShape(ProductShape::Proj(a)) => self.inst_proj_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::TupleDim(a)) => {
                self.inst_tuple_dim_obj(a, param_to_arg_map)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(a)) => {
                self.inst_finite_set_size_obj(a, param_to_arg_map)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(a)) => {
                self.inst_finite_set_max_obj(a, param_to_arg_map)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(a)) => {
                self.inst_finite_set_min_obj(a, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::FnRange(a)) => {
                self.inst_fn_range_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Sum(a)) => {
                self.inst_sum_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(a)) => {
                self.inst_sum_of_finite_set_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Product(a)) => {
                self.inst_product_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(a)) => {
                self.inst_product_of_finite_set_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Reduce(a)) => {
                self.inst_reduce_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(a)) => {
                self.inst_finite_set_reduce_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::Range(a)) => self.inst_range_obj(a, param_to_arg_map),
            Obj::SetFormer(SetFormer::ClosedRange(a)) => {
                self.inst_closed_range_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(a)) => {
                self.inst_finite_seq_set_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::SeqSet(a)) => self.inst_seq_set_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::ObjAtIndex(a)) => {
                self.inst_obj_at_index_obj(a, param_to_arg_map)
            }
            Obj::FnObj(f) => self.inst_fn_obj(f, param_to_arg_map),
            Obj::SetFormer(SetFormer::SetBuilder(sb)) => {
                self.inst_set_builder_obj(sb, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => {
                self.inst_fn_set_obj(fs, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
                self.inst_anonymous_fn_obj(af, param_to_arg_map)
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(s)) => Ok(Obj::StructAndFieldAccessObj(
                StructAndFieldAccessObj::StructObj(self.inst_struct_obj(s, param_to_arg_map)?),
            )),
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a)) => Ok(Obj::StructAndFieldAccessObj(
                StructAndFieldAccessObj::FieldAccess(self.inst_field_access(a, param_to_arg_map)?),
            )),
            Obj::InstantiatedTemplateObj(a) => {
                Ok(Obj::InstantiatedTemplateObj(
                    self.inst_instantiated_template(a, param_to_arg_map)?,
                ))
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(i)) => {
                self.inst_one_side_infinity_interval(i, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::IntervalObj(i)) => self.inst_interval(i, param_to_arg_map),
        }
    }
}
