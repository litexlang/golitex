mod arith;
mod atom;
mod binder_obj;
mod set;
mod struct_template;

use std::collections::HashMap;

use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

use super::error::InstError;

impl Runtime {
    pub(crate) fn inst_obj_rec(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        match obj {
            Obj::Identifier(_) => {
                self.inst_identifier_obj(obj, param_to_arg_map, fresh, binder_renames)
            }
            Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => Ok(Self::inst_leaf_obj(obj)),
            Obj::Add(a) => self.inst_add_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Sub(a) => self.inst_sub_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Mul(a) => self.inst_mul_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Div(a) => self.inst_div_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Mod(a) => self.inst_mod_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Quot(a) => self.inst_quot_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Gcd(a) => self.inst_gcd_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Lcm(a) => self.inst_lcm_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Min(a) => self.inst_min_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Max(a) => self.inst_max_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Pow(a) => self.inst_pow_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Log(a) => self.inst_log_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Floor(a) => self.inst_floor_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Ceil(a) => self.inst_ceil_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Exp(a) => self.inst_exp_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Ln(a) => self.inst_ln_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Sign(a) => self.inst_sign_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Factorial(a) => self.inst_factorial_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Abs(a) => self.inst_abs_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Sin(a) => self.inst_sin_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Arcsin(a) => self.inst_arcsin_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Cos(a) => self.inst_cos_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Tan(a) => self.inst_tan_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Cot(a) => self.inst_cot_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::RealPart(a) => self.inst_real_part_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::ImaginaryPart(a) => {
                self.inst_imaginary_part_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::ComplexAbs(a) => self.inst_complex_abs_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Sqrt(a) => self.inst_sqrt_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Union(a) => self.inst_union_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Intersect(a) => self.inst_intersect_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::SetMinus(a) => self.inst_set_minus_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::BigUnion(a) => self.inst_big_union_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::BigIntersect(a) => {
                self.inst_big_intersect_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::IndexUnion(a) => self.inst_index_union_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::IndexIntersect(a) => {
                self.inst_index_intersect_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::PowerSet(a) => self.inst_power_set_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::GeneralCart(a) => self.inst_general_cart_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::ListSet(a) => self.inst_list_set_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Cart(a) => self.inst_cart_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Tuple(a) => self.inst_tuple_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::CartDim(a) => self.inst_cart_dim_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Proj(a) => self.inst_proj_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::TupleDim(a) => self.inst_tuple_dim_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::FiniteSetSize(a) => {
                self.inst_finite_set_size_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::FiniteSetMax(a) => {
                self.inst_finite_set_max_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::FiniteSetMin(a) => {
                self.inst_finite_set_min_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::FnRange(a) => self.inst_fn_range_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Replacement(a) => self.inst_replacement_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::Sum(a) => self.inst_sum_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::SumOfFiniteSet(a) => {
                self.inst_sum_of_finite_set_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::Product(a) => self.inst_product_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::ProductOfFiniteSet(a) => {
                self.inst_product_of_finite_set_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::Reduce(a) => self.inst_reduce_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::FiniteSetReduce(a) => {
                self.inst_finite_set_reduce_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::Range(a) => self.inst_range_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::ClosedRange(a) => self.inst_closed_range_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::FiniteSeqSet(a) => {
                self.inst_finite_seq_set_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::SeqSet(a) => self.inst_seq_set_obj(a, param_to_arg_map, fresh, binder_renames),
            Obj::FiniteSeqListObj(a) => {
                self.inst_finite_seq_list_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::ObjAtIndex(a) => {
                self.inst_obj_at_index_obj(a, param_to_arg_map, fresh, binder_renames)
            }
            Obj::FnObj(f) => self.inst_fn_obj(f, param_to_arg_map, fresh, binder_renames),
            Obj::SetBuilder(sb) => self.inst_set_builder_obj(sb, param_to_arg_map, fresh, binder_renames),
            Obj::FnSet(fs) => self.inst_fn_set_obj(fs, param_to_arg_map, fresh, binder_renames),
            Obj::AnonymousFn(af) => self.inst_anonymous_fn_obj(af, param_to_arg_map, fresh, binder_renames),
            Obj::StructObj(s) => Ok(Obj::StructObj(
                self.inst_struct_obj(s, param_to_arg_map, fresh, binder_renames)?,
            )),
            Obj::ObjAsStructInstanceWithFieldAccess(a) => Ok(Obj::ObjAsStructInstanceWithFieldAccess(
                self.inst_obj_as_struct(a, param_to_arg_map, fresh, binder_renames)?,
            )),
            Obj::InstantiatedTemplateObj(a) => Ok(Obj::InstantiatedTemplateObj(
                self.inst_instantiated_template(a, param_to_arg_map, fresh, binder_renames)?,
            )),
            Obj::OneSideInfinityIntervalObj(i) => {
                self.inst_one_side_infinity_interval(i, param_to_arg_map, fresh, binder_renames)
            }
            Obj::IntervalObj(i) => self.inst_interval(i, param_to_arg_map, fresh, binder_renames),
        }
    }
}
