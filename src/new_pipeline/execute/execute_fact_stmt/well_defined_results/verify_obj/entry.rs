//! Object WD entry: known-memory lookup, then match Obj → family branch.
//!
//! Soft miss is `Ok(Failed(...))`. Must-prove callers reject that at their boundary.

use super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedResult;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::ObjWellDefinedProofByDef;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Top-level object WD: Success(proof) | Failed(reason). Proof never embeds Fail.
pub enum VerifyObjWellDefinedResult {
    Success(ObjWellDefinedProof),
    Failed(FailToVerifyObjWellDefinedResult),
}

// Success-only evidence that an object is well-defined.
pub enum ObjWellDefinedProof {
    ByKnown { wd_id: WellDefinednessId },
    ByDef(ObjWellDefinedProofByDef),
}

impl VerifyObjWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Known-memory lookup across the env stack, then prove by definition.
    // When store_well_defined_fact is set and ByDef succeeds, record on current top.
    pub fn verify_obj_well_definedness(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if let Some(wd_id) = self.well_defined_visible_in_stack(obj) {
            return Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown {
                wd_id,
            }));
        }

        let stages = self.verify_obj_well_definedness_by_def(obj, verify_state.clone())?;
        match finish_by_def(obj, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(obj.clone(), wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
                    by_def,
                )))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed(fail)),
        }
    }

    // Big match: every Obj variant has its own by-def branch function.
    // Branches return CommonStages; entry packs into Obj-mirrored Success/Failed.
    fn verify_obj_well_definedness_by_def(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        match obj {
            Obj::Identifier(_) => self.verify_atom_obj_well_definedness_by_def(verify_state),
            Obj::FnObj(value) => self.verify_fn_obj_well_definedness_by_def(value, verify_state),
            Obj::Number(_) => self.verify_number_obj_well_definedness_by_def(verify_state),
            Obj::ImaginaryUnit(_) => {
                self.verify_imaginary_unit_obj_well_definedness_by_def(verify_state)
            }
            Obj::EulerNumber(_) => {
                self.verify_euler_number_obj_well_definedness_by_def(verify_state)
            }
            Obj::Pi(_) => self.verify_pi_obj_well_definedness_by_def(verify_state),
            Obj::Add(value) => self.verify_add_obj_well_definedness_by_def(value, verify_state),
            Obj::Sub(value) => self.verify_sub_obj_well_definedness_by_def(value, verify_state),
            Obj::Mul(value) => self.verify_mul_obj_well_definedness_by_def(value, verify_state),
            Obj::Div(value) => self.verify_div_obj_well_definedness_by_def(value, verify_state),
            Obj::Mod(value) => self.verify_mod_obj_well_definedness_by_def(value, verify_state),
            Obj::Quot(value) => self.verify_quot_obj_well_definedness_by_def(value, verify_state),
            Obj::Gcd(value) => self.verify_gcd_obj_well_definedness_by_def(value, verify_state),
            Obj::Lcm(value) => self.verify_lcm_obj_well_definedness_by_def(value, verify_state),
            Obj::Floor(value) => self.verify_floor_obj_well_definedness_by_def(value, verify_state),
            Obj::Ceil(value) => self.verify_ceil_obj_well_definedness_by_def(value, verify_state),
            Obj::Min(value) => self.verify_min_obj_well_definedness_by_def(value, verify_state),
            Obj::Max(value) => self.verify_max_obj_well_definedness_by_def(value, verify_state),
            Obj::Exp(value) => self.verify_exp_obj_well_definedness_by_def(value, verify_state),
            Obj::Ln(value) => self.verify_ln_obj_well_definedness_by_def(value, verify_state),
            Obj::Sign(value) => self.verify_sign_obj_well_definedness_by_def(value, verify_state),
            Obj::Factorial(value) => {
                self.verify_factorial_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Pow(value) => self.verify_pow_obj_well_definedness_by_def(value, verify_state),
            Obj::Abs(value) => self.verify_abs_obj_well_definedness_by_def(value, verify_state),
            Obj::Sin(value) => self.verify_sin_obj_well_definedness_by_def(value, verify_state),
            Obj::Arcsin(value) => {
                self.verify_arcsin_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Cos(value) => self.verify_cos_obj_well_definedness_by_def(value, verify_state),
            Obj::Tan(value) => self.verify_tan_obj_well_definedness_by_def(value, verify_state),
            Obj::Cot(value) => self.verify_cot_obj_well_definedness_by_def(value, verify_state),
            Obj::RealPart(value) => {
                self.verify_real_part_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ImaginaryPart(value) => {
                self.verify_imaginary_part_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ComplexAbs(value) => {
                self.verify_complex_abs_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Sqrt(value) => self.verify_sqrt_obj_well_definedness_by_def(value, verify_state),
            Obj::Log(value) => self.verify_log_obj_well_definedness_by_def(value, verify_state),
            Obj::Union(value) => self.verify_union_obj_well_definedness_by_def(value, verify_state),
            Obj::Intersect(value) => {
                self.verify_intersect_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetMinus(value) => {
                self.verify_set_minus_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::BigUnion(value) => {
                self.verify_big_union_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::BigIntersect(value) => {
                self.verify_big_intersect_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IndexUnion(value) => {
                self.verify_index_union_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IndexIntersect(value) => {
                self.verify_index_intersect_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::PowerSet(value) => {
                self.verify_power_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::GeneralCart(value) => {
                self.verify_general_cart_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ListSet(value) => {
                self.verify_list_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetBuilder(value) => {
                self.verify_set_builder_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FnSet(value) => {
                self.verify_fn_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::AnonymousFn(value) => {
                self.verify_anonymous_fn_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Cart(value) => self.verify_cart_obj_well_definedness_by_def(value, verify_state),
            Obj::CartDim(value) => {
                self.verify_cart_dim_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Proj(value) => self.verify_proj_obj_well_definedness_by_def(value, verify_state),
            Obj::TupleDim(value) => {
                self.verify_tuple_dim_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Tuple(value) => self.verify_tuple_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSetSize(value) => {
                self.verify_finite_set_size_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetMax(value) => {
                self.verify_finite_set_max_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetMin(value) => {
                self.verify_finite_set_min_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FnRange(value) => {
                self.verify_fn_range_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Replacement(value) => {
                self.verify_replacement_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Sum(value) => self.verify_sum_obj_well_definedness_by_def(value, verify_state),
            Obj::SumOfFiniteSet(value) => {
                self.verify_sum_of_finite_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Product(value) => {
                self.verify_product_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductOfFiniteSet(value) => {
                self.verify_product_of_finite_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Reduce(value) => {
                self.verify_reduce_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetReduce(value) => {
                self.verify_finite_set_reduce_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::Range(value) => self.verify_range_obj_well_definedness_by_def(value, verify_state),
            Obj::ClosedRange(value) => {
                self.verify_closed_range_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSeqSet(value) => {
                self.verify_finite_seq_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SeqSet(value) => {
                self.verify_seq_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSeqListObj(value) => {
                self.verify_finite_seq_list_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ObjAtIndex(value) => {
                self.verify_obj_at_index_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::StandardSet(_) => {
                self.verify_standard_set_obj_well_definedness_by_def(verify_state)
            }
            Obj::StructObj(value) => {
                self.verify_struct_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ObjAsStructInstanceWithFieldAccess(value) => self
                .verify_obj_as_struct_instance_with_field_access_obj_well_definedness_by_def(
                    value,
                    verify_state,
                ),
            Obj::InstantiatedTemplateObj(value) => {
                self.verify_instantiated_template_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::OneSideInfinityIntervalObj(value) => self
                .verify_one_side_infinity_interval_obj_well_definedness_by_def(value, verify_state),
            Obj::IntervalObj(value) => {
                self.verify_interval_obj_well_definedness_by_def(value, verify_state)
            }
        }
    }
}
