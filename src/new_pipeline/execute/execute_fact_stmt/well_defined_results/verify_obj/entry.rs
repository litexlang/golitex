//! Object WD entry: known-memory lookup, then match Obj → family branch.
//!
//! Soft miss is `Ok(Failed(...))` — ill-formed / not WD, not "unknown theorem".
//! Must-prove callers reject that at their boundary.

use super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedResult;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::ObjWellDefinedProofByDef;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use crate::new_pipeline::ast::obj::{
    ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FnObjHead, FunctionSpace,
    IntegerOperator, IteratedOperator, Literal, Obj, ProductShape, SetFormer, SetOperator,
    StructAndFieldAccessObj, TrigOperator,
};
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
    // the well-definedness of this object is already proved earlier
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
            return Ok(VerifyObjWellDefinedResult::Success(
                ObjWellDefinedProof::ByKnown { wd_id },
            ));
        }

        // Identifier: must be defined in the current env stack.
        if let Obj::Identifier(value) = obj {
            return self.verify_identifier_obj_well_definedness(value, verify_state);
        }

        // Struct view `&Name` / `&Name(args)`: known definition + arity + param WD.
        if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(value)) = obj {
            return self.verify_struct_obj_well_definedness(value, verify_state);
        }

        // Template instance `\Name<args>`: known definition + arity + args/requirements WD.
        if let Obj::InstantiatedTemplateObj(value) = obj {
            return self.verify_instantiated_template_obj_well_definedness(value, verify_state);
        }

        // `x.y` / `x.y.z`: definition-time struct carrier walk along `fields`.
        if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value)) = obj {
            return self.verify_field_access_obj_well_definedness(value, verify_state);
        }

        // Identifier / template-instance / anonymous-literal headed FnObj: domain check.
        if let Obj::FnObj(value) = obj {
            match value.head.as_ref() {
                FnObjHead::Identifier(_) | FnObjHead::InstantiatedTemplateObj(_) => {
                    return self.verify_in_function_set_headed_fn_obj_well_definedness(
                        value,
                        verify_state,
                    );
                }
                FnObjHead::AnonymousFnLiteral(_) => {
                    return self.verify_anonymous_fn_literal_headed_fn_obj_well_definedness(
                        value,
                        verify_state,
                    );
                }
                FnObjHead::FieldAccess(_) => {}
            }
        }

        // fn_range(f): requires f registered in some FnSet.
        if let Obj::FunctionSpace(FunctionSpace::FnRange(value)) = obj {
            return self.verify_fn_range_obj_well_definedness(value, verify_state);
        }

        // Indexed family / choice: `$is_set` half + family ∈ FnSet registration.
        match obj {
            Obj::SetOperator(SetOperator::IndexUnion(value)) => {
                return self.verify_index_union_obj_well_definedness(value, verify_state);
            }
            Obj::SetOperator(SetOperator::IndexIntersect(value)) => {
                return self.verify_index_intersect_obj_well_definedness(value, verify_state);
            }
            Obj::SetOperator(SetOperator::IndexCart(value)) => {
                return self.verify_index_cart_obj_well_definedness(value, verify_state);
            }
            _ => {}
        }

        // Binder objects: dedicated pipelines that keep proof-scope local_env.
        match obj {
            Obj::FunctionSpace(FunctionSpace::FnSet(value)) => {
                return self.verify_fn_set_obj_well_definedness(value, verify_state);
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(value)) => {
                return self.verify_anonymous_fn_obj_well_definedness(value, verify_state);
            }
            Obj::SetFormer(SetFormer::SetBuilder(value)) => {
                return self.verify_set_builder_obj_well_definedness(value, verify_state);
            }
            _ => {}
        }

        let stages = self.verify_obj_well_definedness_by_def(obj, verify_state.clone())?;
        match finish_by_def(obj, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(obj.clone(), wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(
                    ObjWellDefinedProof::ByDef(by_def),
                ))
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
            Obj::Identifier(_) => {
                unreachable!("Identifier WD uses verify_identifier_obj_well_definedness")
            }
            Obj::FnObj(value) => self.verify_fn_obj_well_definedness_by_def(value, verify_state),
            Obj::Literal(Literal::Number(_)) => {
                self.verify_number_obj_well_definedness_by_def(verify_state)
            }
            Obj::Literal(Literal::ImaginaryUnit(_)) => {
                self.verify_imaginary_unit_obj_well_definedness_by_def(verify_state)
            }
            Obj::Literal(Literal::EulerNumber(_)) => {
                self.verify_euler_number_obj_well_definedness_by_def(verify_state)
            }
            Obj::Literal(Literal::Pi(_)) => {
                self.verify_pi_obj_well_definedness_by_def(verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => {
                self.verify_add_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => {
                self.verify_sub_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => {
                self.verify_neg_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => {
                self.verify_mul_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => {
                self.verify_div_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IntegerOperator(IntegerOperator::Mod(value)) => {
                self.verify_mod_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IntegerOperator(IntegerOperator::Quot(value)) => {
                self.verify_quot_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(value)) => {
                self.verify_gcd_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IntegerOperator(IntegerOperator::Lcm(value)) => {
                self.verify_lcm_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(value)) => {
                self.verify_floor_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(value)) => {
                self.verify_ceil_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(value)) => {
                self.verify_min_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(value)) => {
                self.verify_max_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(value)) => {
                self.verify_exp_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Ln(value)) => {
                self.verify_ln_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(value)) => {
                self.verify_sign_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(value)) => {
                self.verify_factorial_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => {
                self.verify_pow_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(value)) => {
                self.verify_abs_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Sin(value)) => {
                self.verify_sin_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Arcsin(value)) => {
                self.verify_arcsin_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Arccos(value)) => {
                self.verify_arccos_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Arctan(value)) => {
                self.verify_arctan_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Arccot(value)) => {
                self.verify_arccot_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Cos(value)) => {
                self.verify_cos_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Tan(value)) => {
                self.verify_tan_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::TrigOperator(TrigOperator::Cot(value)) => {
                self.verify_cot_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ComplexOperator(ComplexOperator::RealPart(value)) => {
                self.verify_real_part_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(value)) => {
                self.verify_imaginary_part_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(value)) => {
                self.verify_complex_abs_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(value)) => {
                self.verify_sqrt_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(value)) => {
                self.verify_log_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::Union(value)) => {
                self.verify_union_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::Intersect(value)) => {
                self.verify_intersect_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::SetMinus(value)) => {
                self.verify_set_minus_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::FamilyUnion(value)) => {
                self.verify_family_union_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::FamilyIntersect(value)) => {
                self.verify_family_intersect_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::IndexUnion(_)) => {
                unreachable!("IndexUnion WD uses verify_index_union_obj_well_definedness")
            }
            Obj::SetOperator(SetOperator::IndexIntersect(_)) => {
                unreachable!("IndexIntersect WD uses verify_index_intersect_obj_well_definedness")
            }
            Obj::SetOperator(SetOperator::PowerSet(value)) => {
                self.verify_power_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetOperator(SetOperator::IndexCart(_)) => {
                unreachable!("IndexCart WD uses verify_index_cart_obj_well_definedness")
            }
            Obj::SetFormer(SetFormer::ListSet(value)) => {
                self.verify_list_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetFormer(SetFormer::SetBuilder(_))
            | Obj::FunctionSpace(FunctionSpace::FnSet(_))
            | Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) => {
                // Handled in verify_obj_well_definedness via binder pipelines.
                Ok(ObjWellDefinedByDefCommonStages::leaf())
            }
            Obj::ProductShape(ProductShape::Cart(value)) => {
                self.verify_cart_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductShape(ProductShape::CartDim(value)) => {
                self.verify_cart_dim_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductShape(ProductShape::Proj(value)) => {
                self.verify_proj_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductShape(ProductShape::TupleDim(value)) => {
                self.verify_tuple_dim_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductShape(ProductShape::Tuple(value)) => {
                self.verify_tuple_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(value)) => {
                self.verify_finite_set_size_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(value)) => {
                self.verify_finite_set_max_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(value)) => {
                self.verify_finite_set_min_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::FunctionSpace(FunctionSpace::FnRange(_)) => {
                unreachable!("FnRange WD uses verify_fn_range_obj_well_definedness")
            }
            Obj::IteratedOperator(IteratedOperator::Sum(value)) => {
                self.verify_sum_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(value)) => {
                self.verify_sum_of_finite_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IteratedOperator(IteratedOperator::Product(value)) => {
                self.verify_product_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(value)) => {
                self.verify_product_of_finite_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IteratedOperator(IteratedOperator::Reduce(value)) => {
                self.verify_reduce_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(value)) => {
                self.verify_finite_set_reduce_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetFormer(SetFormer::Range(value)) => {
                self.verify_range_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetFormer(SetFormer::ClosedRange(value)) => {
                self.verify_closed_range_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(value)) => {
                self.verify_finite_seq_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::SetFormer(SetFormer::SeqSet(value)) => {
                self.verify_seq_set_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::ProductShape(ProductShape::ObjAtIndex(value)) => {
                self.verify_obj_at_index_obj_well_definedness_by_def(value, verify_state)
            }
            Obj::StandardSet(_) => {
                self.verify_standard_set_obj_well_definedness_by_def(verify_state)
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_)) => {
                unreachable!("StructObj WD uses verify_struct_obj_well_definedness")
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_)) => {
                unreachable!("field-access WD uses verify_field_access_obj_well_definedness")
            }
            Obj::InstantiatedTemplateObj(_) => {
                unreachable!(
                    "InstantiatedTemplateObj WD uses verify_instantiated_template_obj_well_definedness"
                )
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(value)) => self
                .verify_one_side_infinity_interval_obj_well_definedness_by_def(value, verify_state),
            Obj::SetFormer(SetFormer::IntervalObj(value)) => {
                self.verify_interval_obj_well_definedness_by_def(value, verify_state)
            }
        }
    }
}
