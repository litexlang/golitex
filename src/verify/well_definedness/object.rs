//! Object well-definedness dispatch and recursive result assembly.

use crate::prelude::*;
use std::rc::Rc;

#[path = "object/advanced.rs"]
mod advanced;
#[path = "object/core.rs"]
mod core;
#[path = "object/iterated.rs"]
mod iterated;
#[path = "object/matrix.rs"]
mod matrix;
#[path = "object/scalar.rs"]
mod scalar;
#[path = "object/sets.rs"]
mod sets;
#[path = "object/structs.rs"]
mod structs;

impl Runtime {
    /// Compositional WD entry point. Every object family returns its exact
    /// recursive children, fact checks, binder body, or Template instantiation.
    pub fn verify_obj_well_defined_result(
        &mut self,
        obj: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<Rc<SuccessVerifyObjWellDefinedResult>, RuntimeError> {
        let verify_state = verify_state.without_known_forall_for_equality();
        let verify_state = &verify_state;
        let reusable_cache_key = self.well_defined_cache_key_for_obj(obj);
        if let Some(source) = reusable_cache_key
            .as_ref()
            .and_then(|key| self.statement_well_defined_object_proof(key))
        {
            return Ok(Rc::new(SuccessVerifyObjWellDefinedResult::Reuse(Box::new(
                SuccessReuseObjWellDefinedResult::new(obj.clone(), source),
            ))));
        }
        let cache_key = reusable_cache_key
            .clone()
            .unwrap_or_else(|| WellDefinedCacheKey::without_function_contract(obj.to_string()));
        let active_key = obj_equality_key(obj);
        if !self.begin_well_defined_object(&active_key) {
            return Ok(Rc::new(
                SuccessVerifyObjWellDefinedResult::RecursiveReference(Box::new(
                    SuccessRecursiveObjWellDefinedResult::new(obj.clone(), active_key),
                )),
            ));
        }

        let steps = match obj {
            Obj::Atom(AtomObj::Identifier(identifier)) => self
                .verify_identifier_well_defined(identifier)
                .map(|_| Some(SuccessVerifyObjWellDefinedStepsResult::new())),
            Obj::Atom(AtomObj::IdentifierWithMod(identifier)) => self
                .verify_identifier_with_mod_well_defined(identifier)
                .map(|_| Some(SuccessVerifyObjWellDefinedStepsResult::new())),
            Obj::FnObj(value) => self
                .verify_fn_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Atom(AtomObj::Forall(_))
            | Obj::Atom(AtomObj::Def(_))
            | Obj::Atom(AtomObj::Exist(_))
            | Obj::Atom(AtomObj::SetBuilder(_))
            | Obj::Atom(AtomObj::FnSet(_))
            | Obj::Atom(AtomObj::Induc(_))
            | Obj::Atom(AtomObj::DefAlgo(_))
            | Obj::Atom(AtomObj::DefStructField(_))
            | Obj::Atom(AtomObj::TupleIndex(_))
            | Obj::Atom(AtomObj::CartIndex(_))
            | Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => Ok(Some(SuccessVerifyObjWellDefinedStepsResult::new())),
            Obj::Add(add) => self
                .verify_add_well_defined_result(add, verify_state)
                .map(Some),
            Obj::Sub(sub) => self
                .verify_sub_well_defined_result(sub, verify_state)
                .map(Some),
            Obj::Mul(mul) => self
                .verify_mul_well_defined_result(mul, verify_state)
                .map(Some),
            Obj::Div(div) => self
                .verify_div_well_defined_result(div, verify_state)
                .map(Some),
            Obj::Mod(value) => self
                .verify_mod_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Quot(value) => self
                .verify_quot_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Gcd(value) => self
                .verify_gcd_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Lcm(value) => self
                .verify_lcm_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Abs(value) => self
                .verify_abs_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Floor(value) => self
                .verify_floor_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Ceil(value) => self
                .verify_ceil_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Min(value) => self
                .verify_min_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Max(value) => self
                .verify_max_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Exp(value) => self
                .verify_exp_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Ln(value) => self
                .verify_ln_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Sign(value) => self
                .verify_sign_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Factorial(value) => self
                .verify_factorial_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Pow(value) => self
                .verify_pow_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Sin(value) => self
                .verify_sin_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Arcsin(value) => self
                .verify_arcsin_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Cos(value) => self
                .verify_cos_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Tan(value) => self
                .verify_tan_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Cot(value) => self
                .verify_cot_well_defined_result(value, verify_state)
                .map(Some),
            Obj::RealPart(value) => self
                .verify_real_part_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ImaginaryPart(value) => self
                .verify_imaginary_part_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ComplexAbs(value) => self
                .verify_complex_abs_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Sqrt(value) => self
                .verify_sqrt_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Log(value) => self
                .verify_log_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Union(value) => self
                .verify_union_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Intersect(value) => self
                .verify_intersect_well_defined_result(value, verify_state)
                .map(Some),
            Obj::SetMinus(value) => self
                .verify_set_minus_well_defined_result(value, verify_state)
                .map(Some),
            Obj::BigUnion(value) => self
                .verify_big_union_well_defined_result(value, verify_state)
                .map(Some),
            Obj::BigIntersect(value) => self
                .verify_big_intersect_well_defined_result(value, verify_state)
                .map(Some),
            Obj::IndexUnion(value) => self
                .verify_index_union_well_defined_result(value, verify_state)
                .map(Some),
            Obj::IndexIntersect(value) => self
                .verify_index_intersect_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ListSet(value) => self
                .verify_list_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Cart(value) => self
                .verify_cart_well_defined_result(value, verify_state)
                .map(Some),
            Obj::CartDim(value) => self
                .verify_cart_dim_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Proj(value) => self
                .verify_proj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::TupleDim(value) => self
                .verify_tuple_dim_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Tuple(value) => self
                .verify_tuple_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSetSize(value) => self
                .verify_finite_set_size_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSetMax(value) => self
                .verify_finite_set_max_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSetMin(value) => self
                .verify_finite_set_min_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FnRange(value) => self
                .verify_fn_range_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Replacement(value) => self
                .verify_replacement_well_defined_result(value, verify_state)
                .map(Some),
            Obj::PowerSet(value) => self
                .verify_power_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::GeneralCart(value) => self
                .verify_general_cart_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ObjAtIndex(value) => self
                .verify_obj_at_index_well_defined_result(value, verify_state)
                .map(Some),
            Obj::IntervalObj(value) => self
                .verify_interval_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::OneSideInfinityIntervalObj(value) => self
                .verify_one_side_infinity_interval_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSeqSet(value) => self
                .verify_finite_seq_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::SeqSet(value) => self
                .verify_seq_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSeqListObj(value) => self
                .verify_finite_seq_list_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Range(value) => self
                .verify_range_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ClosedRange(value) => self
                .verify_closed_range_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Sum(value) => self
                .verify_sum_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::SumOfFiniteSet(value) => self
                .verify_finite_set_sum_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Product(value) => self
                .verify_product_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ProductOfFiniteSet(value) => self
                .verify_finite_set_product_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::Reduce(value) => self
                .verify_reduce_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FiniteSetReduce(value) => self
                .verify_finite_set_reduce_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixSet(value) => self
                .verify_matrix_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixListObj(value) => self
                .verify_matrix_list_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixAdd(value) => self
                .verify_matrix_add_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixSub(value) => self
                .verify_matrix_sub_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixMul(value) => self
                .verify_matrix_mul_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixScalarMul(value) => self
                .verify_matrix_scalar_mul_well_defined_result(value, verify_state)
                .map(Some),
            Obj::MatrixPow(value) => self
                .verify_matrix_pow_well_defined_result(value, verify_state)
                .map(Some),
            Obj::SetBuilder(value) => self
                .verify_set_builder_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FnSet(value) => self
                .verify_fn_set_well_defined_result(value, verify_state)
                .map(Some),
            Obj::AnonymousFn(value) => self
                .verify_anonymous_fn_well_defined_result(value, verify_state)
                .map(Some),
            Obj::StructObj(value) => self
                .verify_struct_obj_well_defined_result(value, verify_state)
                .map(Some),
            Obj::ObjAsStructInstanceWithFieldAccess(value) => self
                .verify_obj_as_struct_instance_with_field_access_well_defined_result(
                    value,
                    verify_state,
                )
                .map(Some),
            Obj::InstantiatedTemplateObj(value) => self
                .verify_instantiated_template_obj_well_defined_result(value, verify_state)
                .map(Some),
        };

        self.end_well_defined_object(&active_key);
        let steps = steps?.expect("every Obj variant returns compositional WD steps");
        let intrinsic_result_set = intrinsic_well_definedness_result_set(obj, &steps);
        let result = Rc::new(SuccessVerifyObjWellDefinedResult::Direct(Box::new(
            SuccessVerifyDirectObjWellDefinedResult::new(
                obj.clone(),
                cache_key.clone(),
                steps,
                intrinsic_result_set,
            ),
        )));
        if let Some(reusable_cache_key) = reusable_cache_key {
            self.remember_statement_well_defined_object_proof(reusable_cache_key, result.clone());
        }
        Ok(result)
    }

    pub fn verify_child_obj_well_defined_result(
        &mut self,
        obj: &Obj,
        verify_state: &ProofSearchState,
        role: WellDefinedObjChildRole,
    ) -> Result<SuccessVerifyChildObjWellDefinedResult, RuntimeError> {
        let result = self.verify_obj_well_defined_result(obj, verify_state)?;
        Ok(SuccessVerifyChildObjWellDefinedResult::new(
            role,
            obj.clone(),
            result,
        ))
    }

    /// Mathematical contract support: reuse a successful
    /// check of the same rendered object; absence from the cache proves
    /// nothing and falls through to the constructor-specific obligations.
    /// Mathematical contract: an object is well-defined exactly when all of
    /// its subobjects are meaningful and its constructor-specific domain
    /// conditions hold (for example, a divisor is nonzero and a function
    /// application satisfies its declared parameter domain).
    pub fn verify_obj_well_defined_and_store_cache(
        &mut self,
        obj: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_result(obj, verify_state)
            .map(|_| ())
    }

    pub fn verify_child_obj_well_defined_and_store_cache(
        &mut self,
        obj: &Obj,
        verify_state: &ProofSearchState,
        role: WellDefinedObjChildRole,
    ) -> Result<Option<WellDefinedObjId>, RuntimeError> {
        self.verify_child_obj_well_defined_result(obj, verify_state, role)
            .map(|_| None)
    }

    /// Verify an object visited only while discharging another object's
    /// contract. When compiler evidence is active this becomes an ordered
    /// `VerificationDependency`, never a target-constructor value slot.
    pub fn verify_obj_well_defined_as_verification_dependency(
        &mut self,
        obj: &Obj,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_result(obj, verify_state)
            .map(|_| ())
    }
}

pub(super) fn success_obj_target_requirement(
    source_object: Obj,
    role: WellDefinednessRequirementRole,
    result: StmtResult,
) -> Result<SuccessVerifyObjTargetRequirementResult, RuntimeError> {
    let success = result.into_factual_success().ok_or_else(|| {
        RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "well-definedness requirement {role:?} for `{source_object}` has no successful factual result"
            )),
        ))
    })?;
    Ok(SuccessVerifyObjTargetRequirementResult::new(
        source_object,
        role,
        success.fact(),
        success.verification,
    ))
}

pub fn success_obj_fact_check(
    result: StmtResult,
) -> Result<SuccessVerifyFactForObjWellDefinedResult, RuntimeError> {
    let success = result.into_factual_success().ok_or_else(|| {
        RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(
                "well-definedness fact check has no successful factual result".to_string(),
            ),
        ))
    })?;
    Ok(SuccessVerifyFactForObjWellDefinedResult::new(
        success.fact(),
        success.verification,
    ))
}

#[cfg(test)]
#[path = "../../../tests/unit/verify/well_definedness/object.rs"]
mod tests;

/// Constructor-owned result carriers are part of the checked object contract,
/// not guesses from surrounding Lean syntax. Example: Litex remainder is an
/// integer operation even when both operands are closed numerals.
fn intrinsic_well_definedness_result_set(
    obj: &Obj,
    steps: &SuccessVerifyObjWellDefinedStepsResult,
) -> Option<Obj> {
    match obj {
        Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) => Some(StandardSet::C.into()),
        Obj::Mod(_) | Obj::Quot(_) => Some(StandardSet::Z.into()),
        Obj::FnObj(_) => steps.stores.iter().rev().find_map(|store| {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &store.fact else {
                return None;
            };
            (obj_equality_key(&membership.element) == obj_equality_key(obj))
                .then(|| membership.set.clone())
        }),
        _ => None,
    }
}

impl Runtime {
    /// Mathematical contract: an object-valued parameter carrier must itself
    /// be a well-defined object; the primitive `set`, `nonempty set`, and
    /// `finite set` parameter kinds are meaningful without another carrier.
    pub fn verify_param_type_well_defined(
        &mut self,
        param_type: &ParamType,
        verify_state: &ProofSearchState,
    ) -> Result<(), RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(obj) => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
        }
    }
}
