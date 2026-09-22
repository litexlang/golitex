//! Object well-definedness dispatch and recursive result assembly.

use crate::prelude::*;
use std::rc::Rc;

struct ActiveWellDefinedObjectGuard<'a> {
    verify_state: &'a VerifyState,
    key: ObjString,
}

impl<'a> ActiveWellDefinedObjectGuard<'a> {
    fn begin(
        verify_state: &'a VerifyState,
        object: &Obj,
        key: ObjString,
    ) -> Result<Self, RuntimeError> {
        if !verify_state.begin_well_defined_object(&key) {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "cyclic object well-definedness dependency while checking `{object}`"
                )),
            )));
        }
        Ok(Self { verify_state, key })
    }
}

impl Drop for ActiveWellDefinedObjectGuard<'_> {
    fn drop(&mut self) {
        self.verify_state.end_well_defined_object(&self.key);
    }
}

impl Runtime {
    /// Compositional WD entry point. Every object family returns its exact
    /// recursive children, fact checks, binder body, or Template instantiation.
    pub fn verify_obj_well_defined_result(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<Rc<SuccessVerifyObjWellDefinedResult>, RuntimeError> {
        let (object_key, function_contracts) = self.well_defined_memo_entry_for_obj(obj);
        if let Some(source) = verify_state.well_defined_object_proof(&object_key) {
            return Ok(Rc::new(SuccessVerifyObjWellDefinedResult::Reuse(Box::new(
                SuccessReuseObjWellDefinedResult::new(obj.clone(), source),
            ))));
        }
        let _active_guard =
            ActiveWellDefinedObjectGuard::begin(verify_state, obj, object_key.clone())?;

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
            Obj::Atom(AtomObj::Bound(_))
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
            Obj::FamilyUnion(value) => self
                .verify_family_union_well_defined_result(value, verify_state)
                .map(Some),
            Obj::FamilyIntersect(value) => self
                .verify_family_intersect_well_defined_result(value, verify_state)
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
            Obj::IndexCart(value) => self
                .verify_index_cart_well_defined_result(value, verify_state)
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

        let steps = steps?.expect("every Obj variant returns compositional WD steps");
        let intrinsic_result_set = intrinsic_well_definedness_result_set(obj, &steps);
        let direct = Rc::new(SuccessVerifyDirectObjWellDefinedResult::new(
            obj.clone(),
            object_key.clone(),
            function_contracts,
            steps,
            intrinsic_result_set,
        ));
        verify_state.remember_well_defined_object_proof(object_key, direct.clone());
        Ok(Rc::new(SuccessVerifyObjWellDefinedResult::Direct(direct)))
    }

    pub fn verify_child_obj_well_defined_result(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
        role: WellDefinedObjChildRole,
    ) -> Result<SuccessVerifyChildObjWellDefinedResult, RuntimeError> {
        let result = self.verify_obj_well_defined_result(obj, verify_state)?;
        Ok(SuccessVerifyChildObjWellDefinedResult::new(
            role,
            obj.clone(),
            result,
        ))
    }
}

pub(super) fn success_obj_target_requirement(
    source_object: Obj,
    role: WellDefinednessRequirementRole,
    result: VerifyFactResult,
) -> Result<SuccessVerifyObjTargetRequirementResult, RuntimeError> {
    let success = result.into_verified().ok_or_else(|| {
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
        success.verification.clone(),
    ))
}

pub(super) fn success_obj_fact_check(
    result: VerifyFactResult,
) -> Result<SuccessVerifyFactForObjWellDefinedResult, RuntimeError> {
    let success = result.into_verified().ok_or_else(|| {
        RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(
                "well-definedness fact check has no successful factual result".to_string(),
            ),
        ))
    })?;
    Ok(SuccessVerifyFactForObjWellDefinedResult::new(
        success.fact(),
        success.verification.clone(),
    ))
}

/// Records a truth proof whose WD is supplied by the surrounding object
/// constructor derivation itself. This is not a standalone fact-verification
/// result and therefore deliberately does not masquerade as `VerifyFactResult`.
pub(super) fn success_obj_fact_check_after_structural_wd(
    result: ProveFactResult,
) -> Result<SuccessVerifyFactForObjWellDefinedResult, RuntimeError> {
    let success = result.into_factual_success().ok_or_else(|| {
        RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(
                "object-WD structural fact check has no successful truth proof".to_string(),
            ),
        ))
    })?;
    Ok(SuccessVerifyFactForObjWellDefinedResult::new(
        success.fact(),
        success.verification,
    ))
}

#[cfg(test)]
#[path = "../../../../tests/unit/verification/well_definedness/object.rs"]
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
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(obj) => self
                .verify_obj_well_defined_result(obj, verify_state)
                .map(|_| ()),
        }
    }
}
