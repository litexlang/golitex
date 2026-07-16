use crate::prelude::*;

mod advanced;
mod core;
mod iterated;
mod matrix;
mod scalar;
mod sets;
mod structs;

impl Runtime {
    fn verify_obj_well_defined_from_cache_if_known(&self, obj: &Obj) -> Option<()> {
        let key = obj.to_string();
        if self.cache_well_defined_obj_contains(&key) {
            Some(())
        } else {
            None
        }
    }

    pub fn verify_obj_well_defined_and_store_cache(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let verify_state = verify_state.without_known_forall_for_equality();
        let verify_state = &verify_state;
        if self
            .verify_obj_well_defined_from_cache_if_known(obj)
            .is_some()
        {
            return Ok(());
        }

        match obj {
            Obj::Atom(AtomObj::Identifier(identifier)) => {
                self.verify_identifier_well_defined(identifier)
            }
            Obj::Atom(AtomObj::IdentifierWithMod(x)) => {
                self.verify_identifier_with_mod_well_defined(x)
            }
            Obj::FnObj(fn_obj) => self.verify_fn_obj_well_defined(fn_obj, verify_state),
            Obj::Number(_) => Ok(()),
            Obj::Add(add) => self.verify_add_well_defined(add, verify_state),
            Obj::Sub(sub) => self.verify_sub_well_defined(sub, verify_state),
            Obj::Mul(mul) => self.verify_mul_well_defined(mul, verify_state),
            Obj::Div(div) => self.verify_div_well_defined(div, verify_state),
            Obj::Mod(m) => self.verify_mod_well_defined(m, verify_state),
            Obj::IntegerQuotient(quotient) => {
                self.verify_integer_quotient_well_defined(quotient, verify_state)
            }
            Obj::Pow(pow) => self.verify_pow_well_defined(pow, verify_state),
            Obj::Abs(abs) => self.verify_abs_well_defined(abs, verify_state),
            Obj::Sqrt(sqrt) => self.verify_sqrt_well_defined(sqrt, verify_state),
            Obj::Log(log) => self.verify_log_well_defined(log, verify_state),
            Obj::Max(max) => self.verify_max_well_defined(max, verify_state),
            Obj::Min(min) => self.verify_min_well_defined(min, verify_state),
            Obj::Union(x) => self.verify_union_well_defined(x, verify_state),
            Obj::Intersect(x) => self.verify_intersect_well_defined(x, verify_state),
            Obj::SetMinus(x) => self.verify_set_minus_well_defined(x, verify_state),
            Obj::SetDiff(x) => self.verify_set_diff_well_defined(x, verify_state),
            Obj::Cup(x) => self.verify_cup_well_defined(x, verify_state),
            Obj::Cap(x) => self.verify_cap_well_defined(x, verify_state),
            Obj::ListSet(x) => self.verify_list_set_well_defined(x, verify_state),
            Obj::SetBuilder(x) => {
                self.run_in_local_env(|rt| rt.verify_set_builder_well_defined(x, verify_state))
            }
            Obj::FnSet(x) => {
                self.run_in_local_env(|rt| rt.verify_fn_set_well_defined(x, verify_state))
            }
            Obj::AnonymousFn(x) => self.verify_anonymous_fn_well_defined(x, verify_state),
            Obj::StandardSet(StandardSet::NPos) => self.verify_n_pos_obj_well_defined(),
            Obj::StandardSet(StandardSet::N) => self.verify_n_obj_well_defined(),
            Obj::StandardSet(StandardSet::Q) => self.verify_q_obj_well_defined(),
            Obj::StandardSet(StandardSet::Z) => self.verify_z_obj_well_defined(),
            Obj::StandardSet(StandardSet::R) => self.verify_r_obj_well_defined(),
            Obj::Cart(x) => self.verify_cart_well_defined(x, verify_state),
            Obj::CartDim(x) => self.verify_cart_dim_well_defined(x, verify_state),
            Obj::Proj(x) => self.verify_proj_well_defined(x, verify_state),
            Obj::TupleDim(x) => self.verify_dim_well_defined(x, verify_state),
            Obj::Tuple(x) => self.verify_tuple_well_defined(x, verify_state),
            Obj::FiniteSetSize(x) => self.verify_finite_set_size_well_defined(x, verify_state),
            Obj::FnRange(x) => self.verify_fn_range_well_defined(x, verify_state),
            Obj::Replacement(x) => self.verify_replacement_well_defined(x, verify_state),
            Obj::Sum(x) => self.verify_sum_obj_well_defined(x, verify_state),
            Obj::SumOfFiniteSet(x) => self.verify_finite_set_sum_obj_well_defined(x, verify_state),
            Obj::Product(x) => self.verify_product_obj_well_defined(x, verify_state),
            Obj::ProductOfFiniteSet(x) => {
                self.verify_finite_set_product_obj_well_defined(x, verify_state)
            }
            Obj::Range(x) => self.verify_range_well_defined(x, verify_state),
            Obj::ClosedRange(x) => self.verify_closed_range_well_defined(x, verify_state),
            Obj::IntervalObj(x) => self.verify_interval_obj_well_defined(x, verify_state),
            Obj::OneSideInfinityIntervalObj(x) => {
                self.verify_one_side_infinity_interval_obj_well_defined(x, verify_state)
            }
            Obj::FiniteSeqSet(x) => self.verify_finite_seq_set_well_defined(x, verify_state),
            Obj::SeqSet(x) => self.verify_seq_set_well_defined(x, verify_state),
            Obj::FiniteSeqListObj(x) => {
                self.verify_finite_seq_list_obj_well_defined(x, verify_state)
            }
            Obj::MatrixSet(x) => self.verify_matrix_set_well_defined(x, verify_state),
            Obj::MatrixListObj(x) => self.verify_matrix_list_obj_well_defined(x, verify_state),
            Obj::MatrixAdd(x) => self.verify_matrix_add_well_defined(x, verify_state),
            Obj::MatrixSub(x) => self.verify_matrix_sub_well_defined(x, verify_state),
            Obj::MatrixMul(x) => self.verify_matrix_mul_well_defined(x, verify_state),
            Obj::MatrixScalarMul(x) => self.verify_matrix_scalar_mul_well_defined(x, verify_state),
            Obj::MatrixPow(x) => self.verify_matrix_pow_well_defined(x, verify_state),
            Obj::PowerSet(x) => self.verify_power_set_well_defined(x, verify_state),
            Obj::GeneralCart(x) => self.verify_general_cart_well_defined(x, verify_state),
            Obj::ObjAtIndex(x) => self.verify_obj_at_index_well_defined(x, verify_state),
            Obj::StandardSet(StandardSet::QPos) => self.verify_q_pos_well_defined(),
            Obj::StandardSet(StandardSet::RPos) => self.verify_r_pos_well_defined(),
            Obj::StandardSet(StandardSet::QNeg) => self.verify_q_neg_well_defined(),
            Obj::StandardSet(StandardSet::ZNeg) => self.verify_z_neg_well_defined(),
            Obj::StandardSet(StandardSet::RNeg) => self.verify_r_neg_well_defined(),
            Obj::StandardSet(StandardSet::QNz) => self.verify_q_nz_well_defined(),
            Obj::StandardSet(StandardSet::ZNz) => self.verify_z_nz_well_defined(),
            Obj::StandardSet(StandardSet::RNz) => self.verify_r_nz_well_defined(),
            Obj::StructObj(struct_obj) => {
                self.verify_struct_obj_well_defined(struct_obj, verify_state)
            }
            Obj::ObjAsStructInstanceWithFieldAccess(field_access) => self
                .verify_obj_as_struct_instance_with_field_access_well_defined(
                    field_access,
                    verify_state,
                ),
            Obj::InstantiatedTemplateObj(template_obj) => {
                self.verify_instantiated_template_obj_well_defined(template_obj, verify_state)
            }
            Obj::Atom(AtomObj::Forall(_)) => Ok(()),
            Obj::Atom(AtomObj::Def(_)) => Ok(()),
            Obj::Atom(AtomObj::Exist(_)) => Ok(()),
            Obj::Atom(AtomObj::SetBuilder(_)) => Ok(()),
            Obj::Atom(AtomObj::FnSet(_)) => Ok(()),
            Obj::Atom(AtomObj::Induc(_)) => Ok(()),
            Obj::Atom(AtomObj::DefAlgo(_)) => Ok(()),
            Obj::Atom(AtomObj::DefStructField(_)) => Ok(()),
            Obj::Atom(AtomObj::TupleIndex(_)) => Ok(()),
            Obj::Atom(AtomObj::CartIndex(_)) => Ok(()),
        }?;

        self.store_well_defined_obj_cache(obj);

        Ok(())
    }
}

impl Runtime {
    pub fn verify_param_type_well_defined(
        &mut self,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(obj) => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
        }
    }
}
