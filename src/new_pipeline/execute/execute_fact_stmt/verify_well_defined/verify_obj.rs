//! Object well-definedness: ByCache | ByDef, with one shared by-def proof shape.
//!
//! Dispatch matches every Obj variant; each arm fills ObjWellDefinedProofByDef
//! from recursive child WD. Domain / requirement facts stay empty until wired.

use crate::new_pipeline::ast::obj::{
    Abs, Add, AnonymousFn, Arcsin, BigIntersect, BigUnion, Cart, CartDim, Ceil, ClosedRange,
    ComplexAbs, Cos, Cot, Div, Exp, Factorial, FiniteSeqListObj, FiniteSeqSet, FiniteSetMax,
    FiniteSetMin, FiniteSetReduce, FiniteSetSize, Floor, FnObj, FnObjHead, FnRange, FnSet, Gcd,
    GeneralCart, ImaginaryPart, IndexIntersect, IndexUnion, InstantiatedTemplateObj, Intersect,
    IntervalObj, IntervalObjStruct, Lcm, ListSet, Ln, Log, MatrixAdd, MatrixListObj, MatrixMul,
    MatrixPow, MatrixScalarMul, MatrixSet, MatrixSub, Max, Min, Mod, Mul, Obj,
    ObjAsStructInstanceWithFieldAccess, ObjAtIndex, OneSideInfinityIntervalObj,
    Pow, PowerSet, Product, ProductOfFiniteSet, Proj, Quot,
    Range, RealPart, Reduce, Replacement, SeqSet, SetBuilder, SetMinus, Sign, Sin, Sqrt,
    StructObj, Sub, Sum, SumOfFiniteSet, Tan, Tuple, TupleDim, Union,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_well_defined::FactWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;
use crate::new_pipeline::execution_environment::helper::ast_obj_key;
use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Top-level object WD result: only cache hit or prove-by-definition.
pub enum VerifyObjResult {
    ByCache { wd_id: WellDefinednessId },
    ByDef(ObjWellDefinedProofByDef),
}

// One by-def shape for every Obj: recursive child WD + optional domain facts.
pub struct ObjWellDefinedProofByDef {
    pub child_obj_well_defined: Vec<VerifyObjResult>,
    pub requirement_fact_well_defined: Vec<FactWellDefinedProof>,
}

impl ObjWellDefinedProofByDef {
    pub fn leaf() -> Self {
        Self {
            child_obj_well_defined: Vec::new(),
            requirement_fact_well_defined: Vec::new(),
        }
    }

    pub fn from_children(child_obj_well_defined: Vec<VerifyObjResult>) -> Self {
        Self {
            child_obj_well_defined,
            requirement_fact_well_defined: Vec::new(),
        }
    }
}

impl Runtime {
    // 1. cache lookup → ByCache
    // 2. else match Obj → fill ObjWellDefinedProofByDef
    // 3. optionally store new WD id into ExecEnv
    pub fn verify_obj_well_definedness(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<VerifyObjResult> {
        let key = ast_obj_key(obj);
        if let Some(wd_id) = self.lookup_obj_wd_in_env_stack(&key) {
            return Ok(VerifyObjResult::ByCache { wd_id });
        }

        let by_def = self.verify_obj_well_definedness_by_def(obj, verify_state.clone())?;
        let result = VerifyObjResult::ByDef(by_def);

        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut().record_native_wd(key, wd_id);
        }

        Ok(result)
    }

    fn lookup_obj_wd_in_env_stack(&self, key: &str) -> Option<WellDefinednessId> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(wd_id) = env.lookup_native_wd(key) {
                return Some(wd_id);
            }
        }
        None
    }

    // Big match: every Obj variant has its own by-def branch function.
    fn verify_obj_well_definedness_by_def(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        match obj {
            Obj::Atom(_) => self.verify_atom_obj_well_definedness_by_def(verify_state),
            Obj::FnObj(value) => self.verify_fn_obj_well_definedness_by_def(value, verify_state),
            Obj::Number(_) => self.verify_number_obj_well_definedness_by_def(verify_state),
            Obj::ImaginaryUnit(_) => self.verify_imaginary_unit_obj_well_definedness_by_def(verify_state),
            Obj::EulerNumber(_) => self.verify_euler_number_obj_well_definedness_by_def(verify_state),
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
            Obj::Factorial(value) => self.verify_factorial_obj_well_definedness_by_def(value, verify_state),
            Obj::Pow(value) => self.verify_pow_obj_well_definedness_by_def(value, verify_state),
            Obj::Abs(value) => self.verify_abs_obj_well_definedness_by_def(value, verify_state),
            Obj::Sin(value) => self.verify_sin_obj_well_definedness_by_def(value, verify_state),
            Obj::Arcsin(value) => self.verify_arcsin_obj_well_definedness_by_def(value, verify_state),
            Obj::Cos(value) => self.verify_cos_obj_well_definedness_by_def(value, verify_state),
            Obj::Tan(value) => self.verify_tan_obj_well_definedness_by_def(value, verify_state),
            Obj::Cot(value) => self.verify_cot_obj_well_definedness_by_def(value, verify_state),
            Obj::RealPart(value) => self.verify_real_part_obj_well_definedness_by_def(value, verify_state),
            Obj::ImaginaryPart(value) => self.verify_imaginary_part_obj_well_definedness_by_def(value, verify_state),
            Obj::ComplexAbs(value) => self.verify_complex_abs_obj_well_definedness_by_def(value, verify_state),
            Obj::Sqrt(value) => self.verify_sqrt_obj_well_definedness_by_def(value, verify_state),
            Obj::Log(value) => self.verify_log_obj_well_definedness_by_def(value, verify_state),
            Obj::Union(value) => self.verify_union_obj_well_definedness_by_def(value, verify_state),
            Obj::Intersect(value) => self.verify_intersect_obj_well_definedness_by_def(value, verify_state),
            Obj::SetMinus(value) => self.verify_set_minus_obj_well_definedness_by_def(value, verify_state),
            Obj::BigUnion(value) => self.verify_big_union_obj_well_definedness_by_def(value, verify_state),
            Obj::BigIntersect(value) => self.verify_big_intersect_obj_well_definedness_by_def(value, verify_state),
            Obj::IndexUnion(value) => self.verify_index_union_obj_well_definedness_by_def(value, verify_state),
            Obj::IndexIntersect(value) => self.verify_index_intersect_obj_well_definedness_by_def(value, verify_state),
            Obj::PowerSet(value) => self.verify_power_set_obj_well_definedness_by_def(value, verify_state),
            Obj::GeneralCart(value) => self.verify_general_cart_obj_well_definedness_by_def(value, verify_state),
            Obj::ListSet(value) => self.verify_list_set_obj_well_definedness_by_def(value, verify_state),
            Obj::SetBuilder(value) => self.verify_set_builder_obj_well_definedness_by_def(value, verify_state),
            Obj::FnSet(value) => self.verify_fn_set_obj_well_definedness_by_def(value, verify_state),
            Obj::AnonymousFn(value) => self.verify_anonymous_fn_obj_well_definedness_by_def(value, verify_state),
            Obj::Cart(value) => self.verify_cart_obj_well_definedness_by_def(value, verify_state),
            Obj::CartDim(value) => self.verify_cart_dim_obj_well_definedness_by_def(value, verify_state),
            Obj::Proj(value) => self.verify_proj_obj_well_definedness_by_def(value, verify_state),
            Obj::TupleDim(value) => self.verify_tuple_dim_obj_well_definedness_by_def(value, verify_state),
            Obj::Tuple(value) => self.verify_tuple_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSetSize(value) => self.verify_finite_set_size_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSetMax(value) => self.verify_finite_set_max_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSetMin(value) => self.verify_finite_set_min_obj_well_definedness_by_def(value, verify_state),
            Obj::FnRange(value) => self.verify_fn_range_obj_well_definedness_by_def(value, verify_state),
            Obj::Replacement(value) => self.verify_replacement_obj_well_definedness_by_def(value, verify_state),
            Obj::Sum(value) => self.verify_sum_obj_well_definedness_by_def(value, verify_state),
            Obj::SumOfFiniteSet(value) => self.verify_sum_of_finite_set_obj_well_definedness_by_def(value, verify_state),
            Obj::Product(value) => self.verify_product_obj_well_definedness_by_def(value, verify_state),
            Obj::ProductOfFiniteSet(value) => self.verify_product_of_finite_set_obj_well_definedness_by_def(value, verify_state),
            Obj::Reduce(value) => self.verify_reduce_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSetReduce(value) => self.verify_finite_set_reduce_obj_well_definedness_by_def(value, verify_state),
            Obj::Range(value) => self.verify_range_obj_well_definedness_by_def(value, verify_state),
            Obj::ClosedRange(value) => self.verify_closed_range_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSeqSet(value) => self.verify_finite_seq_set_obj_well_definedness_by_def(value, verify_state),
            Obj::SeqSet(value) => self.verify_seq_set_obj_well_definedness_by_def(value, verify_state),
            Obj::FiniteSeqListObj(value) => self.verify_finite_seq_list_obj_well_definedness_by_def(value, verify_state),
            Obj::ObjAtIndex(value) => self.verify_obj_at_index_obj_well_definedness_by_def(value, verify_state),
            Obj::StandardSet(_) => self.verify_standard_set_obj_well_definedness_by_def(verify_state),
            Obj::MatrixSet(value) => self.verify_matrix_set_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixListObj(value) => self.verify_matrix_list_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixAdd(value) => self.verify_matrix_add_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixSub(value) => self.verify_matrix_sub_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixMul(value) => self.verify_matrix_mul_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixScalarMul(value) => self.verify_matrix_scalar_mul_obj_well_definedness_by_def(value, verify_state),
            Obj::MatrixPow(value) => self.verify_matrix_pow_obj_well_definedness_by_def(value, verify_state),
            Obj::StructObj(value) => self.verify_struct_obj_well_definedness_by_def(value, verify_state),
            Obj::ObjAsStructInstanceWithFieldAccess(value) => self.verify_obj_as_struct_instance_with_field_access_obj_well_definedness_by_def(value, verify_state),
            Obj::InstantiatedTemplateObj(value) => self.verify_instantiated_template_obj_well_definedness_by_def(value, verify_state),
            Obj::OneSideInfinityIntervalObj(value) => self.verify_one_side_infinity_interval_obj_well_definedness_by_def(value, verify_state),
            Obj::IntervalObj(value) => self.verify_interval_obj_well_definedness_by_def(value, verify_state),

        }
    }

    fn verify_objs_as_children(
        &mut self,
        objs: &[&Obj],
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut child_obj_well_defined = Vec::new();
        for obj in objs {
            child_obj_well_defined
                .push(self.verify_obj_well_definedness(obj, verify_state.clone())?);
        }
        Ok(ObjWellDefinedProofByDef::from_children(child_obj_well_defined))
    }

    fn verify_boxed_objs_as_children(
        &mut self,
        objs: &[Box<Obj>],
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let refs: Vec<&Obj> = objs.iter().map(|o| o.as_ref()).collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    fn verify_unary_obj_well_definedness_by_def(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(&[arg], verify_state)
    }

    fn verify_binary_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(&[left, right], verify_state)
    }

    fn verify_atom_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_fn_obj_well_definedness_by_def(
        &mut self,
        value: &FnObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        self.collect_fn_obj_head_child_objs(&value.head, &mut children);
        for layer in &value.body {
            for arg in layer {
                children.push(arg.as_ref());
            }
        }
        self.verify_objs_as_children(&children, verify_state)
    }

    fn collect_fn_obj_head_child_objs<'a>(
        &self,
        head: &'a FnObjHead,
        children: &mut Vec<&'a Obj>,
    ) {
        let _ = self;
        match head {
            FnObjHead::Identifier(_)
            | FnObjHead::IdentifierWithMod(_)
            | FnObjHead::Bound(_) => {}
            FnObjHead::AnonymousFnLiteral(anon) => {
                for group in &anon.body.set_bound_parameters.groups {
                    children.push(group.param_type.as_ref());
                }
                children.push(anon.body.ret_set.as_ref());
                children.push(anon.equal_to.as_ref());
            }
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in &list.objs {
                    children.push(obj.as_ref());
                }
            }
            FnObjHead::ObjAtIndex(at) => {
                children.push(at.obj.as_ref());
                children.push(at.index.as_ref());
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                children.push(access.obj.as_ref());
                if let Some(carrier) = &access.resolved_struct_carrier {
                    for param in &carrier.params {
                        children.push(param);
                    }
                }
            }
            FnObjHead::InstantiatedTemplateObj(inst) => {
                for arg in &inst.args {
                    children.push(arg);
                }
            }
            FnObjHead::MatrixOperator(obj) => {
                children.push(obj.as_ref());
            }
        }
    }

    fn verify_number_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_imaginary_unit_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_euler_number_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_pi_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_standard_set_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    fn verify_add_obj_well_definedness_by_def(
        &mut self,
        value: &Add,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_sub_obj_well_definedness_by_def(
        &mut self,
        value: &Sub,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_mul_obj_well_definedness_by_def(
        &mut self,
        value: &Mul,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_div_obj_well_definedness_by_def(
        &mut self,
        value: &Div,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_mod_obj_well_definedness_by_def(
        &mut self,
        value: &Mod,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_quot_obj_well_definedness_by_def(
        &mut self,
        value: &Quot,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_gcd_obj_well_definedness_by_def(
        &mut self,
        value: &Gcd,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_lcm_obj_well_definedness_by_def(
        &mut self,
        value: &Lcm,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_floor_obj_well_definedness_by_def(
        &mut self,
        value: &Floor,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_ceil_obj_well_definedness_by_def(
        &mut self,
        value: &Ceil,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_min_obj_well_definedness_by_def(
        &mut self,
        value: &Min,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_max_obj_well_definedness_by_def(
        &mut self,
        value: &Max,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_exp_obj_well_definedness_by_def(
        &mut self,
        value: &Exp,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_ln_obj_well_definedness_by_def(
        &mut self,
        value: &Ln,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_sign_obj_well_definedness_by_def(
        &mut self,
        value: &Sign,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_factorial_obj_well_definedness_by_def(
        &mut self,
        value: &Factorial,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_pow_obj_well_definedness_by_def(
        &mut self,
        value: &Pow,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.base.as_ref(),
            value.exponent.as_ref(),
            verify_state,
        )
    }

    fn verify_abs_obj_well_definedness_by_def(
        &mut self,
        value: &Abs,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_sin_obj_well_definedness_by_def(
        &mut self,
        value: &Sin,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_arcsin_obj_well_definedness_by_def(
        &mut self,
        value: &Arcsin,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_cos_obj_well_definedness_by_def(
        &mut self,
        value: &Cos,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_tan_obj_well_definedness_by_def(
        &mut self,
        value: &Tan,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_cot_obj_well_definedness_by_def(
        &mut self,
        value: &Cot,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_real_part_obj_well_definedness_by_def(
        &mut self,
        value: &RealPart,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_imaginary_part_obj_well_definedness_by_def(
        &mut self,
        value: &ImaginaryPart,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_complex_abs_obj_well_definedness_by_def(
        &mut self,
        value: &ComplexAbs,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_sqrt_obj_well_definedness_by_def(
        &mut self,
        value: &Sqrt,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_log_obj_well_definedness_by_def(
        &mut self,
        value: &Log,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.base.as_ref(),
            value.arg.as_ref(),
            verify_state,
        )
    }

    fn verify_union_obj_well_definedness_by_def(
        &mut self,
        value: &Union,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &Intersect,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_set_minus_obj_well_definedness_by_def(
        &mut self,
        value: &SetMinus,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_big_union_obj_well_definedness_by_def(
        &mut self,
        value: &BigUnion,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }

    fn verify_big_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &BigIntersect,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }

    fn verify_index_union_obj_well_definedness_by_def(
        &mut self,
        value: &IndexUnion,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.index_set.as_ref(),
            value.ambient_set.as_ref(),
            value.family_fn.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_index_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &IndexIntersect,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.index_set.as_ref(),
            value.ambient_set.as_ref(),
            value.family_fn.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_power_set_obj_well_definedness_by_def(
        &mut self,
        value: &PowerSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_general_cart_obj_well_definedness_by_def(
        &mut self,
        value: &GeneralCart,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.index_set.as_ref(),
            value.family_set.as_ref(),
            value.family_fn.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_list_set_obj_well_definedness_by_def(
        &mut self,
        value: &ListSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.list, verify_state)
    }

    fn verify_set_builder_obj_well_definedness_by_def(
        &mut self,
        value: &SetBuilder,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        // Dom facts are not wired into requirement_fact_well_defined yet.
        let _ = &value.facts;
        self.verify_unary_obj_well_definedness_by_def(value.param_set.as_ref(), verify_state)
    }

    fn verify_fn_set_obj_well_definedness_by_def(
        &mut self,
        value: &FnSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for group in &value.body.set_bound_parameters.groups {
            children.push(group.param_type.as_ref());
        }
        children.push(value.body.ret_set.as_ref());
        let _ = &value.body.dom_facts;
        self.verify_objs_as_children(&children, verify_state)
    }

    fn verify_anonymous_fn_obj_well_definedness_by_def(
        &mut self,
        value: &AnonymousFn,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for group in &value.body.set_bound_parameters.groups {
            children.push(group.param_type.as_ref());
        }
        children.push(value.body.ret_set.as_ref());
        children.push(value.equal_to.as_ref());
        let _ = &value.body.dom_facts;
        self.verify_objs_as_children(&children, verify_state)
    }

    fn verify_cart_obj_well_definedness_by_def(
        &mut self,
        value: &Cart,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }

    fn verify_cart_dim_obj_well_definedness_by_def(
        &mut self,
        value: &CartDim,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_proj_obj_well_definedness_by_def(
        &mut self,
        value: &Proj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.dim.as_ref(),
            verify_state,
        )
    }

    fn verify_tuple_dim_obj_well_definedness_by_def(
        &mut self,
        value: &TupleDim,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }

    fn verify_tuple_obj_well_definedness_by_def(
        &mut self,
        value: &Tuple,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }

    fn verify_finite_set_size_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetSize,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_finite_set_max_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMax,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_finite_set_min_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMin,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_fn_range_obj_well_definedness_by_def(
        &mut self,
        value: &FnRange,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.function.as_ref(), verify_state)
    }

    fn verify_replacement_obj_well_definedness_by_def(
        &mut self,
        value: &Replacement,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.source_set.as_ref(), verify_state)
    }

    fn verify_sum_obj_well_definedness_by_def(
        &mut self,
        value: &Sum,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.start.as_ref(),
            value.end.as_ref(),
            value.func.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_sum_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &SumOfFiniteSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            verify_state,
        )
    }

    fn verify_product_obj_well_definedness_by_def(
        &mut self,
        value: &Product,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.start.as_ref(),
            value.end.as_ref(),
            value.func.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_product_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &ProductOfFiniteSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            verify_state,
        )
    }

    fn verify_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &Reduce,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.start.as_ref(),
            value.end.as_ref(),
            value.func.as_ref(),
            value.op.as_ref(),
            value.seed.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_finite_set_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetReduce,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.set.as_ref(),
            value.func.as_ref(),
            value.op.as_ref(),
            value.seed.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_range_obj_well_definedness_by_def(
        &mut self,
        value: &Range,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state,
        )
    }

    fn verify_closed_range_obj_well_definedness_by_def(
        &mut self,
        value: &ClosedRange,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state,
        )
    }

    fn verify_finite_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.n.as_ref(),
            verify_state,
        )
    }

    fn verify_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &SeqSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }

    fn verify_finite_seq_list_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqListObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.objs, verify_state)
    }

    fn verify_obj_at_index_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAtIndex,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.obj.as_ref(),
            value.index.as_ref(),
            verify_state,
        )
    }

    fn verify_matrix_set_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixSet,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
            value.set.as_ref(),
            value.row_len.as_ref(),
            value.col_len.as_ref()
            ],
            verify_state,
        )
    }

    fn verify_matrix_list_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixListObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for row in &value.rows {
            for cell in row {
                children.push(cell.as_ref());
            }
        }
        self.verify_objs_as_children(&children, verify_state)
    }

    fn verify_matrix_add_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixAdd,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_matrix_sub_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixSub,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_matrix_mul_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixMul,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    fn verify_matrix_scalar_mul_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixScalarMul,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.scalar.as_ref(),
            value.matrix.as_ref(),
            verify_state,
        )
    }

    fn verify_matrix_pow_obj_well_definedness_by_def(
        &mut self,
        value: &MatrixPow,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.base.as_ref(),
            value.exponent.as_ref(),
            verify_state,
        )
    }

    fn verify_struct_obj_well_definedness_by_def(
        &mut self,
        value: &StructObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let refs: Vec<&Obj> = value.params.iter().collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    fn verify_obj_as_struct_instance_with_field_access_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAsStructInstanceWithFieldAccess,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        children.push(value.obj.as_ref());
        if let Some(carrier) = &value.resolved_struct_carrier {
            for param in &carrier.params {
                children.push(param);
            }
        }
        self.verify_objs_as_children(&children, verify_state)
    }

    fn verify_instantiated_template_obj_well_definedness_by_def(
        &mut self,
        value: &InstantiatedTemplateObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let refs: Vec<&Obj> = value.args.iter().collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    fn verify_one_side_infinity_interval_obj_well_definedness_by_def(
        &mut self,
        value: &OneSideInfinityIntervalObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let start = match value {
            OneSideInfinityIntervalObj::LeftOpen(v)
            | OneSideInfinityIntervalObj::LeftClosed(v)
            | OneSideInfinityIntervalObj::RightOpen(v)
            | OneSideInfinityIntervalObj::RightClosed(v) => v.start.as_ref(),
        };
        self.verify_unary_obj_well_definedness_by_def(start, verify_state)
    }

    fn verify_interval_obj_well_definedness_by_def(
        &mut self,
        value: &IntervalObj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let bounds: &IntervalObjStruct = match value {
            IntervalObj::LeftOpenRightOpen(v)
            | IntervalObj::LeftOpenRightClosed(v)
            | IntervalObj::LeftClosedRightOpen(v)
            | IntervalObj::LeftClosedRightClosed(v) => v,
        };
        self.verify_binary_obj_well_definedness_by_def(
            bounds.start.as_ref(),
            bounds.end.as_ref(),
            verify_state,
        )
    }
}
